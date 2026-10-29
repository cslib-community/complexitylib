/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Prepare

/-!
# The native Convolution-3SUM instance loop

The supplied solver is an actual finite structured program. Its six input registers hold the
side, weight bound, three matrix pointers and workspace pointer; its seventh register returns
an unsigned Boolean. Solver registers are disjoint from the host bank. The host writes each
instance using `Fill.program`, copies its arguments, executes the solver and accumulates the
verdict. The execution theorem requires the concrete solver's execution/correctness/frame proof;
it does not establish a fast solver by assuming one.

The construction directly adapts Anthropic's pinned
[`c3Round` and `c3Body`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Host.lean).

## Main definitions

* `Host.instanceArgs`: the concrete generated instance and layout.
* `Host.hit`: the mathematical verdict for one instance.
* `Host.round`: fill, invoke the solver and advance one instance.
* `Host.loop`: the complete instance loop.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ThreeSum

/-- The generated matrices follow the input and precede the solver's workspace. -/
def instanceArgs (N U s : ℕ) (μ : ℕ → ℤ) : Fill.Args :=
  ⟨N, sideLength N, s, 1, N + 1,
    N + 1 + sideLength N * sideLength N,
    N + 1 + 2 * (sideLength N * sideLength N), μ, 2 * U + 1⟩

/-- The exact-triangle answer for one instance of the explicit reduction. -/
def hit (N U s : ℕ) (μ : ℕ → ℤ) : Prop :=
  Cslib.Algorithms.ExactTriangle.HasZeroTriangle
    (weightAB (t := sideLength N) N μ (2 * U + 1))
    (weightBC N s μ (2 * U + 1)) (weightAC N s μ (2 * U + 1))

/-- Embed the fixed matrix-builder register bank. -/
def fillRegisters (i : Fin 28) : Fin 64 := ⟨i.val, by omega⟩

/-- Copy every matrix-builder argument; the builder bank occupies the first 28 registers. -/
def fillSetup : Code .standard 64 :=
  let fLen := fillRegisters Cell.len
  let fBase := fillRegisters Cell.base
  let fFiller := fillRegisters Cell.filler
  let fSide := fillRegisters Cell.side
  let fInst := fillRegisters Cell.inst
  let fAB := fillRegisters Cell.matAB
  let fBC := fillRegisters Cell.matBC
  let fAC := fillRegisters Cell.matAC
  ram[ fLen ← len; fBase ← base; fFiller ← encodedFiller;
    fSide ← side; fInst ← inst; fAB ← matAB; fBC ← matBC; fAC ← matAC ]

/-- Matrix construction, including its argument copies. -/
def fill : Code .standard 64 := .seq fillSetup (Fill.program.rename fillRegisters)

/-- Host registers precede the solver bank. -/
def hostRegisters {r : ℕ} (i : Fin 64) : Fin (64 + r) := ⟨i.val, by omega⟩

/-- The solver bank is disjoint from every host register. -/
def solverRegisters {r : ℕ} (i : Fin r) : Fin (64 + r) := ⟨64 + i.val, by omega⟩

/-- One of the seven fixed protocol registers in the solver bank. -/
def solverArg {r : ℕ} (i : Fin 7) : Fin (r + 7) := ⟨i.val, by omega⟩

/-- Protocol registers after placing the solver after the host. -/
def callRegisters {r : ℕ} (i : Fin 7) : Fin (64 + (r + 7)) :=
  solverRegisters (solverArg i)

/-- Prepare the solver's side, unsigned bound, AB/BC/AC pointers and free pointer. -/
def solverSetup {r : ℕ} : Code .standard (64 + (r + 7)) :=
  .seq (.op (.copy (callRegisters 0) (hostRegisters side)))
  (.seq (.op (.copy (callRegisters 1) (hostRegisters filler)))
  (.seq (.op (.copy (callRegisters 2) (hostRegisters matAB)))
  (.seq (.op (.copy (callRegisters 3) (hostRegisters matBC)))
  (.seq (.op (.copy (callRegisters 4) (hostRegisters matAC)))
    (.op (.copy (callRegisters 5) (hostRegisters free)))))))

/-- Accumulate the unsigned Boolean result and advance the instance counter. -/
def finish {r : ℕ} : Code .standard (64 + (r + 7)) :=
  .seq (.branch (.eq (callRegisters 6) (hostRegisters one))
    (.op (.copy (hostRegisters found) (hostRegisters one)))
    (.op (.copy (hostRegisters found) (hostRegisters found))))
    (.op (.bin .add (hostRegisters inst) (hostRegisters inst) (hostRegisters one)))

/-- One complete instance, invoking the supplied finite solver in its own register bank. -/
def round {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (64 + (r + 7)) :=
  .seq (fill.rename hostRegisters)
    (.seq solverSetup (.seq (solver.rename solverRegisters) finish))

/-- Every one of the `2t` instances is examined, without an uncharged early-exit operation. -/
def loop {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (64 + (r + 7)) :=
  .loop (.lt (hostRegisters inst) (hostRegisters stop)) (round solver)

private theorem fill_injective : fillRegisters.Injective := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 64 => k.val) h)

private theorem parameters_of_regs {N U : ℕ} {x y : Data 64}
    (hx : Parameters N U x)
    (h : ∀ i : Fin 64, 34 ≤ i.val → i ≠ inst → i ≠ found → y.regs i = x.regs i) :
    Parameters N U y := by
  exact ⟨(h len (by decide) (by decide) (by decide)).trans hx.len,
    (h upper (by decide) (by decide) (by decide)).trans hx.upper,
    (h base (by decide) (by decide) (by decide)).trans hx.base,
    (h matAB (by decide) (by decide) (by decide)).trans hx.ab,
    (h matBC (by decide) (by decide) (by decide)).trans hx.bc,
    (h matAC (by decide) (by decide) (by decide)).trans hx.ac,
    (h free (by decide) (by decide) (by decide)).trans hx.free,
    (h side (by decide) (by decide) (by decide)).trans hx.side,
    (h stop (by decide) (by decide) (by decide)).trans hx.stop,
    (h filler (by decide) (by decide) (by decide)).trans hx.filler,
    (h encodedFiller (by decide) (by decide) (by decide)).trans hx.encodedFiller,
    (h one (by decide) (by decide) (by decide)).trans hx.one⟩

/-- All eight argument copies and the complete matrix builder are charged. Memory before
the matrix blocks is preserved; the result contains the three actual serialized matrices. -/
theorem exec_fill {w N U s : ℕ} (μ : ℕ → ℤ) (x : Data 64)
    (hp : Parameters N U x) (hs : x.regs inst = s)
    (hmem : ∀ i < N, x.mem (1 + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w ((2 * (sideLength N * sideLength N) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w (2 * (U : ℤ) + 1))
    (hnF : GenericRAM.Signed.Fits w (-(2 * (U : ℤ) + 1)))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (hsize : Fits (w + 2) (N + 1 + 3 * (sideLength N * sideLength N))) :
    ∃ y, ExecWithin (w + 2) fill x y (131 * (sideLength N * sideLength N) + 13) ∧
      Parameters N U y ∧ y.regs inst = s ∧ y.regs found = x.regs found ∧
      y.mem = (instanceArgs N U s μ).filled x.mem (sideLength N * sideLength N) ∧
      (∀ a < N + 1, y.mem a = x.mem a) := by
  let b := x.set (fillRegisters Cell.len) N |>.set (fillRegisters Cell.base) 1
    |>.set (fillRegisters Cell.filler) (4 * U + 2)
    |>.set (fillRegisters Cell.side) (sideLength N) |>.set (fillRegisters Cell.inst) s
    |>.set (fillRegisters Cell.matAB) (N + 1)
    |>.set (fillRegisters Cell.matBC) (N + 1 + sideLength N * sideLength N)
    |>.set (fillRegisters Cell.matAC) (N + 1 + 2 * (sideLength N * sideLength N))
  have hb : ExecWithin (w + 2) fillSetup x b 8 := by
    ram_eval [fillSetup, b, hp.len, hp.base, hp.encodedFiller, hp.side, hs,
      hp.ab, hp.bc, hp.ac, fillRegisters, Cell.len, Cell.base, Cell.filler, Cell.side,
      Cell.inst, Cell.matAB, Cell.matBC, Cell.matAC, len, base, encodedFiller, side, inst,
      matAB, matBC, matAC, Fin.mk.injEq]
  have hbregs (i : Fin 64) (hi : 34 ≤ i.val) : b.regs i = x.regs i := by
    have hne (j : Fin 28) : i ≠ fillRegisters j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [fillRegisters] at hv
      have := j.isLt
      omega
    simp only [b, Data.set_regs, Function.update_of_ne (hne _)]
  have hbf : (b.comap fillRegisters).regs Cell.filler = encode (instanceArgs N U s μ).filler := by
    simp +decide [b, instanceArgs, fillRegisters, Cell.filler, Cell.side, Cell.inst,
      Cell.matAB, Cell.matBC, Cell.matAC, encode,
      show ¬(2 * (U : ℤ) + 1 < 0) from by omega]
    omega
  obtain ⟨p, he, hm, -⟩ := Fill.exec (instanceArgs N U s μ) (b.comap fillRegisters)
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.side, Cell.inst,
      Cell.matAB, Cell.matBC, Cell.matAC])
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.inst,
      Cell.matAB, Cell.matBC, Cell.matAC])
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.matAB, Cell.matBC, Cell.matAC])
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.matBC, Cell.matAC])
    (by simp [b, instanceArgs])
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.len, Cell.base, Cell.filler,
      Cell.side, Cell.inst, Cell.matAB, Cell.matBC, Cell.matAC])
    (by simp +decide [b, instanceArgs, fillRegisters, Cell.base, Cell.filler,
      Cell.side, Cell.inst, Cell.matAB, Cell.matBC, Cell.matAC]) hbf
    hmem hidx hF hnF hμ
    (hsize.of_le (by dsimp [instanceArgs]; omega))
    (hsize.of_le (by dsimp [instanceArgs]; omega))
    (hsize.of_le (by dsimp [instanceArgs]; omega))
    (hsize.of_le (by dsimp [instanceArgs]; omega))
    (by dsimp [instanceArgs]; omega) (by dsimp [instanceArgs]; omega)
    (by dsimp [instanceArgs]; omega)
  let y := p.extend fillRegisters b
  have hy : ExecWithin (w + 2) (Fill.program.rename fillRegisters) b y
      (131 * (sideLength N * sideLength N) + 5) := he.rename fill_injective
  have hyr (i : Fin 64) (hi : 34 ≤ i.val) : y.regs i = x.regs i := by
    refine (hy.regs_eq ?_).trans (hbregs i hi)
    apply Code.preserves_rename_of_forall_ne
    intro j heq
    have hv := congrArg Fin.val heq
    dsimp only [fillRegisters] at hv
    have := j.isLt
    omega
  refine ⟨y, ?_, parameters_of_regs hp (fun i hi _ _ => hyr i hi), (hyr inst (by decide)).trans hs,
    hyr found (by decide), hm, ?_⟩
  · convert hb.seq hy using 1 <;> first | rfl | omega
  · intro a ha
    change p.mem a = x.mem a
    rw [hm]
    apply Fill.Args.outside_filled
    all_goals dsimp [instanceArgs]; omega

/-- The host register bank is embedded injectively. -/
theorem hostRegisters_injective {r : ℕ} : (hostRegisters (r := r)).Injective := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (64 + r) => k.val) h)

private theorem solver_injective {r : ℕ} : (solverRegisters (r := r)).Injective := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [solverRegisters] at this
  omega

private theorem exec_solverSetup {w r : ℕ} (x : Data (64 + (r + 7))) :
    ∃ y, ExecWithin w solverSetup x y 6 ∧
      (∀ i, y.regs (hostRegisters i) = x.regs (hostRegisters i)) ∧ y.mem = x.mem ∧
      y.regs (callRegisters 0) = x.regs (hostRegisters side) ∧
      y.regs (callRegisters 1) = x.regs (hostRegisters filler) ∧
      y.regs (callRegisters 2) = x.regs (hostRegisters matAB) ∧
      y.regs (callRegisters 3) = x.regs (hostRegisters matBC) ∧
      y.regs (callRegisters 4) = x.regs (hostRegisters matAC) ∧
      y.regs (callRegisters 5) = x.regs (hostRegisters free) := by
  refine ⟨?y, ?exec, ?frame, ?mem, ?side, ?bound, ?ab, ?bc, ?ac, ?free⟩
  case exec => ram_eval [solverSetup, callRegisters, solverArg, solverRegisters,
    hostRegisters, side, filler,
    matAB, matBC, matAC, free, Fin.mk.injEq]
  case frame =>
    intro i
    have hlt := i.isLt
    simp only [Data.set_regs, Function.update_apply, hostRegisters, Fin.mk.injEq]
    split_ifs <;> omega
  all_goals simp +decide [Data.set_regs, callRegisters, solverArg, solverRegisters, hostRegisters]

private theorem exec_finish {w r s : ℕ} (x : Data (64 + (r + 7)))
    (ho : x.regs (hostRegisters one) = 1) (hi : x.regs (hostRegisters inst) = s)
    (hfit : Fits w (s + 1)) :
    ∃ y, ExecWithin w finish x y 4 ∧
      y.regs (hostRegisters inst) = s + 1 ∧
      y.regs (hostRegisters found) =
        (if x.regs (callRegisters 6) = 1 then 1 else x.regs (hostRegisters found)) ∧
      (∀ i : Fin 64, i ≠ inst → i ≠ found →
        y.regs (hostRegisters i) = x.regs (hostRegisters i)) ∧ y.mem = x.mem := by
  change x.regs ⟨45, by omega⟩ = 1 at ho
  change x.regs ⟨42, by omega⟩ = s at hi
  by_cases ha : x.regs (callRegisters 6) = 1
  · change x.regs ⟨70, by omega⟩ = 1 at ha
    refine ⟨(x.set (hostRegisters found) 1).set (hostRegisters inst) (s + 1),
      ?exec, ?inst, ?found, ?frame, ?mem⟩
    case exec =>
      apply ExecWithin.of_eval (fuel := 0) (n := 3)
      · simp +decide [finish, Code.eval, Op.eval_copy, Op.eval_bin, Data.put,
          Data.set_regs, Cond.holds_eq, BinOp.eval,
          callRegisters, solverArg, solverRegisters, hostRegisters, one, inst, found,
          ho, hi, ha, hfit]
      · omega
    case inst => simp
    case found =>
      simp +decide [ha, callRegisters, solverArg, solverRegisters, hostRegisters, inst, found]
    case frame =>
      intro i hi hf
      have hni := (hostRegisters_injective (r := r + 7)).ne hi
      have hnf := (hostRegisters_injective (r := r + 7)).ne hf
      simp only [Data.set_regs, Function.update_of_ne hni, Function.update_of_ne hnf]
    case mem => rfl
  · change ¬x.regs ⟨70, by omega⟩ = 1 at ha
    refine ⟨(x.set (hostRegisters found) (x.regs (hostRegisters found))).set
      (hostRegisters inst) (s + 1), ?exec, ?inst, ?found, ?frame, ?mem⟩
    case exec =>
      apply ExecWithin.of_eval (fuel := 0) (n := 4)
      · simp +decide [finish, Code.eval, Op.eval_copy, Op.eval_bin, Data.put,
          Data.set_regs, Cond.holds_eq, BinOp.eval,
          callRegisters, solverArg, solverRegisters, hostRegisters, one, inst, found,
          ho, hi, ha, hfit]
      · omega
    case inst => simp
    case found =>
      simp +decide [ha, callRegisters, solverArg, solverRegisters, hostRegisters, inst, found]
    case frame =>
      intro i hi hf
      have hni := (hostRegisters_injective (r := r + 7)).ne hi
      have hnf := (hostRegisters_injective (r := r + 7)).ne hf
      simp only [Data.set_regs, Function.update_of_ne hni, Function.update_of_ne hnf]
    case mem => rfl

/-- One generated instance, with the concrete solver's native execution proof supplied by the
caller. The solver may overwrite matrices and scratch, but preserves the length header and input.
The matrices in its premise are produced by the native builder, with no supplied layout oracle. -/
theorem exec_round {w r N U s T : ℕ} (μ : ℕ → ℤ)
    (solver : Code .standard (r + 7)) (x : Data (64 + (r + 7)))
    (hp : Parameters N U (x.comap hostRegisters))
    (hs : x.regs (hostRegisters inst) = s) (hslt : s < 2 * sideLength N)
    (hf : x.regs (hostRegisters found) ≤ 1)
    (hmem : ∀ i < N, x.mem (1 + i) = encode (μ i))
    (hidx : GenericRAM.Signed.Fits w ((2 * (sideLength N * sideLength N) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w (2 * (U : ℤ) + 1))
    (hnF : GenericRAM.Signed.Fits w (-(2 * (U : ℤ) + 1)))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (hsize : Fits (w + 2) (N + 1 + 3 * (sideLength N * sideLength N)))
    (hsolver : ∀ (a : Data (r + 7)) (mem : ℕ → ℕ),
      a.regs (solverArg 0) = sideLength N → a.regs (solverArg 1) = 2 * U + 1 →
      a.regs (solverArg 2) = N + 1 →
      a.regs (solverArg 3) = N + 1 + sideLength N * sideLength N →
      a.regs (solverArg 4) = N + 1 + 2 * (sideLength N * sideLength N) →
      a.regs (solverArg 5) = N + 1 + 3 * (sideLength N * sideLength N) →
      a.mem = (instanceArgs N U s μ).filled mem (sideLength N * sideLength N) →
      ∃ b, ExecWithin (w + 2) solver a b T ∧ b.regs (solverArg 6) ≤ 1 ∧
        (b.regs (solverArg 6) = 1 ↔ hit N U s μ) ∧
        (∀ a < N + 1, b.mem a = mem a)) :
    ∃ y, ExecWithin (w + 2) (round solver) x y
        (131 * (sideLength N * sideLength N) + T + 23) ∧
      Parameters N U (y.comap hostRegisters) ∧ y.regs (hostRegisters inst) = s + 1 ∧
      y.regs (hostRegisters found) ≤ 1 ∧
      (y.regs (hostRegisters found) = 1 ↔ x.regs (hostRegisters found) = 1 ∨ hit N U s μ) ∧
      (∀ a < N + 1, y.mem a = x.mem a) := by
  obtain ⟨a, ha, hap, hasi, haf, ham, -⟩ :=
    exec_fill μ (x.comap hostRegisters) hp hs hmem hidx hF hnF hμ hsize
  let y := a.extend hostRegisters x
  have hy : ExecWithin (w + 2) (fill.rename hostRegisters) x y
      (131 * (sideLength N * sideLength N) + 13) := ha.rename hostRegisters_injective
  have hyc : y.comap hostRegisters = a := Data.comap_extend hostRegisters_injective _ _
  have hyp : Parameters N U (y.comap hostRegisters) := by rw [hyc]; exact hap
  have hysi : y.regs (hostRegisters inst) = s :=
    (hostRegisters_injective.extend_apply _ _ inst).trans hasi
  have hyf : y.regs (hostRegisters found) = x.regs (hostRegisters found) :=
    (hostRegisters_injective.extend_apply _ _ found).trans haf
  obtain ⟨b, hb, hbr, hbm, hb0, hb1, hb2, hb3, hb4, hb5⟩ := exec_solverSetup (w := w + 2) y
  have hbp : Parameters N U (b.comap hostRegisters) :=
    parameters_of_regs hyp (fun i _ _ _ => hbr i)
  obtain ⟨c, hc, hcans, hchit, hcm⟩ := hsolver (b.comap solverRegisters) x.mem
    (hb0.trans hyp.side) (hb1.trans hyp.filler) (hb2.trans hyp.ab)
    (hb3.trans hyp.bc) (hb4.trans hyp.ac) (hb5.trans hyp.free)
    (hbm.trans ham)
  let z := c.extend solverRegisters b
  have hz : ExecWithin (w + 2) (solver.rename solverRegisters) b z T :=
    hc.rename solver_injective
  have hzr (i : Fin 64) : z.regs (hostRegisters i) = b.regs (hostRegisters i) := by
    apply hz.regs_eq
    apply Code.preserves_rename_of_forall_ne
    intro j he
    have hv := congrArg Fin.val he
    dsimp only [solverRegisters, hostRegisters] at hv
    have := i.isLt
    omega
  have hzp : Parameters N U (z.comap hostRegisters) :=
    parameters_of_regs hbp (fun i _ _ _ => hzr i)
  have hzsi : z.regs (hostRegisters inst) = s :=
    (hzr inst).trans ((hbr inst).trans hysi)
  have hzf : z.regs (hostRegisters found) = x.regs (hostRegisters found) :=
    (hzr found).trans ((hbr found).trans hyf)
  have hza : z.regs (callRegisters 6) = c.regs (solverArg 6) :=
    solver_injective.extend_apply _ _ _
  have hinc : Fits (w + 2) (s + 1) := hsize.of_le (by
    have := Nat.le_mul_self (sideLength N)
    omega)
  obtain ⟨q, hq, hqi, hqf, hqr, hqm⟩ := exec_finish z hzp.one hzsi hinc
  have hqp : Parameters N U (q.comap hostRegisters) :=
    parameters_of_regs hzp (fun i _ hi hf => hqr i hi hf)
  refine ⟨q, ?_, hqp, hqi, ?_, ?_, ?_⟩
  · exact (hy.seq (hb.seq (hz.seq hq))).mono (by omega)
  · rw [hqf, hza, hzf]
    split_ifs <;> omega
  · rw [hqf, hza, hzf]
    by_cases h : c.regs (solverArg 6) = 1
    · simp only [h, ↓reduceIte, hchit.mp h, or_true]
    · simp only [h, ↓reduceIte, hchit.not.mp h, or_false]
  · intro a ha
    rw [hqm]
    exact hcm a ha

/-- The complete native instance loop. Its invariant records exactly the instances already
examined, retains the original input, and charges every solver call and loop instruction. -/
theorem exec_loop {w r N U T : ℕ} (μ : ℕ → ℤ)
    (solver : Code .standard (r + 7)) (x : Data (64 + (r + 7)))
    (hp : Parameters N U (x.comap hostRegisters))
    (hi : x.regs (hostRegisters inst) = 0) (hf : x.regs (hostRegisters found) = 0)
    (hmem : ∀ i < N, x.mem (1 + i) = encode (μ i))
    (hidx : ∀ s < 2 * sideLength N,
      GenericRAM.Signed.Fits w ((2 * (sideLength N * sideLength N) + s + 1 : ℕ) : ℤ))
    (hF : GenericRAM.Signed.Fits w (2 * (U : ℤ) + 1))
    (hnF : GenericRAM.Signed.Fits w (-(2 * (U : ℤ) + 1)))
    (hμ : ∀ i < N, GenericRAM.Signed.Fits w (μ i))
    (hsize : Fits (w + 2) (N + 1 + 3 * (sideLength N * sideLength N)))
    (hsolver : ∀ s < 2 * sideLength N, ∀ (a : Data (r + 7)) (mem : ℕ → ℕ),
      a.regs (solverArg 0) = sideLength N → a.regs (solverArg 1) = 2 * U + 1 →
      a.regs (solverArg 2) = N + 1 →
      a.regs (solverArg 3) = N + 1 + sideLength N * sideLength N →
      a.regs (solverArg 4) = N + 1 + 2 * (sideLength N * sideLength N) →
      a.regs (solverArg 5) = N + 1 + 3 * (sideLength N * sideLength N) →
      a.mem = (instanceArgs N U s μ).filled mem (sideLength N * sideLength N) →
      ∃ b, ExecWithin (w + 2) solver a b T ∧ b.regs (solverArg 6) ≤ 1 ∧
        (b.regs (solverArg 6) = 1 ↔ hit N U s μ) ∧
        (∀ a < N + 1, b.mem a = mem a)) :
    ∃ y, ExecWithin (w + 2) (loop solver) x y
        (2 * sideLength N * (131 * (sideLength N * sideLength N) + T + 25) + 2) ∧
      Parameters N U (y.comap hostRegisters) ∧
      y.regs (hostRegisters inst) = 2 * sideLength N ∧
      y.regs (hostRegisters found) ≤ 1 ∧
      (y.regs (hostRegisters found) = 1 ↔ ∃ s < 2 * sideLength N, hit N U s μ) ∧
      (∀ a < N + 1, y.mem a = x.mem a) := by
  let I (y : Data (64 + (r + 7))) : Prop :=
    Parameters N U (y.comap hostRegisters) ∧
      y.regs (hostRegisters inst) ≤ 2 * sideLength N ∧
      y.regs (hostRegisters found) ≤ 1 ∧
      (y.regs (hostRegisters found) = 1 ↔ ∃ s < y.regs (hostRegisters inst), hit N U s μ) ∧
      (∀ a < N + 1, y.mem a = x.mem a)
  have hbody (y : Data (64 + (r + 7))) (hy : I y)
      (hc : (Cond.lt (hostRegisters inst) (hostRegisters stop)).Holds y) :
      ∃ z, ExecWithin (w + 2) (round solver) y z
          (131 * (sideLength N * sideLength N) + T + 23) ∧ I z ∧
        2 * sideLength N - z.regs (hostRegisters inst) <
          2 * sideLength N - y.regs (hostRegisters inst) := by
    obtain ⟨hyp, hys, hyf, hyans, hym⟩ := hy
    have hlt : y.regs (hostRegisters inst) < 2 * sideLength N := by
      change y.regs (hostRegisters inst) < y.regs (hostRegisters stop) at hc
      exact hc.trans_eq hyp.stop
    have hyinput : ∀ i < N, y.mem (1 + i) = encode (μ i) := by
      intro i hi
      rw [hym _ (by omega)]
      exact hmem i hi
    obtain ⟨z, hz, hzp, hzsi, hzf, hzans, hzm⟩ := exec_round μ solver y hyp rfl hlt
      hyf hyinput (hidx _ hlt) hF hnF hμ hsize (hsolver _ hlt)
    refine ⟨z, hz, ⟨hzp, by omega, hzf, ?_, ?_⟩, by omega⟩
    · rw [hzans, hyans, hzsi]
      constructor
      · rintro (⟨s, hs, hh⟩ | hh)
        · exact ⟨s, by omega, hh⟩
        · exact ⟨_, by omega, hh⟩
      · rintro ⟨s, hs, hh⟩
        by_cases h : s < y.regs (hostRegisters inst)
        · exact Or.inl ⟨s, h, hh⟩
        · have he : s = y.regs (hostRegisters inst) := by omega
          exact Or.inr (he ▸ hh)
    · intro a ha
      exact (hzm a ha).trans (hym a ha)
  have hx : I x := ⟨hp, by omega, by omega, by simp [hi, hf], fun _ _ => rfl⟩
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => 2 * sideLength N - y.regs (hostRegisters inst)) hbody hx
  obtain ⟨hyp, hyi, hyf, hyans, hym⟩ := hy
  have hend : y.regs (hostRegisters inst) = 2 * sideLength N := by
    change ¬y.regs (hostRegisters inst) < y.regs (hostRegisters stop) at hc
    have hstop : y.regs (hostRegisters stop) = 2 * sideLength N := hyp.stop
    omega
  refine ⟨y, ?_, hyp, hend, hyf, ?_, hym⟩
  · simpa only [loop, hi, Nat.sub_zero, Nat.add_assoc, Nat.reduceAdd] using he
  · simpa only [hend] using hyans

end Cslib.Algorithms.WordRAM.ThreeSum.Host
