/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.PPZ.Forced
public import Complexity.Algorithms.WordRAM.Schoening.Trial
public import Complexity.Computability.Complexity.FineGrained.PPZ.LazyOrder
public import Complexity.Computability.WordRAM.Randomized.Law
import Complexity.Probability.PMF.Map

/-!
# One round of PPZ on the randomized word RAM

`Cslib.Algorithms.WordRAM.PPZ.roundProgram` is one round of the PPZ algorithm
[Paturi, Pudlák, Zane][PPZ1997] as a program of the randomized word RAM
(`Cslib.WordRAM.runRand`). On the input `encode φ`, the number `n` of variables followed by the
clauses of `φ : CNF (Fin n)`, it

1. stores the empty partial assignment `τ` (the word `2` for every variable) and the array
   `P = [0, 1, …, n - 1]` just after the input;
2. for `i = 0, …, n - 1`: draws `j` uniformly from `[i, n)`, swaps `P[i]` and `P[j]`, and sets the
   variable `x = P[i]` to its forced value (`Cslib.Complexity.PPZ.forced`, computed by
   `Cslib.Algorithms.WordRAM.PPZ.forcedCode`), or to a uniform bit if it has none;
3. halts with output `1` if the assignment it built satisfies `φ`, and `0` otherwise.

Step 2 is the Fisher–Yates shuffle, run lazily: the variables still to be processed are
`P[i], …, P[n - 1]`, and the swap brings a uniformly chosen one of them to position `i`. This is
exactly the recursion `Cslib.Complexity.PPZ.roundOn_succ`, so each iteration of the loop matches one
step of `Cslib.Complexity.PPZ.roundOn` (`Cslib.Algorithms.WordRAM.PPZ.roundLoop_law`), and
`Cslib.Complexity.PPZ.roundWith_eq_roundOn` identifies the whole loop with a round.

`Cslib.Algorithms.WordRAM.PPZ.roundProgram_spec` proves that the program halts on every path within
`roundTime n L = n (28 L + 40) + 12 L + 19` instructions, where `L` is the input length, makes at
most `2 n` `rand` calls, reports correctly whether the assignment it leaves satisfies `φ`, and that
the law of that assignment is exactly `Cslib.Complexity.PPZ.round φ`. The PPZ success bound
`Cslib.Complexity.PPZ.round_success_of_satisfiable` therefore applies to the program. Time is the
instruction count of the word RAM with unit-cost `rand` (`Cslib.WordRAM.stepRand`); every
instruction counts, including loop tests and jumps.

The final check reuses Schöning's clause scan `Cslib.Algorithms.WordRAM.Schoening.scan`, renamed
into the register file of this program along `Cslib.Algorithms.WordRAM.PPZ.embed`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPZ.partialAssignmentAt`: reading back a stored partial assignment.
* `Cslib.Algorithms.WordRAM.PPZ.RoundFrame`: the registers and memory a round relies on.
* `Cslib.Algorithms.WordRAM.PPZ.roundBody`, `Cslib.Algorithms.WordRAM.PPZ.roundLoop`,
  `Cslib.Algorithms.WordRAM.PPZ.roundCore`, `Cslib.Algorithms.WordRAM.PPZ.roundCheck`: the parts of
  a round.
* `Cslib.Algorithms.WordRAM.PPZ.embed`: Schöning's registers inside the register file of PPZ.
* `Cslib.Algorithms.WordRAM.PPZ.roundCode`, `Cslib.Algorithms.WordRAM.PPZ.roundProgram`: a round on
  the input `encode φ`, structured and compiled.
* `Cslib.Algorithms.WordRAM.PPZ.roundTime`: its instruction bound.
* `Cslib.Algorithms.WordRAM.PPZ.cfgPartial`: the partial assignment left by a halting run.

## Main results

* `Cslib.Algorithms.WordRAM.PPZ.roundBody_law`: one step of the loop is one step of the lazy order.
* `Cslib.Algorithms.WordRAM.PPZ.roundLoop_law`: the loop has the law of
  `Cslib.Complexity.PPZ.roundOn`.
* `Cslib.Algorithms.WordRAM.PPZ.roundCore_law`: the round body has the law of
  `Cslib.Complexity.PPZ.round`.
* `Cslib.Algorithms.WordRAM.PPZ.roundCheck_exec`: the satisfaction check.
* `Cslib.Algorithms.WordRAM.PPZ.roundProgram_spec`: halting, time and `rand` bounds, a correct
  output, and the exact law of a round for the compiled program.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPZ
open Cslib.Algorithms.WordRAM.Schoening (encodeClauses encode AssignAt assignmentAt
  assignmentAt_eq assignAt_assignmentAt length_encode ScanResult firstUnsat_eq_none_iff)

variable {n : ℕ}

/-! ### Reading partial assignments -/

/-- The value of a partial assignment stored as the word `v`: `0` and `1` are set values, any
other word is unset. -/
def optDecode : ℕ → Option Bool
  | 0 => some false
  | 1 => some true
  | _ + 2 => none

@[simp]
theorem optDecode_optCode (o : Option Bool) : optDecode (optCode o) = o := by
  rcases o with _ | b
  · rfl
  · cases b <;> rfl

/-- The partial assignment read from the `n` words at address `base`. -/
def partialAssignmentAt (mem : ℕ → ℕ) (base n : ℕ) : Fin n → Option Bool :=
  fun i => optDecode (mem (base + i))

/-- Reading back a stored partial assignment. -/
theorem partialAssignmentAt_eq {mem : ℕ → ℕ} {base : ℕ} {τ : Fin n → Option Bool}
    (h : PartialAt mem base τ) : partialAssignmentAt mem base n = τ := by
  funext i
  rw [partialAssignmentAt, h i, optDecode_optCode]

/-! ### Registers -/

namespace Reg

/-- Address of the order array `P`. -/
abbrev pBase : Fin 32 := 23
/-- The step `i`. -/
abbrev iReg : Fin 32 := 24
/-- The drawn position `j`. -/
abbrev jReg : Fin 32 := 25
/-- The address of `P[i]`. -/
abbrev aI : Fin 32 := 26
/-- The address of `P[j]`. -/
abbrev aJ : Fin 32 := 27
/-- Output. -/
abbrev out : Fin 32 := 28
/-- Where the renamed Schöning scan reports a falsified clause
(`embed Cslib.Algorithms.WordRAM.Schoening.Reg.found`). -/
abbrev sFound : Fin 32 := 16

end Reg

open Reg

/-! ### The frame of a round -/

/-- The registers and memory a round relies on: the constants, the clauses of `φ` stored in
`[C, Tb)`, the partial assignment's address `Tb`, the order array's address `Tb + n`, and `n`. The
memory from address `Tb + 2 n` on, just after the order array, agrees with `M`; a round never
writes there. -/
structure RoundFrame (φ : CNF (Fin n)) (C Tb : ℕ) (M : ℕ → ℕ) (x : Data 32) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  two_eq : x.regs two = 2
  cBeg_eq : x.regs cBeg = C
  cEnd_eq : x.regs cEnd = Tb
  tBase_eq : x.regs tBase = Tb
  nReg_eq : x.regs nReg = n
  pBase_eq : x.regs pBase = Tb + n
  clauses : HoldsList C (encodeClauses φ) x.mem
  span : C + (encodeClauses φ).length = Tb
  rest : ∀ a, Tb + 2 * n ≤ a → x.mem a = M a

/-- The frame survives any change that keeps its registers and the memory outside
`[Tb, Tb + 2 n)`. -/
theorem RoundFrame.congr {φ : CNF (Fin n)} {C Tb : ℕ} {M : ℕ → ℕ} {x y : Data 32}
    (h : RoundFrame φ C Tb M x) (hz : y.regs zero = x.regs zero) (ho : y.regs one = x.regs one)
    (ht : y.regs two = x.regs two) (hc : y.regs cBeg = x.regs cBeg)
    (he : y.regs cEnd = x.regs cEnd) (hb : y.regs tBase = x.regs tBase)
    (hn : y.regs nReg = x.regs nReg) (hp : y.regs pBase = x.regs pBase)
    (hmem : ∀ a, a < Tb ∨ Tb + 2 * n ≤ a → y.mem a = x.mem a) : RoundFrame φ C Tb M y where
  zero_eq := hz.trans h.zero_eq
  one_eq := ho.trans h.one_eq
  two_eq := ht.trans h.two_eq
  cBeg_eq := hc.trans h.cBeg_eq
  cEnd_eq := he.trans h.cEnd_eq
  tBase_eq := hb.trans h.tBase_eq
  nReg_eq := hn.trans h.nReg_eq
  pBase_eq := hp.trans h.pBase_eq
  clauses := h.clauses.frame fun a _ ha' => hmem a (Or.inl (h.span ▸ ha'))
  span := h.span
  rest a ha := (hmem a (Or.inr ha)).trans (h.rest a ha)

/-- The frame with the memory after the order array taken as it is. -/
theorem RoundFrame.self {φ : CNF (Fin n)} {C Tb : ℕ} {M : ℕ → ℕ} {x : Data 32}
    (h : RoundFrame φ C Tb M x) : RoundFrame φ C Tb x.mem x :=
  { h with rest := fun _ _ => rfl }

/-- Code that writes none of the frame registers. -/
def PreservesRound (c : Code .standard 32) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves two ∧ c.Preserves cBeg ∧ c.Preserves cEnd ∧
    c.Preserves tBase ∧ c.Preserves nReg ∧ c.Preserves pBase

instance (c : Code .standard 32) : Decidable (PreservesRound c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A deterministic run of frame-preserving code that keeps the memory outside `[Tb, Tb + 2 n)`
keeps the frame. -/
theorem RoundFrame.of_execWithin {φ : CNF (Fin n)} {C Tb : ℕ} {M : ℕ → ℕ} {c : Code .standard 32}
    {x y : Data 32} {w T : ℕ} (h : RoundFrame φ C Tb M x) (hc : PreservesRound c)
    (he : ExecWithin w c x y T) (hmem : ∀ a, a < Tb ∨ Tb + 2 * n ≤ a → y.mem a = x.mem a) :
    RoundFrame φ C Tb M y :=
  h.congr (he.regs_eq hc.1) (he.regs_eq hc.2.1) (he.regs_eq hc.2.2.1) (he.regs_eq hc.2.2.2.1)
    (he.regs_eq hc.2.2.2.2.1) (he.regs_eq hc.2.2.2.2.2.1) (he.regs_eq hc.2.2.2.2.2.2.1)
    (he.regs_eq hc.2.2.2.2.2.2.2) hmem

/-- The frame after setting a register outside it. -/
theorem RoundFrame.set {φ : CNF (Fin n)} {C Tb : ℕ} {M : ℕ → ℕ} {x : Data 32}
    (h : RoundFrame φ C Tb M x) {i : Fin 32}
    (hi : i ∉ ({zero, one, two, cBeg, cEnd, tBase, nReg, pBase} : Finset (Fin 32))) (v : ℕ) :
    RoundFrame φ C Tb M (x.set i v) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hi
  exact h.congr (by simp [Function.update_of_ne (Ne.symm h0)])
    (by simp [Function.update_of_ne (Ne.symm h1)]) (by simp [Function.update_of_ne (Ne.symm h2)])
    (by simp [Function.update_of_ne (Ne.symm h3)]) (by simp [Function.update_of_ne (Ne.symm h4)])
    (by simp [Function.update_of_ne (Ne.symm h5)]) (by simp [Function.update_of_ne (Ne.symm h6)])
    (by simp [Function.update_of_ne (Ne.symm h7)]) fun _ _ => rfl

/-! ### The initial arrays -/

/-- Store `τ[i] = 2` (unset) and `P[i] = i`, and count. -/
def initBody : Code .standard 32 := ram[
  addr ← tBase + iReg; *addr ← two; addr ← pBase + iReg; *addr ← iReg; iReg ← iReg + one ]

/-- Initialize the entries `iReg, …, n - 1` of both arrays. -/
def initLoop : Code .standard 32 := .loop (.lt iReg nReg) initBody

/-- The initial arrays from entry `i` on: the first `i` entries of both arrays are stored, and the
loop stores the others. -/
theorem initLoop_spec {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} (hw : Fits w (Tb + 2 * n)) :
    ∀ (d : ℕ) (x : Data 32), RoundFrame φ C Tb M x → x.regs iReg + d = n →
      (∀ v < x.regs iReg, x.mem (Tb + v) = 2 ∧ x.mem (Tb + n + v) = v) →
      ∃ y, ExecWithin w initLoop x y (7 * d + 2) ∧ RoundFrame φ C Tb M y ∧
        ∀ v < n, y.mem (Tb + v) = 2 ∧ y.mem (Tb + n + v) = v
  | 0, x, hx, hd, hv => by
    have hc : ¬(Cond.lt iReg nReg).Holds x := by simp [Cond.holds_lt, hx.nReg_eq]; omega
    exact ⟨x, (ExecWithin.loop_exit hc).mono (by omega), hx, fun v hv' => hv v (by omega)⟩
  | d + 1, x, hx, hd, hv => by
    obtain ⟨i, hi⟩ : ∃ i, x.regs iReg = i := ⟨_, rfl⟩
    rw [hi] at hd hv
    have hc : (Cond.lt iReg nReg).Holds x := by simp [Cond.holds_lt, hx.nReg_eq, hi]; omega
    have hf1 : Fits w (Tb + i) := hw.of_le (by omega)
    have hf2 : Fits w (Tb + n + i) := hw.of_le (by omega)
    have hf3 : Fits w (i + 1) := hw.of_le (by omega)
    let y := (((((x.set addr (Tb + i)).write (Tb + i) 2).set addr (Tb + n + i)).write
      (Tb + n + i) i).set iReg (i + 1))
    have hrun : ExecWithin w initBody x y 5 := by
      ram_eval [y, initBody, hx.tBase_eq, hx.pBase_eq, hx.two_eq, hx.one_eq, hi, hf1, hf2, hf3]
    have hym : y.mem = Function.update (Function.update x.mem (Tb + i) 2) (Tb + n + i) i := rfl
    have hy : RoundFrame φ C Tb M y := hx.of_execWithin (by decide) hrun fun a ha => by
      rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    obtain ⟨z, hz, hzf, hzv⟩ := initLoop_spec hw d y hy (by simp [y]; omega) (fun v hv' => by
      simp only [y, Data.set_regs, Function.update_self] at hv'
      rw [hym]
      by_cases hvi : v = i
      · subst hvi
        refine ⟨?_, by simp⟩
        rw [Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hv v (by omega))
    exact ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by omega), hzf, hzv⟩

/-! ### One step of the round -/

/-- Swap `P[i]` and `P[j]`, where `jReg` holds the draw `j - i`, and load the new `P[i]` into
`xReg`. -/
def swapCode : Code .standard 32 := ram[
  jReg ← jReg + iReg; aI ← pBase + iReg; aJ ← pBase + jReg; val ← *aI; xReg ← *aJ; *aI ← xReg;
  *aJ ← val ]

/-- Without a forced value, draw a uniform bit. -/
def bitCode : Code .standard 32 := ram[ if res = two then [ res ← rand one ] else [ res ← res ] ]

/-- Store the value of `x` and count the step. -/
def storeCode : Code .standard 32 := ram[ addr ← tBase + xReg; *addr ← res; iReg ← iReg + one ]

/-- **One step of a round**: draw `j - i` uniformly from `[0, n - 1 - i]`, swap `P[i]` and `P[j]`,
and set `x = P[i]` to its forced value or to a uniform bit. -/
def roundBody : Code .standard 32 := ram[
  jReg ← nReg - iReg; jReg ← jReg - one; jReg ← rand jReg; ⟪swapCode⟫; ⟪forcedCode⟫; ⟪bitCode⟫;
  ⟪storeCode⟫ ]

/-- **The steps of a round**: steps `iReg, …, n - 1`. -/
def roundLoop : Code .standard 32 := .loop (.lt iReg nReg) roundBody

/-- The state at the head of the round loop at step `i`: the frame, `iReg = i`, the partial
assignment `τ` stored at `Tb`, and the unprocessed variables `g 0, …, g (d - 1)` stored at
`P[i], P[i + 1], …`. Every variable that `τ` leaves unset is among them. -/
structure LoopState (φ : CNF (Fin n)) (C Tb : ℕ) (M : ℕ → ℕ) (i : ℕ) (τ : Fin n → Option Bool)
    {d : ℕ} (g : Fin d → Fin n) (x : Data 32) : Prop where
  frame : RoundFrame φ C Tb M x
  i_eq : x.regs iReg = i
  stored : PartialAt x.mem Tb τ
  order : ∀ t : Fin d, x.mem (Tb + n + i + t) = g t
  cover : ∀ v, τ v = none → ∃ t, g t = v

/-- A uniform draw from `[0, m]` observed through its value only depends on `m`. -/
private theorem uniform_map_val_congr {α : Type*} {m m' : ℕ} (h : m = m') (F : ℕ → α) :
    (Probability.PMF.uniformOfFintype (Fin (m + 1))).map (fun k => F k.val) =
      (Probability.PMF.uniformOfFintype (Fin (m' + 1))).map (fun k => F k.val) := by
  subst h
  rfl

/-- A uniform draw from `{0, 1}` is a uniform bit. -/
private theorem uniform_two_map_bit :
    (Probability.PMF.uniformOfFintype (Fin (1 + 1))).map (fun k => decide (k.val = 1)) =
      Probability.PMF.uniformOfFintype Bool := by
  have h := Probability.PMF.uniformOfFintype_map_equiv finTwoEquiv
  convert h using 2
  funext k
  fin_cases k <;> rfl

/-- The swapped order array: after `P[i]` and `P[i + k]` are swapped, position `i + t` holds
`g (swap 0 k t)`. -/
private theorem swap_order {m : ℕ} (g : Fin (m + 1) → Fin n) (k : Fin (m + 1)) (mem : ℕ → ℕ)
    (base : ℕ) (hg : ∀ t : Fin (m + 1), mem (base + t) = g t) (t : Fin (m + 1)) :
    Function.update (Function.update mem base (g k)) (base + k) (g 0) (base + t) =
      g (Equiv.swap 0 k t) := by
  by_cases htk : t = k
  · subst htk
    simp
  · rw [Function.update_of_ne (fun h => htk (Fin.ext (by omega)))]
    by_cases ht0 : t = 0
    · subst ht0
      simp [Equiv.swap_apply_left]
    · rw [Function.update_of_ne (fun h => ht0 (Fin.ext (by simp at h ⊢; omega))), hg t,
        Equiv.swap_apply_of_ne_of_ne ht0 htk]

/-- After processing `g p`, every variable left unset is among the remaining ones. -/
private theorem cover_succ {m : ℕ} {τ : Fin n → Option Bool} {g : Fin (m + 1) → Fin n}
    (hc : ∀ v, τ v = none → ∃ t, g t = v) (p : Fin (m + 1)) (b : Bool) :
    ∀ v, Function.update τ (g p) (some b) v = none →
      ∃ t : Fin m, g (Equiv.swap 0 p t.succ) = v := by
  intro v hv
  have hvp : v ≠ g p := fun h => by subst h; simp at hv
  rw [Function.update_of_ne hvp] at hv
  obtain ⟨t, rfl⟩ := hc v hv
  have htp : t ≠ p := fun h => hvp (h ▸ rfl)
  set s := Equiv.swap 0 p t with hs
  have hs0 : s ≠ 0 := fun h => htp (by
    have := congrArg (Equiv.swap 0 p) h
    simpa [hs] using this)
  refine ⟨s.pred hs0, ?_⟩
  rw [Fin.succ_pred, hs, Equiv.swap_apply_self]

/-- The scan frame of a round frame, for the variable in `xReg` and the partial assignment
stored at `Tb`. -/
theorem RoundFrame.scanFrame {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} {y : Data 32}
    (h : RoundFrame φ C Tb M y) {τ : Fin n → Option Bool} {v : Fin n} (hv : y.regs xReg = v)
    (hs : PartialAt y.mem Tb τ) (hw : Fits w (Tb + 2 * n)) (hT : 1 ≤ Tb) :
    ScanFrame w τ v y where
  zero_eq := h.zero_eq
  one_eq := h.one_eq
  two_eq := h.two_eq
  x_eq := hv
  stored := by rw [h.tBase_eq]; exact hs
  fits := by rw [h.tBase_eq]; exact hw
  pos := by rw [h.tBase_eq]; exact hT

/-- The postcondition of the step from step `i`: for the drawn position `p` and the value `b` set,
`jReg = i + p`, `res = b`, and the loop state at step `i + 1` after processing `g p`. -/
def StepPost (φ : CNF (Fin n)) (C Tb : ℕ) (M : ℕ → ℕ) (i : ℕ) (τ : Fin n → Option Bool) {m : ℕ}
    (g : Fin (m + 1) → Fin n) (y : Data 32) : Prop :=
  ∃ (p : Fin (m + 1)) (b : Bool), y.regs jReg = i + p ∧ y.regs res = b.toNat ∧
    LoopState φ C Tb M (i + 1) (Function.update τ (g p) (some b))
      (fun t : Fin m => g (Equiv.swap 0 p t.succ)) y

/-- **One step of a round** draws the position `p` uniformly from the `m + 1` unprocessed
positions and sets `g p` with the law of `Cslib.Complexity.PPZ.step`, within `28 E + 31`
instructions and two `rand` calls. -/
theorem roundBody_law {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} (hw : Fits w (Tb + 2 * n))
    (hT : 1 ≤ Tb) {i m : ℕ} {τ : Fin n → Option Bool} {g : Fin (m + 1) → Fin n} {x : Data 32}
    (hx : LoopState φ C Tb M i τ g x) (hd : i + (m + 1) = n) :
    ExecRandLaw w roundBody x (StepPost φ C Tb M i τ g) (28 * (encodeClauses φ).length + 31) 2
      (fun y => (y.regs jReg - i, decide (y.regs res = 1)))
      ((Probability.PMF.uniformOfFintype (Fin (m + 1))).bind fun p =>
        (stepWith (forced φ) τ (g p)).map fun b => (p.val, b)) := by
  have hf := hx.frame
  have hf1 : Fits w (n - i) := hw.of_le (by omega)
  have hf2 : Fits w (n - i - 1) := hw.of_le (by omega)
  let x₂ := (x.set jReg (n - i)).set jReg (n - i - 1)
  have h₁ : ExecWithin w (ram[ jReg ← nReg - iReg ] : Code .standard 32) x (x.set jReg (n - i))
      1 := by
    ram_eval [hf.nReg_eq, hx.i_eq, hf1]
  have h₂ : ExecWithin w (ram[ jReg ← jReg - one ] : Code .standard 32) (x.set jReg (n - i)) x₂
      1 := by
    ram_eval [x₂, hf.one_eq, hf2]
  have hx₂j : x₂.regs jReg = m := by simp [x₂]; omega
  let F : Data 32 → ℕ × Bool := fun y => (y.regs jReg - i, decide (y.regs res = 1))
  let κ : ℕ → PMF (ℕ × Bool) := fun v =>
    if hv : v < m + 1 then (stepWith (forced φ) τ (g ⟨v, hv⟩)).map fun b => (v, b)
    else PMF.pure (0, false)
  -- after drawing `k`: the rest of the step
  have hrest : ∀ y, (∃ k : Fin (x₂.regs jReg + 1), y = x₂.set jReg k.val) →
      ExecRandLaw w (ram[ ⟪swapCode⟫; ⟪forcedCode⟫; ⟪bitCode⟫; ⟪storeCode⟫ ]) y
        (StepPost φ C Tb M i τ g) (28 * (encodeClauses φ).length + 28) 1 F (κ (y.regs jReg)) := by
    rintro y ⟨k', rfl⟩
    have hk : k'.val < m + 1 := by have := k'.isLt; omega
    set k : Fin (m + 1) := ⟨k'.val, hk⟩ with hkdef
    have hkv : (k : ℕ) = k'.val := rfl
    -- the swap
    have hm0 : x.mem (Tb + n + i) = (g 0 : ℕ) := by simpa using hx.order 0
    have hmk : x.mem (Tb + n + (k'.val + i)) = (g k : ℕ) := by
      rw [show Tb + n + (k'.val + i) = Tb + n + i + (k : ℕ) by omega]
      exact hx.order k
    have hfa : Fits w (k'.val + i) := hw.of_le (by omega)
    have hfb : Fits w (Tb + n + i) := hw.of_le (by omega)
    have hfc : Fits w (Tb + n + (k'.val + i)) := hw.of_le (by omega)
    let y₁ := ((((((((x₂.set jReg k'.val).set jReg (k'.val + i)).set aI (Tb + n + i)).set aJ
      (Tb + n + (k'.val + i))).set val (g 0 : ℕ)).set xReg (g k : ℕ)).write (Tb + n + i)
      (g k : ℕ)).write (Tb + n + (k'.val + i)) (g 0 : ℕ))
    have hswap : ExecWithin w swapCode (x₂.set jReg k'.val) y₁ 7 := by
      ram_eval [y₁, x₂, swapCode, hx.i_eq, hf.pBase_eq, hm0, hmk, hfa, hfb, hfc]
    have hy₁m : y₁.mem = Function.update (Function.update x.mem (Tb + n + i) (g k : ℕ))
        (Tb + n + i + (k : ℕ)) (g 0 : ℕ) := by
      simp only [y₁, Data.write_mem, Data.set_mem, x₂]
      rw [show Tb + n + (k'.val + i) = Tb + n + i + (k : ℕ) by omega]
    have hy₁far : ∀ a, a < Tb + n → y₁.mem a = x.mem a := fun a ha => by
      rw [hy₁m, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hfy₁ : RoundFrame φ C Tb M y₁ :=
      hf.congr (by simp +decide [y₁, x₂]) (by simp +decide [y₁, x₂]) (by simp +decide [y₁, x₂])
        (by simp +decide [y₁, x₂]) (by simp +decide [y₁, x₂]) (by simp +decide [y₁, x₂])
        (by simp +decide [y₁, x₂]) (by simp +decide [y₁, x₂]) fun a ha => by
          rw [hy₁m, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hst₁ : PartialAt y₁.mem Tb τ := fun v => by
      rw [hy₁far _ (by omega)]
      exact hx.stored v
    have hxr₁ : y₁.regs xReg = (g k : ℕ) := by simp [y₁]
    have hj₁ : y₁.regs jReg = k'.val + i := by simp +decide [y₁]
    have hi₁ : y₁.regs iReg = i := by simp +decide [y₁, x₂, hx.i_eq]
    -- the forced value
    obtain ⟨z, hz, hzm, hzr, hzs, hzce, hzcb⟩ := forcedCode_spec φ τ (g k) y₁
      (hfy₁.scanFrame hxr₁ hst₁ hw hT) (by rw [hfy₁.cBeg_eq]; exact hfy₁.clauses)
      (by rw [hfy₁.cBeg_eq, hfy₁.cEnd_eq]; exact hfy₁.span)
      (by rw [hfy₁.cEnd_eq]; exact hw.of_le (by omega))
    have hfz : RoundFrame φ C Tb M z := hfy₁.of_execWithin (by decide) hz fun a _ => by rw [hzm]
    have hjz : z.regs jReg = k'.val + i := (hz.regs_eq (by decide)).trans hj₁
    have hiz : z.regs iReg = i := (hz.regs_eq (by decide)).trans hi₁
    have hxz : z.regs xReg = (g k : ℕ) := hzs.x_eq
    -- the value set, and the store
    have hfs : Fits w (Tb + (g k : ℕ)) := hw.of_le (by omega)
    have hfi : Fits w (i + 1) := hw.of_le (by omega)
    have hstore : ∀ b : Bool, ∃ Y, ExecWithin w storeCode (z.set res b.toNat) Y 3 ∧
        StepPost φ C Tb M i τ g Y ∧ F Y = F (z.set res b.toNat) := by
      intro b
      let Y := (((z.set res b.toNat).set addr (Tb + (g k : ℕ))).write (Tb + (g k : ℕ))
        b.toNat).set iReg (i + 1)
      have hrun : ExecWithin w storeCode (z.set res b.toNat) Y 3 := by
        ram_eval [Y, storeCode, hfz.tBase_eq, hxz, hiz, hfz.one_eq, hfs, hfi]
      have hYm : Y.mem = Function.update z.mem (Tb + (g k : ℕ)) b.toNat := rfl
      refine ⟨Y, hrun, ⟨k, b, by simp +decide [Y, hjz]; omega, by simp +decide [Y], ?_⟩,
        by simp +decide [Y, F]⟩
      refine ⟨hfz.congr (by simp +decide [Y]) (by simp +decide [Y]) (by simp +decide [Y])
        (by simp +decide [Y]) (by simp +decide [Y]) (by simp +decide [Y]) (by simp +decide [Y])
        (by simp +decide [Y]) fun a ha => ?_, by simp +decide [Y], ?_, ?_, cover_succ hx.cover k b⟩
      · rw [hYm, Function.update_of_ne (by omega)]
      · intro v
        rw [hYm, hzm]
        by_cases hv : v = g k
        · subst hv
          simp [optCode]
        · rw [Function.update_of_ne (by intro h; exact hv (Fin.ext (by omega))),
            Function.update_of_ne hv, hy₁far _ (by omega)]
          exact hx.stored v
      · intro t
        rw [hYm, hzm, Function.update_of_ne (by omega), hy₁m,
          show Tb + n + (i + 1) + (t : ℕ) = Tb + n + i + (t.succ : ℕ) by simp; omega]
        exact swap_order g k x.mem (Tb + n + i) (fun t => by simpa using hx.order t) t.succ
    -- the law of the value set
    have hbit : ExecRandLaw w bitCode z (fun z' => ∃ b : Bool, z' = z.set res b.toNat) 3 1 F
        ((stepWith (forced φ) τ (g k)).map fun b => (k'.val, b)) := by
      rcases hfo : forced φ τ (g k) with _ | b
      · rw [hfo] at hzr
        have hc : (Cond.eq res two).Holds z := by simp [Cond.holds_eq, hzr, hfz.two_eq, optCode]
        have hr := ExecRandLaw.rand (w := w) (B := .standard) (dst := res) (src := one) (x := z)
          (f := F) (P := fun z' => ∃ b : Bool, z' = z.set res b.toNat)
          (by rw [hfz.one_eq]; exact hw.of_le (by omega)) (fun k₂ => ⟨decide (k₂.val = 1), by
            have h2 : k₂.val < 2 := by have := k₂.isLt; have h1 := hfz.one_eq; omega
            congr 1
            rcases (show k₂.val = 0 ∨ k₂.val = 1 by omega) with h | h <;> simp [h]⟩)
        refine ((ExecRandLaw.branch_pos (neg := ram[ res ← res ]) hc hr).congr_law ?_).mono
          (fun _ h => h) (by omega) le_rfl
        rw [stepWith_of_eq_none hfo, uniform_map_val_congr hfz.one_eq
          (fun v => F (z.set res v)), ← uniform_two_map_bit, PMF.map_comp]
        congr 1
        funext k₂
        simp +decide [F, hjz]
      · rw [hfo] at hzr
        have hc : ¬(Cond.eq res two).Holds z := by
          cases b <;> simp [Cond.holds_eq, hzr, hfz.two_eq, optCode]
        have hcp := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := res) (x := z)
        rw [hzr] at hcp
        refine ((ExecRandLaw.branch_neg (pos := ram[ res ← rand one ]) hc
          (ExecRandLaw.of_execWithin (f := F) hcp ⟨b, by simp [optCode]⟩)).congr_law ?_).mono
          (fun _ h => h) le_rfl (Nat.zero_le _)
        rw [stepWith_of_eq_some hfo, PMF.pure_map]
        simp +decide [F, hjz, optCode]
    have hall := ExecRandLaw.seq_det hswap (ExecRandLaw.seq_det hz
      (ExecRandLaw.seq_det_right hbit fun z' ⟨b, hz'⟩ => hz' ▸ hstore b))
    refine (hall.congr_law ?_).mono (fun _ h => h) (by omega) le_rfl
    simp only [κ, Data.set_regs, Function.update_self, hk, ↓reduceDIte]
    rfl
  -- the draw
  have hrand := ExecRandLaw.rand (w := w) (B := .standard) (dst := jReg) (src := jReg) (x := x₂)
    (f := fun y => y.regs jReg) (P := fun y => ∃ k : Fin (x₂.regs jReg + 1), y = x₂.set jReg k.val)
    (by rw [hx₂j]; exact hw.of_le (by omega)) fun k => ⟨k, rfl⟩
  have hall := ExecRandLaw.seq_det h₁ (ExecRandLaw.seq_det h₂ (ExecRandLaw.seq hrand hrest))
  refine (hall.congr_law ?_).mono (fun _ h => h) (by omega) le_rfl
  simp only [Data.set_regs, Function.update_self]
  rw [uniform_map_val_congr hx₂j (fun v => v), PMF.bind_map]
  congr 1
  funext p
  simp only [Function.comp_apply, κ, p.isLt, ↓reduceDIte]

/-- **The steps of a round** from step `i`, with the unprocessed variables `g 0, …, g (d - 1)`,
have the law of `roundOn (forced φ) g τ`, take `d (28 E + 33) + 2` instructions and `2 d` `rand`
calls, and leave every variable set. -/
theorem roundLoop_law {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} (hw : Fits w (Tb + 2 * n))
    (hT : 1 ≤ Tb) :
    ∀ (d i : ℕ) (τ : Fin n → Option Bool) (g : Fin d → Fin n) (x : Data 32),
      LoopState φ C Tb M i τ g x → i + d = n →
      ExecRandLaw w roundLoop x (fun y => RoundFrame φ C Tb M y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1)
        (d * (28 * (encodeClauses φ).length + 33) + 2) (2 * d)
        (fun y => partialAssignmentAt y.mem Tb n) (roundOn (forced φ) g τ)
  | 0, i, τ, g, x, hx, hd => by
    have hc : ¬(Cond.lt iReg nReg).Holds x := by
      simp [Cond.holds_lt, hx.frame.nReg_eq, hx.i_eq]; omega
    have hpost : RoundFrame φ C Tb M x ∧ ∀ v < n, x.mem (Tb + v) ≤ 1 := by
      refine ⟨hx.frame, fun v hv => ?_⟩
      obtain ⟨b, hb⟩ : ∃ b, τ ⟨v, hv⟩ = some b := by
        rcases h : τ ⟨v, hv⟩ with _ | b
        · obtain ⟨t, -⟩ := hx.cover _ h
          exact t.elim0
        · exact ⟨b, rfl⟩
      have h := hx.stored ⟨v, hv⟩
      simp only [hb, optCode] at h
      rw [h]
      cases b <;> decide
    have h := ExecRandLaw.loop_exit (w := w) (body := roundBody)
      (P := fun y => RoundFrame φ C Tb M y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1)
      (f := fun y => partialAssignmentAt y.mem Tb n) hc hpost
    rw [partialAssignmentAt_eq hx.stored, ← roundOn_zero (forced φ) g τ] at h
    exact h.mono (fun _ h => h) (by omega) le_rfl
  | m + 1, i, τ, g, x, hx, hd => by
    have hc : (Cond.lt iReg nReg).Holds x := by
      simp [Cond.holds_lt, hx.frame.nReg_eq, hx.i_eq]; omega
    let κ : ℕ × Bool → PMF (Fin n → Option Bool) := fun q =>
      if hq : q.1 < m + 1 then
        roundOn (forced φ) (fun t : Fin m => g (Equiv.swap 0 ⟨q.1, hq⟩ t.succ))
          (Function.update τ (g ⟨q.1, hq⟩) (some q.2))
      else PMF.pure τ
    have h := ExecRandLaw.loop_iter (κ := κ) hc (roundBody_law hw hT hx hd)
      fun y ⟨p, b, hj, hr, hy⟩ => by
        have hobs : (y.regs jReg - i, decide (y.regs res = 1)) = (p.val, b) := by
          rw [hj, hr]
          cases b <;> simp
        rw [hobs]
        simp only [κ, p.isLt, ↓reduceDIte]
        exact roundLoop_law hw hT m (i + 1) _ _ y hy (by omega)
    rw [roundOn_succ]
    have hT' := Nat.add_mul m 1 (28 * (encodeClauses φ).length + 33)
    refine (h.congr_law ?_).mono (fun _ h => h) (by omega) (by omega)
    rw [PMF.bind_bind]
    congr 1
    funext p
    rw [PMF.bind_map]
    congr 1
    funext b
    simp only [Function.comp_apply, κ, p.isLt, ↓reduceDIte]

/-! ### The round -/

/-- **The body of a round**: store the empty partial assignment and the array `P[i] = i`, then
process the variables in a lazily drawn uniform order. The clauses are read from `[cBeg, cEnd)`,
the partial assignment is stored from `tBase` and the order array from `pBase`, and `n` is read
from `nReg`. -/
def roundCore : Code .standard 32 := ram[ iReg ← zero; ⟪initLoop⟫; iReg ← zero; ⟪roundLoop⟫ ]

/-- The instruction bound of a round body on `n` variables and a clause encoding of length
`E`. -/
def roundCoreTime (n E : ℕ) : ℕ := n * (28 * E + 40) + 6

/-- **The body of a round** has the law of `Cslib.Complexity.PPZ.round`, keeps the frame, and
leaves every variable set. -/
theorem roundCore_law {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} (hw : Fits w (Tb + 2 * n))
    (hT : 1 ≤ Tb) {x : Data 32} (hx : RoundFrame φ C Tb M x) :
    ExecRandLaw w roundCore x (fun y => RoundFrame φ C Tb M y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1)
      (roundCoreTime n (encodeClauses φ).length) (2 * n)
      (fun y => partialAssignmentAt y.mem Tb n) (round φ) := by
  have h₀ := ExecWithin.copy (B := .standard) (w := w) (d := iReg) (s := zero) (x := x)
  rw [hx.zero_eq] at h₀
  obtain ⟨y, hy, hfy, hyv⟩ := initLoop_spec hw n (x.set iReg 0) (hx.set (by decide) 0)
    (by simp) (by simp)
  have h₁ := ExecWithin.copy (B := .standard) (w := w) (d := iReg) (s := zero) (x := y)
  rw [hfy.zero_eq] at h₁
  have hst : LoopState φ C Tb M 0 (fun _ => none) (id : Fin n → Fin n) (y.set iReg 0) :=
    { frame := hfy.set (by decide) 0
      i_eq := by simp
      stored := fun v => (hyv v v.isLt).1
      order := fun t => by simpa using (hyv t t.isLt).2
      cover := fun v _ => ⟨v, rfl⟩ }
  have hloop := roundLoop_law hw hT n 0 _ _ _ hst (by omega)
  rw [← roundWith_eq_roundOn] at hloop
  exact (ExecRandLaw.seq_det h₀ (ExecRandLaw.seq_det hy (ExecRandLaw.seq_det h₁ hloop))).mono
    (fun _ h => h) (by simp only [roundCoreTime]; ring_nf; omega) le_rfl

/-! ### The satisfaction check -/

/-- The registers of Schöning's programs (`Cslib.Algorithms.WordRAM.Schoening.Reg`) inside the
register file of PPZ: `zero`, `one` and `cBeg` are shared, Schöning's assignment address `aBase`
and `nReg` are `tBase` and `nReg`, Schöning's scratch registers are PPZ's scan scratch, and the
counter registers `bBase`, `bLen` and `flag` of the amplified algorithm are the last three
registers. -/
def embed (i : Fin 24) : Fin 32 :=
  if i.val < 3 then ⟨i.val, by omega⟩ else if i.val < 21 then ⟨i.val + 1, by omega⟩
  else ⟨i.val + 8, by omega⟩

theorem embed_injective : Function.Injective embed := by
  intro a b h
  simp only [embed] at h
  split_ifs at h <;> simp only [Fin.mk.injEq] at h <;> exact Fin.ext (by omega)

/-- **The satisfaction check**: Schöning's scan of the clauses against the assignment stored at
`tBase`, then `out = 1` exactly when no clause is falsified. -/
def roundCheck : Code .standard 32 :=
  ram[ ⟪Schoening.scan.rename embed⟫; out ← one - sFound ]

/-- **The satisfaction check** on a total assignment stored at `Tb` sets `out` to whether it
satisfies `φ`, within `12 E + 5` instructions, and keeps the memory and the frame. -/
theorem roundCheck_exec {φ : CNF (Fin n)} {C Tb w : ℕ} {M : ℕ → ℕ} (hw : Fits w (Tb + 2 * n))
    (hT : 1 ≤ Tb) {x : Data 32} (hx : RoundFrame φ C Tb M x)
    (hbits : ∀ v < n, x.mem (Tb + v) ≤ 1) :
    ∃ y, ExecWithin w roundCheck x y (12 * (encodeClauses φ).length + 5) ∧ y.mem = x.mem ∧
      RoundFrame φ C Tb M y ∧
      y.regs out = (if φ.eval (assignmentAt x.mem Tb n) then 1 else 0) := by
  set σ := assignmentAt x.mem Tb n
  have hσ : AssignAt x.mem Tb σ := assignAt_assignmentAt hbits
  obtain ⟨y₀, hy₀, hm₀, hr₀⟩ := Schoening.scan_spec (w := w) σ φ (x.comap embed)
    hx.zero_eq hx.one_eq (by simpa [embed] using hx.cBeg_eq ▸ hx.clauses)
    (by simp only [Data.comap_regs]; rw [show embed Schoening.Reg.cBeg = cBeg by decide,
      show embed Schoening.Reg.aBase = tBase by decide, hx.cBeg_eq, hx.tBase_eq]; exact hx.span)
    (by simp only [Data.comap_regs]; rw [show embed Schoening.Reg.aBase = tBase by decide,
      hx.tBase_eq]; exact hσ)
    (by simp only [Data.comap_regs]; rw [show embed Schoening.Reg.aBase = tBase by decide,
      hx.tBase_eq]; exact hw)
    (by simp only [Data.comap_regs]; rw [show embed Schoening.Reg.aBase = tBase by decide,
      hx.tBase_eq]; omega)
  have hrun := ExecWithin.rename embed_injective hy₀
  set y₁ := y₀.extend embed x with hy₁
  have hfnd : y₁.regs sFound = if φ.eval σ then 0 else 1 := by
    have h : y₁.regs sFound = y₀.regs Schoening.Reg.found :=
      embed_injective.extend_apply y₀.regs x.regs Schoening.Reg.found
    rw [h]
    unfold ScanResult at hr₀
    rcases hfu : Cslib.Complexity.Schoening.firstUnsat φ σ with _ | c
    · simp only [hfu] at hr₀
      rw [hr₀]
      simp [(firstUnsat_eq_none_iff _ _).mp hfu]
    · simp only [hfu] at hr₀
      have : φ.eval σ = false := by
        rcases h : φ.eval σ
        · rfl
        · rw [← firstUnsat_eq_none_iff] at h
          rw [h] at hfu
          cases hfu
      rw [hr₀.1, this]
      rfl
  have hm₁ : y₁.mem = x.mem := hm₀
  have hf₁ : RoundFrame φ C Tb M y₁ := hx.of_execWithin (by decide) hrun fun a _ => by rw [hm₁]
  have hfo : Fits w (1 - y₁.regs sFound) := hw.of_le (by omega)
  have hout := ExecWithin.bin (w := w) (f := .sub) (d := out) (i := one) (j := sFound) (x := y₁)
    (by rw [hf₁.one_eq]; exact hfo)
  refine ⟨_, hrun.seq hout, by simpa using hm₁, hf₁.set (by decide) _, ?_⟩
  simp only [Data.set_regs, Function.update_self, BinOp.eval, hf₁.one_eq, hfnd]
  split_ifs <;> rfl

/-! ### The program -/

/-- Set up the registers of a round on the input `encode φ`: the clauses start at address `2`, the
partial assignment is stored just after the input, and the order array just after it. -/
def roundSetup : Code .standard 32 := ram[
  one ← #1; two ← #2; val ← *zero; tBase ← val + one; cEnd ← tBase; nReg ← *one;
  cBeg ← one + one; pBase ← tBase + nReg ]

/-- **One round of PPZ** on the input `encode φ`, as a structured program. -/
def roundCode : Code .standard 32 := ram[ ⟪roundSetup⟫; ⟪roundCore⟫; ⟪roundCheck⟫ ]

/-- **One round of PPZ** on the input `encode φ`, halting with `out`. -/
def roundProgram : Program .standard 32 := roundCode.program out

/-- The instruction bound of a round on `n` variables and an input of length `L`. -/
def roundTime (n L : ℕ) : ℕ := n * (28 * L + 40) + 12 * L + 19

/-- The partial assignment left by a halting run: read from address `base`. -/
def cfgPartial {r : ℕ} (base n : ℕ) : RandCfg r → (Fin n → Option Bool)
  | .halted _ d => partialAssignmentAt d.mem base n
  | _ => fun _ => none

/-- The data after the setup of a round on the input `encode φ`. -/
def roundSetupData (φ : CNF (Fin n)) : Data 32 :=
  (((((((((Data.init (encode φ)).set one 1).set two 2).set val (encode φ).length).set tBase
    ((encode φ).length + 1)).set cEnd ((encode φ).length + 1)).set nReg n).set cBeg 2).set pBase
    ((encode φ).length + 1 + n))

/-- The setup establishes the frame of a round on the input `encode φ`. -/
theorem roundSetup_exec (φ : CNF (Fin n)) {w : ℕ} (hw : Fits w ((encode φ).length + 2 * n + 1)) :
    ExecWithin w roundSetup (Data.init (encode φ)) (roundSetupData φ) 8 ∧
      RoundFrame φ 2 ((encode φ).length + 1) (roundSetupData φ).mem (roundSetupData φ) := by
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w 2 := hw.of_le (by simp [encode]; omega)
  have hf3 : Fits w ((encode φ).length + 1) := hw.of_le (by omega)
  have hf4 : Fits w ((encode φ).length + 1 + n) := hw.of_le (by omega)
  have hm0 : (Data.init (encode φ) : Data 32).mem 0 = (encode φ).length := rfl
  have hm1 : (Data.init (encode φ) : Data 32).mem 1 = n := rfl
  refine ⟨?run, ?frame⟩
  case run =>
    ram_eval [roundSetup, roundSetupData, Data.init_regs, hm0, hm1, hf1, hf2, hf3, hf4]
  case frame =>
    refine ⟨by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData], ?_, ?_, fun _ _ => rfl⟩
    · intro i
      change (Data.init (encode φ) : Data 32).mem (2 + i.val) = (encodeClauses φ)[i.val]
      rw [show 2 + i.val = (1 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, Nat.add_comm 1 i.val]
    · simp [length_encode]; omega

/-- **One round of PPZ on the randomized word RAM.** On the input `encode φ` of length `L`, at any
word size `w` with `L + 2 n + 1 < 2 ^ w`, the program

* halts on every path within `roundTime n L = n (28 L + 40) + 12 L + 19` instructions;
* makes at most `2 n` `rand` calls;
* outputs `1` exactly when the assignment it leaves at address `L + 1` satisfies `φ`, and that
  assignment is total: every word is `0` or `1`;
* leaves a partial assignment whose law is exactly `Cslib.Complexity.PPZ.round φ`. -/
theorem roundProgram_spec (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((encode φ).length + 2 * n + 1)) :
    RandHaltsWithin w roundProgram (.init (encode φ)) (roundTime n (encode φ).length) ∧
    RandCallsBounded w roundProgram (.init (encode φ)) (roundTime n (encode φ).length) (2 * n) ∧
    (∀ cfg ∈ (runRand w roundProgram (roundTime n (encode φ).length)
        (.running (.init (encode φ)))).support,
      ∃ d : Data 32, cfg = .halted
        (if φ.eval (assignmentAt d.mem ((encode φ).length + 1) n) then 1 else 0) d ∧
        ∀ v < n, d.mem ((encode φ).length + 1 + v) ≤ 1) ∧
    (evalRand w roundProgram (roundTime n (encode φ).length) (.init (encode φ))).map
      (cfgPartial ((encode φ).length + 1) n) = round φ := by
  set Tb := (encode φ).length + 1
  obtain ⟨hy, hfr⟩ := roundSetup_exec φ hw
  have hT : 1 ≤ Tb := by omega
  have hw' : Fits w (Tb + 2 * n) := hw.of_le (by omega)
  have hcore := ExecRandLaw.seq_det hy (ExecRandLaw.seq_det_right (roundCore_law hw' hT hfr)
    (Q := fun y => (RoundFrame φ 2 Tb (roundSetupData φ).mem y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1) ∧
      y.regs out = if φ.eval (assignmentAt y.mem Tb n) then 1 else 0)
    fun y ⟨hfy, hby⟩ => by
      obtain ⟨z, hz, hzm, hfz, hzo⟩ := roundCheck_exec hw' hT hfy hby
      exact ⟨z, hz, ⟨⟨hfz, by rw [hzm]; exact hby⟩, by rw [hzm]; exact hzo⟩, by simp [hzm]⟩)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hcore.program out (T' := roundTime n (encode φ).length)
    (by
      simp only [roundCoreTime, roundTime, length_encode]
      have := Nat.mul_le_mul_left n (show 28 * (encodeClauses φ).length + 40 ≤
        28 * ((encodeClauses φ).length + 1) + 40 by omega)
      omega)
    (cfgPartial Tb n) fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, ⟨-, hb⟩, hd⟩ := hpost cfg hcfg
  exact ⟨d, by rw [hd], hb⟩

end Cslib.Algorithms.WordRAM.PPZ
