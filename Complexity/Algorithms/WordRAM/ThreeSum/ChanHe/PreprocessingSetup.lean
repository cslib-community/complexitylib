/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLayout
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingReserve
import Complexity.Computability.WordRAM.Call

/-!
# Internal initialization proof for native preprocessing

The controller saves the computed frontend metadata, builds the shared prime bitmap, delivers
the traversal arguments and reserves space for the forest. These private stage contracts keep
the computed metadata and exact instruction costs together; catalogue and visitor initialization
compose them.
The native ABI, layout and composition proofs are original.
-/

-- Proof-only companion; catalogue and visitor initialization use `import all`.
set_option linter.privateModule false

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Exact computed metadata retained outside the root program's register bank. -/
private structure Saved (κ n : ℕ) (x : Data 128) : Prop where
  /-- Descriptor table and count produced by the frontend. -/
  base : x.regs descriptors = (Frontend.layout κ n).descriptors
  count : x.regs roots = (Frontend.layout κ n).count
  /-- Exact numeric parameter outputs. -/
  fuel : x.regs levels = Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  magnitude : x.regs inputMagnitude = (n + 2) ^ κ
  limit : x.regs candidateLimit = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  digits : x.regs labels = (Frontend.layout κ n).digits
  length : x.regs packedLength =
    8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2
  endpoint : x.regs firstFree = (Frontend.layout κ n).endpoint
  /-- Actual index and small constants. -/
  index : x.regs current = 0
  stride : x.regs stride = 6
  one : x.regs one = 1
  zero : x.regs zero = 0
  four : x.regs four = 4

/-- Programs restricted to lower registers retain all computed outer metadata. -/
private theorem Saved.congr {κ n : ℕ} {x y : Data 128} (h : Saved κ n x)
    (hr : ∀ i : Fin 128, 109 ≤ i.val → (i.val ≤ 120 ∨ i.val = 126) →
      y.regs i = x.regs i) : Saved κ n y := by
  cases h
  constructor <;> rw [hr _ (by decide) (by decide)] <;> assumption

/-- Saving computed scalars and initializing the outer constants changes no memory. -/
private theorem snapshot_exec {κ n w : ℕ} (x : Data 128)
    (hp : Parameters.Output n ((n + 2) ^ κ) (x.comap Frontend.parameterRegisters))
    (hb : x.regs Frontend.descriptorBase = (Frontend.layout κ n).descriptors)
    (hc : x.regs Frontend.descriptorCount = (Frontend.layout κ n).count)
    (he : x.regs Frontend.heapEnd = (Frontend.layout κ n).endpoint)
    (h6 : Fits w 6) : ∃ y, Exec w snapshot x y 13 ∧ Saved κ n y ∧ y.mem = x.mem := by
  let l := Frontend.layout κ n
  let y := x |>.set descriptors l.descriptors |>.set roots l.count
    |>.set levels (Cslib.Algorithms.ThreeSum.ChanHe.fuel n)
    |>.set inputMagnitude ((n + 2) ^ κ)
    |>.set candidateLimit (Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ))
    |>.set labels l.digits
    |>.set packedLength (8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) ^ 2)
    |>.set firstFree l.endpoint |>.set current 0 |>.set stride 6
    |>.set one 1 |>.set zero 0 |>.set four 4
  have hf := hp.fuel
  have hU := hp.magnitude
  have hm := hp.primeBound
  have hΛ := hp.digits
  have hN := hp.packedLen
  simp only [Data.comap_regs] at hf hU hm hΛ hN
  have h1 : Fits w 1 := h6.of_le (by decide)
  have h4 : Fits w 4 := h6.of_le (by decide)
  refine ⟨y, ?_, ?_, rfl⟩
  · ram_eval [snapshot, y, l, hb, hc, he, hf, hU, hm, hΛ, hN, h1, h4, h6,
      Frontend.layout, descriptors, roots, levels, inputMagnitude, candidateLimit,
      labels, packedLength, firstFree, current, stride, one, zero, four]
  · constructor <;> simp +decide [y, l, descriptors, roots, levels, inputMagnitude,
      candidateLimit, labels, packedLength, firstFree, current, stride, one, zero, four]

/-- Compute the actual shared bitmap from the already computed frontend and numeric parameters. -/
private theorem primes_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hfit : Fits w ((Frontend.layout κ n).endpoint +
      Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) + 4)) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let base := (Frontend.layout κ n).endpoint
    ∃ y, ExecWithin w (.seq preparePrimes (PrimeTable.program.rename primeRegisters)) x y
        (2 + ((m + 1) * (7 * m + 15) + 8)) ∧
      Saved κ n y ∧ y.mem = PrimeTable.memory x.mem base (m + 1) ∧
      y.regs (primeRegisters PrimeTable.count) = (Nat.primesLE m).card ∧
      (∀ q ≤ m, y.mem (base + q) = if q.Prime then 1 else 0) ∧
      ∀ p < base, y.mem p = x.mem p := by
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  let base := (Frontend.layout κ n).endpoint
  let p := (x.set (primeRegisters PrimeTable.limit) m).set (primeRegisters PrimeTable.base) base
  have hp : Exec w preparePrimes x p 2 := by
    ram_eval [preparePrimes, p, hs.limit, hs.endpoint, m, base]
  have hpi : Function.Injective primeRegisters := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 128 => k.val) hij)
  obtain ⟨y, hz, ⟨hmem, hcount, _, _⟩, _⟩ := ExecWithin.rename_post hpi
    (PrimeTable.exec (p.comap primeRegisters)
    (hfit.of_le (by change m + 3 ≤ base + m + 4; omega))
    (hfit.of_le (by change base + (m + 1) ≤ base + m + 4; omega)))
  have he : ExecWithin w (.seq preparePrimes (PrimeTable.program.rename primeRegisters)) x y
      (2 + ((m + 1) * (7 * m + 15) + 8)) := by
    simpa +decide [p, Data.comap, primeRegisters, PrimeTable.limit, m] using
      hp.within.seq hz
  have hmemory : y.mem = PrimeTable.memory x.mem base (m + 1) := by
    simpa +decide [p, Data.comap, primeRegisters, PrimeTable.limit,
      PrimeTable.base] using hmem
  refine ⟨y, he, hs.congr (fun i hi _ => he.regs_eq ?_), hmemory, ?_, ?_, ?_⟩
  · have hh : ∀ i : Fin 128, 109 ≤ i.val →
        (Code.seq preparePrimes (PrimeTable.program.rename primeRegisters)).Preserves i := by decide
    exact hh i hi
  · simpa +decide [p, Data.comap, primeRegisters, PrimeTable.limit] using hcount
  · intro q hq
    change y.mem (base + q) = if q.Prime then 1 else 0
    change q ≤ m at hq
    rw [hmemory]
    simp only [PrimeTable.memory, show base ≤ base + q ∧ base + q < base + (m + 1) by omega,
      and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro q hq
    rw [hmemory]
    simp only [PrimeTable.memory, show ¬(base ≤ q ∧ q < base + (m + 1)) by omega, ↓reduceIte]

/-- Execute all shared traversal arguments, constants and explicit-stack reservations. -/
private theorem setupTraversal_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hc : x.regs (primeRegisters PrimeTable.count) =
      (Nat.primesLE (Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ))).card)
    (hfit : Fits w ((arena κ n x.mem).floor + (arena κ n x.mem).U +
      (arena κ n x.mem).N + (arena κ n x.mem).fuel + 16)) :
    ∃ y, Exec w setupTraversal x y 19 ∧ Saved κ n y ∧
      (arena κ n x.mem).Controls y ∧ y.regs Traversal.outputCount = 0 ∧
      y.regs power = 1 ∧
      y.regs remaining = Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1 ∧
      y.regs scalar = 3 ∧ y.mem = x.mem := by
  let a := arena κ n x.mem
  let F := a.fuel
  let y := x |>.set Traversal.limit a.m |>.set Traversal.digits a.Λ
    |>.set Traversal.magnitude a.U |>.set Traversal.groups a.N
    |>.set Traversal.bitmap a.primes |>.set Traversal.primeCount (Nat.primesLE a.m).card
    |>.set Traversal.stackBase (a.primes + a.m)
    |>.set Traversal.stackBase a.stack
    |>.set Traversal.stackCapacity (F + F)
    |>.set Traversal.stackCapacity (F + F + 1) |>.set scalar 7
    |>.set Traversal.stackCapacity a.capacity |>.set Traversal.outputs a.table
    |>.set Traversal.outputCount 0 |>.set Traversal.zero 0 |>.set Traversal.one 1
    |>.set power 1 |>.set remaining (F + 1) |>.set scalar 3
  have hfloor : a.primes + a.m + 1 + 7 * (2 * F + 1) ≤ a.floor := by
    dsimp only [a, F, arena]
    omega
  have fit (v : ℕ) (hv : v ≤ a.floor + a.U + a.N + F + 16) : Fits w v := hfit.of_le hv
  have hU : Fits w (2 * (n + 2) ^ κ) := fit _ (by change a.U ≤ _; omega)
  have hN : Fits w (2 * a.m ^ 2) := fit _ (by change a.N ≤ _; omega)
  have hstack₀ : Fits w (a.primes + a.m) := fit _ (by omega)
  have hstack : Fits w a.stack := fit _ (by change a.primes + a.m + 1 ≤ _; omega)
  have hF₀ : Fits w (F + F) := fit _ (by omega)
  have hF₁ : Fits w (F + F + 1) := fit _ (by omega)
  have hcap : Fits w a.capacity := fit _ (by change 7 * (2 * F + 1) ≤ _; omega)
  have htable : Fits w a.table := fit _ (by change a.primes + a.m + 1 + 7 * (2 * F + 1) ≤ _; omega)
  have hnext : Fits w (F + 1) := fit _ (by omega)
  have h1 : Fits w 1 := fit _ (by omega)
  have h3 : Fits w 3 := fit _ (by omega)
  have h7 : Fits w 7 := fit _ (by omega)
  have hdiv : 8 * a.m ^ 2 / 4 = 2 * a.m ^ 2 := by omega
  simp only [a, F, arena, ← two_mul, Nat.mul_comm, Nat.add_assoc]
    at hU hN hstack₀ hstack hF₀ hF₁ hcap htable hnext hdiv
  dsimp only [primeRegisters, PrimeTable.count] at hc
  have he : Exec w setupTraversal x y 19 := by
    ram_eval [setupTraversal, y, a, F, arena, hs.limit, hs.digits, hs.magnitude,
      hs.length, hs.endpoint, hs.fuel, hs.one, hs.four, hc, hdiv, hU, hN,
      hstack₀, hstack, hF₀, hF₁, hcap, htable, hnext, h1, h3, h7,
      Traversal.limit, Traversal.digits, Traversal.magnitude, Traversal.groups,
      Traversal.bitmap, Traversal.primeCount, Traversal.stackBase, Traversal.stackCapacity,
      Traversal.outputs, Traversal.outputCount, Traversal.zero, Traversal.one,
      candidateLimit, labels, inputMagnitude, packedLength, four, firstFree, levels,
      one, power, remaining, scalar, primeRegisters, PrimeTable.count,
      ← two_mul, Nat.mul_comm, Nat.add_assoc]
  refine ⟨y, he, hs.congr (fun i hi hj => he.within.regs_eq ?_), ?_, ?_, ?_, ?_, ?_, rfl⟩
  · have hh : ∀ i : Fin 128, 109 ≤ i.val → i ≠ power → i ≠ remaining → i ≠ scalar →
        setupTraversal.Preserves i := by decide
    exact hh i hi (by intro hh; subst i; norm_num [power] at hj)
      (by intro hh; subst i; norm_num [remaining] at hj)
      (by intro hh; subst i; norm_num [scalar] at hj)
  · constructor <;> simp +decide [y, a, F, arena, Traversal.limit, Traversal.digits,
      Traversal.magnitude, Traversal.groups, Traversal.bitmap, Traversal.primeCount,
      Traversal.outputs, Traversal.stackBase, Traversal.stackCapacity,
      Traversal.zero, Traversal.one, scalar, remaining, power]
  all_goals simp +decide [y, F, a, arena, Traversal.outputCount,
    Traversal.one, Traversal.zero, Traversal.outputs, Traversal.stackCapacity,
    power, remaining, scalar]

/-- Compute all root reservations and the actual first fresh heap address by native code. -/
private theorem finish_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hc : (arena κ n x.mem).Controls x) (hcount : x.regs Traversal.outputCount = 0)
    (hp : x.regs power = 1)
    (hr : x.regs remaining = Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1)
    (hscalar : x.regs scalar = 3)
    (hpow : Fits w (3 ^ (Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1)))
    (hfloor : Fits w (arena κ n x.mem).floor) :
    ∃ y, ExecWithin w (.seq reserve finishLayout) x y
        (4 * (Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1) + 5) ∧
      Saved κ n y ∧ (arena κ n x.mem).Controls y ∧
      y.regs Traversal.outputCount = 0 ∧ y.regs Traversal.heap = (arena κ n x.mem).floor ∧
      y.regs outputCapacity = (arena κ n x.mem).outputCapacity ∧
      y.regs heapFloor = (arena κ n x.mem).floor ∧ y.mem = x.mem := by
  let a := arena κ n x.mem
  obtain ⟨p, he, hpower, _, hmem, hregs⟩ := reserve_exec x hp hr hs.zero hs.one hscalar hpow
  have ps : Saved κ n p := hs.congr (fun i hi hj => hregs i
    (by intro hh; subst i; norm_num [power] at hj)
    (by intro hh; subst i; norm_num [remaining] at hj))
  have pc : a.Controls p := hc.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hregs i (by intro hh; subst i; norm_num [power] at hi)
      (by intro hh; subst i; norm_num [remaining] at hi))
  have pcount : p.regs Traversal.outputCount = 0 :=
    (hregs _ (by decide) (by decide)).trans hcount
  let y := p |>.set outputCapacity a.outputCapacity |>.set Traversal.heap a.floor
    |>.set heapFloor a.floor
  have hcap : Fits w a.outputCapacity := hfloor.of_le (by dsimp only [a, arena]; omega)
  have hout := pc.2.2.2.2.2.2.1
  dsimp only [a, arena] at hcap hfloor hout
  have hz : Exec w finishLayout p y 3 := by
    ram_eval [finishLayout, y, a, arena, ps.count, hpower, hout, hcap, hfloor,
      outputCapacity, roots, power, Traversal.outputs, Traversal.heap, heapFloor]
  have ys : Saved κ n y := ps.congr (fun i hi hj => hz.within.regs_eq (by
    have hh : ∀ i : Fin 128, 109 ≤ i.val → (i.val ≤ 120 ∨ i.val = 126) →
        finishLayout.Preserves i := by decide
    exact hh i hi hj))
  have yc : a.Controls y := pc.congr (by
    intro i hi
    apply hz.within.regs_eq
    have hh : ∀ i : Fin 128, i.val ∈ [71, 72, 73, 74, 75, 76, 78, 80, 81, 82, 83] →
        finishLayout.Preserves i := by decide
    exact hh i hi)
  refine ⟨y, (he.seq hz.within).mono (by omega), ys, yc, ?_, ?_, ?_, ?_, hmem⟩
  · simpa +decide [y, outputCapacity, Traversal.heap, heapFloor,
      Traversal.outputCount] using pcount
  all_goals simp +decide [y, a, outputCapacity, Traversal.heap, heapFloor]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
