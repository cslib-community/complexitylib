/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.AKS.CongruenceLoop
public import Complexity.Algorithms.WordRAM.AKS.GcdTotient
public import Complexity.Algorithms.WordRAM.AKS.OrderSearch
public import Complexity.Algorithms.WordRAM.AKS.PerfectPower
public import Complexity.Algorithms.WordRAM.NatClog
public import Complexity.Algorithms.WordRAM.NatSqrt
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
public import Complexity.Foundations.NumberTheory.AKS.IntegerVariant
import Complexity.Foundations.NumberTheory.AKS.SmallR

/-!
# The AKS primality test on the word RAM

The AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] decides whether `n` is prime. This
program runs it on the word RAM, with the input `n` in memory cell `1` and the integer thresholds
`c = ⌈log₂ n⌉` and `L = c²` (`Cslib.AKS.PassesUpTo`):

0. if `n < 2`, answer `0`;
1. if `n` is a perfect power, answer `0`;
2. find the least `r ≥ 2` with `ord_r(n) > L`;
3. if `1 < gcd(a, n) < n` for some `a ≤ r`, answer `0`;
4. if `n ≤ r`, answer `1`;
5. answer `1` exactly when `(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for every
   `1 ≤ a ≤ ⌊√(φ(r) L)⌋`.

Each step is a subroutine run on the low registers. The search in step 2 stops by
`Cslib.AKS.exists_lt_orderOf`, at some `r ≤ 4 c⁵`, and the answer is correct by Theorem 4.1 of the
paper with integer thresholds (`Cslib.AKS.prime_iff_passesUpTo_numTestsNat`).

The word size must hold the numbers the steps compute; for an input of `s` bits, the width
`8 (s + 1)` suffices. The program then answers within `time s ≤ 4096 (s + 1)¹⁵` instructions
(`Cslib.Algorithms.WordRAM.AKS.time_le`). The dominant term is step 5: at most `2 s⁴` values of
`a`, each tested by `s` rounds of schoolbook multiplication of polynomials with `r ≤ 4 s⁵`
coefficients.
Theorem 5.1 of the paper bounds the bit complexity of the algorithm by `Õ(log^{21/2} n)`, using
fast multiplication of integers and polynomials.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.program`: the AKS algorithm.
* `Cslib.Algorithms.WordRAM.AKS.time`: its instruction bound on inputs of `s` bits.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.answers`: at a word size of at least `8 (size n + 1)`, the
  program answers whether `n` is prime within `time (size n)` instructions.
* `Cslib.Algorithms.WordRAM.AKS.decidesInTime`: its compiled program decides the primes.
* `Cslib.Algorithms.WordRAM.AKS.time_le`, `Cslib.Algorithms.WordRAM.AKS.polynomiallyBounded_time`:
  the instruction bound is at most `4096 (s + 1)¹⁵`, so it is polynomial.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS

open Cslib.WordRAM Cslib.AKS

/-! ### Registers -/

/-- Subroutines run on the low registers `0, …, k - 1`, below the registers of the top level. -/
def low {k : ℕ} (hk : k ≤ 29) : Fin k → Fin 36 := Fin.castLE (by omega)

theorem low_injective {k : ℕ} (hk : k ≤ 29) : (low hk).Injective := Fin.castLE_injective _

/-- The input `n`. -/
abbrev nv : Fin 36 := 29
/-- Constant one, which is also the address of the input. -/
abbrev one : Fin 36 := 30
/-- Constant two. -/
abbrev two : Fin 36 := 31
/-- The bound `L = ⌈log₂ n⌉²` on the order. -/
abbrev lv : Fin 36 := 32
/-- The modulus `r` of step 2. -/
abbrev rv : Fin 36 := 33
/-- Euler's totient `φ(r)`. -/
abbrev phv : Fin 36 := 34
/-- The answer. -/
abbrev ans : Fin 36 := 35

/-- The input of the perfect-power test. -/
abbrev ppN : Fin 36 := 0
/-- The answer of the perfect-power test. -/
abbrev ppFlag : Fin 36 := 11
/-- The argument of the binary logarithm. -/
abbrev logArg : Fin 36 := 0
/-- The binary logarithm. -/
abbrev logRes : Fin 36 := 1
/-- The number `n` of the search for `r`. -/
abbrev osN : Fin 36 := 0
/-- The bound `L` of the search for `r`. -/
abbrev osL : Fin 36 := 1
/-- The result `r` of the search. -/
abbrev osR : Fin 36 := 2
/-- The number `n` of step 3. -/
abbrev gtN : Fin 36 := 0
/-- The modulus `r` of step 3. -/
abbrev gtR : Fin 36 := 1
/-- The answer of step 3. -/
abbrev gtOk : Fin 36 := 4
/-- The totient computed in step 3. -/
abbrev gtPhi : Fin 36 := 5
/-- The argument of the square root. -/
abbrev sqArg : Fin 36 := 0
/-- The square root. -/
abbrev sqRoot : Fin 36 := 1
/-- The result block of step 5. -/
abbrev clR : Fin 36 := 0
/-- The base block of step 5. -/
abbrev clB : Fin 36 := 1
/-- The scratch block of step 5. -/
abbrev clT : Fin 36 := 2
/-- The number `r` of coefficients in step 5. -/
abbrev clRr : Fin 36 := 3
/-- The modulus `n` of step 5. -/
abbrev clNn : Fin 36 := 4
/-- The last tested value `A` of step 5. -/
abbrev clA : Fin 36 := 25
/-- The answer of step 5. -/
abbrev clOk : Fin 36 := 27

/-! ### The program -/

/-- Step 1, the perfect-power test. -/
def perfectPower : Code .standard 36 := PerfectPower.program.rename (low (by norm_num))

/-- The binary logarithm `⌈log₂ n⌉`. -/
def clog : Code .standard 36 := NatClog.program.rename (low (by norm_num))

/-- Step 2, the search for `r`. -/
def orderSearch : Code .standard 36 := OrderSearch.program.rename (low (by norm_num))

/-- Step 3, and the totient `φ(r)`. -/
def gcdTotient : Code .standard 36 := GcdTotient.program.rename (low (by norm_num))

/-- The integer square root. -/
def sqrt : Code .standard 36 := NatSqrt.program.rename (low (by norm_num))

/-- Step 5, the congruences. -/
def congruences : Code .standard 36 := CongruenceLoop.program.rename (low (by norm_num))

/-- Steps 4 and 5: answer `1` if `n ≤ r`, and otherwise test the congruence for
`1 ≤ a ≤ ⌊√(φ(r) L)⌋`, with the blocks at `0`, `r` and `2 r`. -/
def congruenceSteps : Code .standard 36 :=
  .branch (.lt rv nv)
    (.seq (ram[ sqArg ← phv * lv ]) (.seq sqrt
      (.seq (ram[ clA ← sqRoot; clR ← #0; clB ← rv; clT ← rv + rv; clRr ← rv; clNn ← nv ])
        (.seq congruences (ram[ ans ← clOk ])))))
    (ram[ ans ← #1 ])

/-- Steps 2 to 5, for an `n ≥ 2` that is not a perfect power. -/
def searchSteps : Code .standard 36 :=
  .seq (ram[ logArg ← nv ]) (.seq clog
    (.seq (ram[ lv ← logRes * logRes; osN ← nv; osL ← lv ]) (.seq orderSearch
    (.seq (ram[ rv ← osR; gtN ← nv; gtR ← rv ]) (.seq gcdTotient
    (.branch (.eq gtOk one) (.seq (ram[ phv ← gtPhi ]) congruenceSteps) (ram[ ans ← #0 ])))))))

/-- **The AKS algorithm.** Read `n`; answer `0` if `n < 2` or `n` is a perfect power, and
otherwise run steps 2 to 5. The answer is in `ans`. -/
def program : Code .standard 36 :=
  .seq (ram[ one ← #1; two ← #2; nv ← *one ])
    (.branch (.lt nv two) (ram[ ans ← #0 ])
      (.seq (ram[ ppN ← nv ]) (.seq perfectPower
        (.branch (.eq ppFlag one) (ram[ ans ← #0 ]) searchSteps))))

/-- The instruction bound of `program` on an input of `s` bits: the perfect-power test, the
logarithm, step 2 with `L ≤ s²` and `r ≤ 4 s⁵`, step 3, the square root, and step 5 with at most
`2 s⁴` tests. -/
def time (s : ℕ) : ℕ :=
  (s + 1) * (s * (6 * s + 13) + 6 * s + 22) + 9 * s + OrderSearch.time (s ^ 2) (4 * s ^ 5) +
    GcdTotient.time (4 * s ^ 5) + 10 * s ^ 4 +
    2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) + 70

/-- The instruction bound is a polynomial of degree `15`: `time s ≤ 4096 (s + 1)¹⁵`. -/
theorem time_le (s : ℕ) : time s ≤ 4096 * (s + 1) ^ 15 := by
  have h (k : ℕ) (hk : k ≤ 15) : s ^ k ≤ (s + 1) ^ 15 :=
    (Nat.pow_le_pow_left (Nat.le_succ s) k).trans (Nat.pow_le_pow_right (Nat.succ_pos s) hk)
  have h0 : 1 ≤ (s + 1) ^ 15 := Nat.one_le_pow _ _ (Nat.succ_pos s)
  have h1 : s ≤ (s + 1) ^ 15 := by simpa using h 1 (by norm_num)
  have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num); have h6 := h 6 (by norm_num); have h7 := h 7 (by norm_num)
  have h8 := h 8 (by norm_num); have h9 := h 9 (by norm_num); have h10 := h 10 (by norm_num)
  have h11 := h 11 (by norm_num); have h12 := h 12 (by norm_num)
  have h13 := h 13 (by norm_num); have h14 := h 14 (by norm_num); have h15 := h 15 le_rfl
  generalize (s + 1) ^ 15 = S at *
  unfold time OrderSearch.time GcdTotient.time PolyPow.mulTime
  ring_nf
  omega

/-- The instruction bound is polynomial in the number of bits. -/
theorem polynomiallyBounded_time : PolynomiallyBounded time :=
  PolynomiallyBounded.of_forall_le 4096 15 time_le

/-! ### Word sizes -/

/-- `s² ≤ 2^(s + 1)`. -/
private theorem sq_le_two_pow (s : ℕ) : s ^ 2 ≤ 2 ^ (s + 1) := by
  induction s with
  | zero => norm_num
  | succ k ih =>
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have h1 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    have h2 : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    have h3 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    omega

/-- Numbers up to `64 s¹⁰` fit the width `8 (s + 1)`, for `s ≥ 2`. -/
private theorem fits_poly {w s v : ℕ} (hs : 2 ≤ s) (hw : 8 * (s + 1) ≤ w)
    (hv : v ≤ 64 * s ^ 10) : Fits w v := by
  have h10 : s ^ 10 ≤ 2 ^ (5 * s + 5) := by
    calc s ^ 10 = (s ^ 2) ^ 5 := by ring
      _ ≤ (2 ^ (s + 1)) ^ 5 := Nat.pow_le_pow_left (sq_le_two_pow s) 5
      _ = 2 ^ (5 * s + 5) := by ring
  refine fits_iff.mpr (lt_of_le_of_lt hv ?_)
  calc 64 * s ^ 10 ≤ 2 ^ 6 * 2 ^ (5 * s + 5) := by norm_num; omega
    _ = 2 ^ (5 * s + 11) := by ring
    _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Numbers below `2^(2 s + 1)` fit the width `8 (s + 1)`. -/
private theorem fits_exp {w s v : ℕ} (hw : 8 * (s + 1) ≤ w) (hv : v < 2 ^ (2 * s + 1)) :
    Fits w v :=
  fits_iff.mpr (hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- A subroutine on the low registers preserves the registers of the top level. -/
private theorem preserves_low {k : ℕ} (hk : k ≤ 29) (c : Code .standard k) (j : Fin 36)
    (hj : 29 ≤ j.val) : (c.rename (low hk)).Preserves j :=
  Code.preserves_rename_of_forall_ne _ _ _ fun i h => by
    have := congrArg Fin.val h
    simp only [low, Fin.val_castLE] at this
    omega

/-! ### Correctness -/

/-- **Steps 4 and 5.** For `2 ≤ r ≤ 4 s⁵` and `L ≤ s²`, with `φ(r)` in `phv`, the answer is `1`
exactly when `n ≤ r` or the congruence holds for every `1 ≤ a ≤ ⌊√(φ(r) L)⌋`. -/
private theorem congruenceSteps_exec {w s : ℕ} (x : Data 36) {N R L : ℕ} (hn : x.regs nv = N)
    (hr : x.regs rv = R) (hl : x.regs lv = L) (hph : x.regs phv = Nat.totient R)
    (hsN : Nat.size N = s) (hs : 2 ≤ s) (hw : 8 * (s + 1) ≤ w) (hR : 2 ≤ R)
    (hRs : R ≤ 4 * s ^ 5) (hLs : L ≤ s ^ 2) :
    ∃ y, ExecWithin w congruenceSteps x y
      (2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) +
        10 * s ^ 4 + 22) ∧
      y.regs ans ≤ 1 ∧
      (y.regs ans = 1 ↔ N ≤ R ∨ ∀ a, 1 ≤ a → a ≤ Nat.sqrt (Nat.totient R * L) →
        Congruence N R a) := by
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  have h5 : s ^ 5 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h7 : s ^ 7 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  by_cases hRN : R < N
  swap
  · -- Step 4: `n ≤ r`.
    have hrun : ExecWithin (B := .standard) w (ram[ ans ← #1 ]) x (x.set ans 1) 1 := by
      ram_eval [fits_poly hs hw (by omega : 1 ≤ 64 * s ^ 10)]
    refine ⟨x.set ans 1, (ExecWithin.branch_neg (by simpa [Cond.holds_lt, hr, hn] using hRN)
      hrun).mono (by omega), ?_, ?_⟩
    · simp
    · simp only [Data.set_regs, Function.update_self, true_iff]
      exact Or.inl (by omega)
  -- The square root.
  set Φ := Nat.totient R
  have hΦR : Φ ≤ R := Nat.totient_le R
  have hΦL : Φ * L ≤ 4 * s ^ 7 := by
    calc Φ * L ≤ (4 * s ^ 5) * s ^ 2 := Nat.mul_le_mul (hΦR.trans hRs) hLs
      _ = 4 * s ^ 7 := by ring
  set A := Nat.sqrt (Φ * L)
  have hA : A ≤ 2 * s ^ 4 := by
    calc A ≤ Nat.sqrt ((2 * s ^ 4) ^ 2) := Nat.sqrt_le_sqrt (by
          calc Φ * L ≤ 4 * s ^ 7 := hΦL
            _ ≤ 4 * s ^ 8 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) (by omega))
            _ = (2 * s ^ 4) ^ 2 := by ring)
      _ = 2 * s ^ 4 := Nat.sqrt_eq' _
  have h4 : s ^ 4 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  let x₁ := x.set sqArg (Φ * L)
  have hrun₁ : ExecWithin (B := .standard) w (ram[ sqArg ← phv * lv ]) x x₁ 1 := by
    ram_eval [x₁, hph, hl, fits_poly hs hw (by omega : Φ * L ≤ 64 * s ^ 10)]
  obtain ⟨y₂, hrun₂, hroot, -, -, -⟩ := NatSqrt.exec_rename (low (by norm_num)) (low_injective _)
    x₁ (by
      have : x₁.regs (low (by norm_num) NatSqrt.arg) = Φ * L := by simp +decide [x₁, low]
      rw [this]
      exact fits_poly hs hw (by omega))
  have hx₁a : x₁.regs (low (by norm_num) NatSqrt.arg) = Φ * L := by simp +decide [x₁, low]
  rw [hx₁a] at hrun₂ hroot
  have hy₂ (j : Fin 36) (hj : 29 ≤ j.val) : y₂.regs j = x₁.regs j :=
    hrun₂.regs_eq (preserves_low _ _ j hj)
  have hy₂n : y₂.regs nv = N := by rw [hy₂ nv (by decide)]; simp +decide [x₁, hn]
  have hy₂r : y₂.regs rv = R := by rw [hy₂ rv (by decide)]; simp +decide [x₁, hr]
  -- The blocks.
  let x₃ := (((((y₂.set clA A).set clR 0).set clB R).set clT (R + R)).set clRr R).set clNn N
  have hrun₃ : ExecWithin (B := .standard) w
      (ram[ clA ← sqRoot; clR ← #0; clB ← rv; clT ← rv + rv; clRr ← rv; clNn ← nv ])
      y₂ x₃ 6 := by
    have hroot' : y₂.regs sqRoot = A := hroot
    ram_eval [x₃, hroot', hy₂r, hy₂n, fits_zero, fits_poly hs hw (by omega : R + R ≤ 64 * s ^ 10)]
  -- Step 5.
  have hxR : x₃.regs clR = 0 := by simp +decide [x₃]
  have hxB : x₃.regs clB = R := by simp +decide [x₃]
  have hxT : x₃.regs clT = R + R := by simp +decide [x₃]
  have hxr : x₃.regs clRr = R := by simp +decide [x₃]
  have hxn : x₃.regs clNn = N := by simp +decide [x₃]
  have hxA : x₃.regs clA = A := by simp +decide [x₃]
  obtain ⟨y₄, hrun₄, hok, hokiff, -⟩ := CongruenceLoop.exec (x₃.comap (low le_rfl))
    hxR hxB hxT hxr hxn hxA
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fits_poly hs hw (by omega)) (fits_poly hs hw (by omega)) (fits_poly hs hw (by omega))
    (fits_poly hs hw (by omega))
    (fits_exp hw (by
      have : (N + 1) * (N + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul hNs hNs
      have h2 : 2 ^ (2 * s + 1) = 2 ^ s * 2 ^ s * 2 := by ring
      rw [h2]
      nlinarith))
    (fits_poly hs hw (by omega))
  have hrun₄' := hrun₄.rename (low_injective (by norm_num : 29 ≤ 29))
  have hy₄ok : (y₄.extend (low (by norm_num : 29 ≤ 29)) x₃).regs clOk = y₄.regs CongruenceLoop.ok :=
    (low_injective _).extend_apply _ _ CongruenceLoop.ok
  -- The answer.
  let z := (y₄.extend (low (by norm_num : 29 ≤ 29)) x₃).set ans (y₄.regs CongruenceLoop.ok)
  have hrun₅ : ExecWithin (B := .standard) w (ram[ ans ← clOk ])
      (y₄.extend (low (by norm_num : 29 ≤ 29)) x₃) z 1 := by
    ram_eval [z, hy₄ok]
  refine ⟨z, (ExecWithin.branch_pos (by simpa [Cond.holds_lt, hr, hn] using hRN)
    (hrun₁.seq (hrun₂.seq (hrun₃.seq (hrun₄'.seq hrun₅))))).mono ?_, ?_, ?_⟩
  · have hmul : PolyPow.mulTime R ≤ PolyPow.mulTime (4 * s ^ 5) := by
      unfold PolyPow.mulTime; gcongr
    have hin : Nat.size N * (2 * PolyPow.mulTime R + 6) + 4 + 26 * R + 57 + 6 ≤
        s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67 := by
      rw [hsN]
      have := Nat.mul_le_mul_left s
        (show 2 * PolyPow.mulTime R + 6 ≤ 2 * PolyPow.mulTime (4 * s ^ 5) + 6 by omega)
      omega
    have := Nat.mul_le_mul hA hin
    unfold CongruenceLoop.time Congruence.time PolyPow.time
    omega
  · simpa [z] using hok
  · simp only [z, Data.set_regs, Function.update_self]
    rw [hokiff]
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · omega
      · exact h

/-- `n ≥ 2` has at least two bits. -/
private theorem two_le_size {N : ℕ} (hN : 2 ≤ N) : 2 ≤ Nat.size N := by
  by_contra h
  have := Nat.size_le.mp (by omega : Nat.size N ≤ 1)
  omega

/-- **Steps 2 to 5.** For `n ≥ 2` that is not a perfect power, at a word size of at least
`8 (size n + 1)`, the answer is `1` exactly when `n` is prime. -/
private theorem searchSteps_exec {w s : ℕ} (x : Data 36) {N : ℕ} (hn : x.regs nv = N)
    (h1 : x.regs one = 1) (hN : 2 ≤ N) (hpp : ¬ IsPerfectPower N) (hsN : Nat.size N = s)
    (hw : 8 * (s + 1) ≤ w) :
    ∃ y, ExecWithin w searchSteps x y
      (5 * s + OrderSearch.time (s ^ 2) (4 * s ^ 5) + GcdTotient.time (4 * s ^ 5) +
        (2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) +
          10 * s ^ 4 + 22) + 20) ∧
      y.regs ans ≤ 1 ∧ (y.regs ans = 1 ↔ N.Prime) := by
  have hs : 2 ≤ s := hsN ▸ two_le_size hN
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  obtain ⟨c, hcdef⟩ : ∃ c, Nat.clog 2 N = c := ⟨_, rfl⟩
  have hc : c ≤ s := hcdef ▸ Nat.clog_le_of_le_pow hNs.le
  have hcc : c * c ≤ s ^ 2 := by rw [sq]; exact Nat.mul_le_mul hc hc
  have h1s : s ≤ s ^ 2 := by nlinarith
  have h2s : s ^ 2 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5s : s ^ 5 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hF1 : Fits w 1 := fits_poly hs hw (by omega)
  have hF2 : Fits w 2 := fits_poly hs hw (by omega)
  have hFN : Fits w N := fits_exp hw (hNs.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hFN1 : Fits w (N + 1) :=
    fits_exp hw (lt_of_le_of_lt hNs (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  -- The logarithm `c = ⌈log₂ n⌉`.
  let x₁ := x.set logArg N
  have hrun₁ : ExecWithin (B := .standard) w (ram[ logArg ← nv ]) x x₁ 1 := by
    ram_eval [x₁, hn]
  have hx₁a : x₁.regs logArg = N := by simp [x₁]
  obtain ⟨y₂, hrun₂, hres, -, -, -⟩ := NatClog.exec_rename (low (k := 4) (by norm_num))
    (low_injective _) x₁ hF2 (by change Fits w (x₁.regs logArg + 1); rw [hx₁a]; exact hFN1)
    (by change Fits w (Nat.clog 2 (x₁.regs logArg) + 1); rw [hx₁a, hcdef]
        exact fits_poly hs hw (by omega))
  have hrun₂' : ExecWithin w clog x₁ y₂ (5 * c + 5) := by
    rw [← hcdef, ← hx₁a]; exact hrun₂
  have hres' : y₂.regs logRes = c := by rw [← hcdef, ← hx₁a]; exact hres
  have hy₂ (j : Fin 36) (hj : 29 ≤ j.val) : y₂.regs j = x₁.regs j :=
    hrun₂.regs_eq (preserves_low _ _ j hj)
  have hy₂n : y₂.regs nv = N := by rw [hy₂ nv (by decide)]; simp +decide [x₁, hn]
  have hy₂1 : y₂.regs one = 1 := by rw [hy₂ one (by decide)]; simp +decide [x₁, h1]
  -- Step 2: the search for `r`, with `L = c²`.
  let x₃ := ((y₂.set lv (c * c)).set osN N).set osL (c * c)
  have hrun₃ : ExecWithin (B := .standard) w (ram[ lv ← logRes * logRes; osN ← nv; osL ← lv ])
      y₂ x₃ 3 := by
    ram_eval [x₃, hres', hy₂n, fits_poly hs hw (by omega : c * c ≤ 64 * s ^ 10)]
  have hx₃n : x₃.regs osN = N := by simp +decide [x₃]
  have hx₃L : x₃.regs osL = c * c := by simp +decide [x₃]
  obtain ⟨r₀, hr₀2, hr₀s, hr₀ord⟩ := exists_lt_orderOf hN
  rw [hcdef] at hr₀s hr₀ord
  have hr₀s' : r₀ ≤ 4 * s ^ 5 := hr₀s.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hc 5))
  have hgood : OrderSearch.Good N (c * c) r₀ := (lt_orderOf_iff hr₀2).mp (by rwa [← sq])
  have hFr₀ : Fits w (r₀ * r₀) := fits_poly hs hw (by
    calc r₀ * r₀ ≤ (4 * s ^ 5) * (4 * s ^ 5) := Nat.mul_le_mul hr₀s' hr₀s'
      _ = 16 * s ^ 10 := by ring
      _ ≤ 64 * s ^ 10 := by omega)
  obtain ⟨y₄, hrun₄, hR2, hRr₀, hRgood, -, -⟩ := OrderSearch.exec
    (x₃.comap (low (k := 13) (by norm_num))) (N := N) (L₀ := c * c) (by exact hx₃n)
    (by exact hx₃L) hr₀2 hgood hFN hFr₀ (fits_poly hs hw (by omega))
  obtain ⟨R, hRdef⟩ : ∃ R, y₄.regs OrderSearch.r = R := ⟨_, rfl⟩
  rw [hRdef] at hR2 hRr₀ hRgood
  have hRs : R ≤ 4 * s ^ 5 := hRr₀.trans hr₀s'
  have hrun₄' := hrun₄.rename (low_injective (by norm_num : 13 ≤ 29))
  set y₄' := y₄.extend (low (by norm_num : 13 ≤ 29)) x₃
  have hy₄R : y₄'.regs osR = R := by
    rw [← hRdef]; exact (low_injective _).extend_apply _ _ OrderSearch.r
  have hy₄ (j : Fin 36) (hj : 29 ≤ j.val) : y₄'.regs j = x₃.regs j :=
    hrun₄'.regs_eq (preserves_low _ _ j hj)
  have hy₄n : y₄'.regs nv = N := by rw [hy₄ nv (by decide)]; simp +decide [x₃, hy₂n]
  -- Step 3 and the totient.
  let x₅ := ((y₄'.set rv R).set gtN N).set gtR R
  have hrun₅ : ExecWithin (B := .standard) w (ram[ rv ← osR; gtN ← nv; gtR ← rv ]) y₄' x₅ 3 := by
    ram_eval [x₅, hy₄R, hy₄n]
  have hx₅n : x₅.regs gtN = N := by simp +decide [x₅]
  have hx₅r : x₅.regs gtR = R := by simp +decide [x₅]
  obtain ⟨y₆, hrun₆, hok, hokiff, hphi, -, -⟩ := GcdTotient.exec
    (x₅.comap (low (k := 11) (by norm_num))) (N := N) (R := R) (by exact hx₅n) (by exact hx₅r)
    hR2 hFN (fits_poly hs hw (by omega))
  have hrun₆' := hrun₆.rename (low_injective (by norm_num : 11 ≤ 29))
  set y₆' := y₆.extend (low (by norm_num : 11 ≤ 29)) x₅
  have hy₆ok : y₆'.regs gtOk = y₆.regs GcdTotient.ok :=
    (low_injective _).extend_apply _ _ GcdTotient.ok
  have hy₆phi : y₆'.regs gtPhi = Nat.totient R := by
    rw [← hphi]; exact (low_injective _).extend_apply _ _ GcdTotient.phi
  have hy₆ (j : Fin 36) (hj : 29 ≤ j.val) : y₆'.regs j = x₅.regs j :=
    hrun₆'.regs_eq (preserves_low _ _ j hj)
  have hy₆n : y₆'.regs nv = N := by rw [hy₆ nv (by decide)]; simp +decide [x₅, hy₄n]
  have hy₆r : y₆'.regs rv = R := by rw [hy₆ rv (by decide)]; simp +decide [x₅]
  have hy₆l : y₆'.regs lv = c * c := by
    rw [hy₆ lv (by decide)]; simp +decide only [x₅, Data.set_regs, Function.update_apply,
      ↓reduceIte]; rw [hy₄ lv (by decide)]; simp +decide [x₃]
  have hy₆1 : y₆'.regs one = 1 := by
    rw [hy₆ one (by decide)]; simp +decide only [x₅, Data.set_regs, Function.update_apply,
      ↓reduceIte]; rw [hy₄ one (by decide)]; simp +decide [x₃, hy₂1]
  have hord : Nat.clog 2 N ^ 2 < orderOf (N : ZMod R) := by
    rw [hcdef, sq]; exact (lt_orderOf_iff hR2).mpr hRgood
  have hprime := prime_iff_passesUpTo_numTestsNat hN hord
  have hOS : OrderSearch.time (c * c) r₀ ≤ OrderSearch.time (s ^ 2) (4 * s ^ 5) := by
    unfold OrderSearch.time; gcongr
  have hGT : GcdTotient.time R ≤ GcdTotient.time (4 * s ^ 5) := by
    unfold GcdTotient.time; gcongr
  by_cases h3 : y₆.regs GcdTotient.ok = 1
  · -- Steps 4 and 5.
    let x₇ := y₆'.set phv (Nat.totient R)
    have hrun₇ : ExecWithin (B := .standard) w (ram[ phv ← gtPhi ]) y₆' x₇ 1 := by
      ram_eval [x₇, hy₆phi]
    obtain ⟨z, hrunz, hz1, hziff⟩ := congruenceSteps_exec (w := w) x₇ (N := N) (R := R)
      (L := c * c) (by simp +decide [x₇, hy₆n]) (by simp +decide [x₇, hy₆r])
      (by simp +decide [x₇, hy₆l]) (by simp +decide [x₇]) hsN hs hw hR2 hRs hcc
    have hbr := ExecWithin.branch_pos (cond := .eq gtOk one) (neg := ram[ ans ← #0 ]) (by
      simp only [Cond.holds_eq, hy₆ok, hy₆1, h3]) (hrun₇.seq hrunz)
    refine ⟨z, (hrun₁.seq (hrun₂'.seq (hrun₃.seq (hrun₄'.seq (hrun₅.seq
      (hrun₆'.seq hbr)))))).mono ?_, hz1, ?_⟩
    · omega
    · rw [hziff, hprime, PassesUpTo, numTestsNat, hcdef, sq]
      exact ⟨fun h => ⟨hpp, hokiff.mp h3, h⟩, fun h => h.2.2⟩
  · -- Step 3 fails.
    let z := y₆'.set ans 0
    have hrunz : ExecWithin (B := .standard) w (ram[ ans ← #0 ]) y₆' z 1 := by
      ram_eval [z, fits_zero]
    have hbr := ExecWithin.branch_neg (cond := .eq gtOk one)
      (pos := .seq (ram[ phv ← gtPhi ]) congruenceSteps) (by
      simp only [Cond.holds_eq, hy₆ok, hy₆1, h3, not_false_eq_true]) hrunz
    refine ⟨z, (hrun₁.seq (hrun₂'.seq (hrun₃.seq (hrun₄'.seq (hrun₅.seq
      (hrun₆'.seq hbr)))))).mono ?_, ?_, ?_⟩
    · omega
    · simp [z]
    · simp only [z, Data.set_regs, Function.update_self, zero_ne_one, false_iff]
      exact fun hp => h3 (hokiff.mpr (passesUpTo_of_prime hp R 0).2.1)

/-- **The AKS algorithm is correct.** At a word size of at least `8 (size n + 1)`, the program
leaves `1` in `ans` if `n` is prime and `0` otherwise, within `time (size n)` instructions. -/
theorem answers {w : ℕ} (N : ℕ) (hw : 8 * (Nat.size N + 1) ≤ w) :
    program.Answers ans w [N] N.Prime (time (Nat.size N)) := by
  obtain ⟨s, hsN⟩ : ∃ s, Nat.size N = s := ⟨_, rfl⟩
  rw [hsN] at hw ⊢
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  have h8 : 2 ^ 8 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF1 : Fits w 1 := fits_iff.mpr (by omega)
  have hF2 : Fits w 2 := fits_iff.mpr (by omega)
  have hmem : (Data.init [N] : Data 36).mem 1 = N := rfl
  let x₁ := (((Data.init [N] : Data 36).set one 1).set two 2).set nv N
  have hrun₁ : ExecWithin (B := .standard) w (ram[ one ← #1; two ← #2; nv ← *one ])
      (.init [N]) x₁ 3 := by
    ram_eval [x₁, hmem, hF1, hF2]
  have hx₁n : x₁.regs nv = N := by simp +decide [x₁]
  have hx₁1 : x₁.regs one = 1 := by simp +decide [x₁]
  have hx₁2 : x₁.regs two = 2 := by simp +decide [x₁]
  by_cases hN : N < 2
  · -- `n < 2`.
    let z := x₁.set ans 0
    have hrunz : ExecWithin (B := .standard) w (ram[ ans ← #0 ]) x₁ z 1 := by
      ram_eval [z, fits_zero]
    refine ⟨z, (hrun₁.seq (ExecWithin.branch_pos (by simp only [Cond.holds_lt, hx₁n, hx₁2, hN])
      hrunz)).mono ?_, by simp [z], ?_⟩
    · unfold time; omega
    · simp only [z, Data.set_regs, Function.update_self, zero_ne_one, false_iff]
      exact fun hp => absurd hp.two_le (by omega)
  have hN2 : 2 ≤ N := by omega
  have hs : 2 ≤ s := hsN ▸ two_le_size hN2
  -- Step 1: the perfect-power test.
  let x₂ := x₁.set ppN N
  have hrun₂ : ExecWithin (B := .standard) w (ram[ ppN ← nv ]) x₁ x₂ 1 := by
    ram_eval [x₂, hx₁n]
  have hx₂ : x₂.regs ppN = N := by simp [x₂]
  obtain ⟨y₃, hrun₃, hflag, -, -⟩ := PerfectPower.exec_rename (low (k := 14) (by norm_num))
    (low_injective _) x₂ (by change 2 ≤ x₂.regs ppN; rw [hx₂]; exact hN2)
    (by
      change Fits w (x₂.regs ppN * x₂.regs ppN + 2 * x₂.regs ppN + 2)
      rw [hx₂]
      refine fits_exp hw ?_
      have : (N + 1) * (N + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul hNs hNs
      have h2 : 2 ^ (2 * s + 1) = 2 ^ s * 2 ^ s * 2 := by ring
      have h4 : 2 ≤ 2 ^ s := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h2]
      nlinarith)
  have hrun₃' : ExecWithin w perfectPower x₂ y₃ (PerfectPower.time N) := by
    rw [← hx₂]; exact hrun₃
  have hflag' : y₃.regs ppFlag = if IsPerfectPower N then 1 else 0 := by
    rw [← hx₂]; exact hflag
  have hy₃ (j : Fin 36) (hj : 29 ≤ j.val) : y₃.regs j = x₂.regs j :=
    hrun₃.regs_eq (preserves_low _ _ j hj)
  have hy₃n : y₃.regs nv = N := by rw [hy₃ nv (by decide)]; simp +decide [x₂, hx₁n]
  have hy₃1 : y₃.regs one = 1 := by rw [hy₃ one (by decide)]; simp +decide [x₂, hx₁1]
  have hPP : PerfectPower.time N ≤ (s + 1) * (s * (6 * s + 13) + 6 * s + 22) + 4 * s + 11 := by
    have hlog : Nat.log 2 N ≤ s := (Nat.log_lt_of_lt_pow (by omega) hNs).le
    have hclog : Nat.clog 2 (N + 1) ≤ s := Nat.clog_le_of_le_pow hNs
    unfold PerfectPower.time; gcongr
  have hbr : ¬ (Cond.lt nv two).Holds x₁ := by simp only [Cond.holds_lt, hx₁n, hx₁2]; omega
  by_cases hpp : IsPerfectPower N
  · -- A perfect power.
    let z := y₃.set ans 0
    have hrunz : ExecWithin (B := .standard) w (ram[ ans ← #0 ]) y₃ z 1 := by
      ram_eval [z, fits_zero]
    refine ⟨z, (hrun₁.seq (ExecWithin.branch_neg hbr (hrun₂.seq (hrun₃'.seq
      (ExecWithin.branch_pos (by simp only [Cond.holds_eq, hflag', hpp, hy₃1, ↓reduceIte])
        hrunz))))).mono ?_, by simp [z], ?_⟩
    · unfold time; omega
    · simp only [z, Data.set_regs, Function.update_self, zero_ne_one, false_iff]
      exact fun hp => not_isPerfectPower_of_prime hp hpp
  · -- Steps 2 to 5.
    obtain ⟨z, hrunz, hz1, hziff⟩ := searchSteps_exec y₃ hy₃n hy₃1 hN2 hpp hsN hw
    refine ⟨z, (hrun₁.seq (ExecWithin.branch_neg hbr (hrun₂.seq (hrun₃'.seq
      (ExecWithin.branch_neg (by simp only [Cond.holds_eq, hflag', hpp, hy₃1, ↓reduceIte]; decide)
        hrunz))))).mono ?_, hz1, hziff⟩
    unfold time; omega

/-- **The AKS algorithm decides the primes.** Its compiled program, given `n` as one word at a word
size of at least `8 (size n + 1)`, answers whether `n` is prime within `time (size n) + 1`
instructions. -/
theorem decidesInTime :
    (program.program ans).DecidesInTime (fun _ n => [n]) {n : ℕ | n.Prime}
      (fun n _ => time (Nat.size n) + 1) (fun n w => 8 * (Nat.size n + 1) ≤ w) :=
  program.decidesInTime_program (time := fun n _ => time (Nat.size n)) ans
    fun n _ hw _ => answers n hw

end Cslib.Algorithms.WordRAM.AKS
