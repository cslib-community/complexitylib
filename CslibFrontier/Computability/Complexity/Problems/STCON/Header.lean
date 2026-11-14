/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output

/-!
# Reading the header of an encoded connectivity instance

Logarithmic-space reductions from directed `s`–`t` connectivity read the unary header
`1^n 0 1^s 0 1^t 0` of the encoding `Cslib.Complexity.encSTCON` into three registers before
they read the adjacency matrix by address. `Cslib.Complexity.STCONInstance.headerCode` is that
code, for counter programs with output, and `Cslib.Complexity.STCONInstance.reachesOut_headerCode`
says that it stores `n`, `s` and `t` in the registers `0`, `1` and `2`, emitting nothing.

## Main definitions

* `Cslib.Complexity.STCONInstance.headerCode`: the code reading the header.

## Main results

* `Cslib.Complexity.STCONInstance.reachesOut_headerCode`: the header is read into the registers
  `0`, `1` and `2`.
-/

@[expose] public section

namespace Cslib.Complexity

namespace STCONInstance

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr

/-- **The code reading the header**, placed at the label `b`: it counts the three unary blocks
into the registers `0`, `1` and `2`, which start at `0`, and continues at `b + 6`. -/
def headerCode (b : ℕ) : List Instr :=
  [read (reg 0) (b + 1) (b + 2) (b + 2),
   assign 0 (add (reg 0) (const 1)) b,
   read (add (add (reg 0) (const 1)) (reg 1)) (b + 3) (b + 4) (b + 4),
   assign 1 (add (reg 1) (const 1)) (b + 2),
   read (add (add (add (add (reg 0) (const 1)) (reg 1)) (const 1)) (reg 2)) (b + 5) (b + 6)
     (b + 6),
   assign 2 (add (reg 2) (const 1)) (b + 4)]

variable (I : STCONInstance) {P : CounterProgram} {B : ℕ}

/-- **The header is read**: from the registers `0, 0, 0` followed by `rest`, the code stores `n`,
`s` and `t` in the registers `0`, `1` and `2`, emitting nothing, while every register stays at
most `B`. -/
theorem reachesOut_headerCode {b : ℕ} (hP : P.CodeAt b (headerCode b)) {rest : List ℕ}
    (hB : I.n ≤ B) (hrest : ∀ r ∈ rest, r ≤ B) :
    P.ReachesOut I.encode (P.Active B) (b, 0 :: 0 :: 0 :: rest)
      (b + 6, I.n :: I.s :: I.t :: rest) [] := by
  have hs := I.s.isLt
  have ht := I.t.isLt
  have hi (i : ℕ) (h : i < 6) := hP i (by simpa [headerCode] using h)
  have hbd : ∀ {x y z : ℕ}, x ≤ I.n → y ≤ I.n → z ≤ I.n → ∀ r ∈ x :: y :: z :: rest, r ≤ B := by
    intro x y z hx hy hz r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · omega
    · omega
    · omega
    · exact hrest r hr
  have hn := reachesOut_count (w := I.encode) (B := B) (n := I.n) (u := 0) (c := b)
    (fun j => j :: 0 :: 0 :: rest) (hi 0 (by omega)) (hi 1 (by omega)) (fun _ _ => by simp)
    (fun j hj => hbd hj (by omega) (by omega))
    (fun j hj => by simp [I.getElem?_encode_n hj.le, hj])
    (by simp [I.getElem?_encode_n le_rfl]) 0 (Nat.zero_le _)
  have hs' := reachesOut_count (w := I.encode) (B := B) (n := I.s) (u := 1) (c := b + 2)
    (fun j => I.n :: j :: 0 :: rest) (hi 2 (by omega)) (hi 3 (by omega)) (fun _ _ => by simp)
    (fun j hj => hbd le_rfl (by omega) (by omega))
    (fun j hj => by simp [I.getElem?_encode_s hj.le, hj])
    (by simp [I.getElem?_encode_s le_rfl]) 0 (Nat.zero_le _)
  have ht' := reachesOut_count (w := I.encode) (B := B) (n := I.t) (u := 2) (c := b + 2 + 2)
    (fun j => I.n :: I.s :: j :: rest) (hi 4 (by omega)) (hi 5 (by omega)) (fun _ _ => by simp)
    (fun j hj => hbd le_rfl (by omega) (by omega))
    (fun j hj => by simp [I.getElem?_encode_t hj.le, hj])
    (by simp [I.getElem?_encode_t le_rfl]) 0 (Nat.zero_le _)
  exact (hn.trans (hs'.trans ht')).of_eq rfl

end STCONInstance

end Cslib.Complexity
