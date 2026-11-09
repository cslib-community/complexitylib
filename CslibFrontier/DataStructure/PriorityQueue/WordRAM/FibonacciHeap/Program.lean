/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.Basic
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.Forest
public import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Fibonacci Heap: Static-Array Word-RAM Program and State Representation

This file defines the uniform `Basis.exact` Word-RAM implementation (`code : PQCode .exact rFib`)
of a static-array Fibonacci heap on `n` handles (`space n = 9 * n + 1` words at
`[base, base + 9 * n + 1)`), together with its concrete state projection (`RawState.ofData`),
representation invariant (`FibInv`), potential function (`potential`), per-operation amortized time
bounds, and memory/register framing lemmas.

## Memory layout (`[base, base + 9 * n + 1)`)

* `[base + 0 * n, base + 1 * n)`: `key[0..n-1]`
* `[base + 1 * n, base + 2 * n)`: `par[0..n-1]` (`0` = root, `p + 1` = parent `p`)
* `[base + 2 * n, base + 3 * n)`: `child[0..n-1]` (`0` = leaf, `c + 1` = head child `c`)
* `[base + 3 * n, base + 4 * n)`: `left[0..n-1]` (circular sibling list predecessor)
* `[base + 4 * n, base + 5 * n)`: `right[0..n-1]` (circular sibling list successor)
* `[base + 5 * n, base + 6 * n)`: `deg[0..n-1]` (number of children)
* `[base + 6 * n, base + 7 * n)`: `mark[0..n-1]` (`0` or `1`, child-loss mark)
* `[base + 7 * n, base + 8 * n)`: `inHeap[0..n-1]` (`0` = absent, `1` = present)
* `[base + 8 * n, base + 9 * n + 1)`: `cons[0..n]` (degree-consolidation table, `0` = empty)

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.rFib`, `space`, `potential`, `charge`:
  register count (`42`), memory footprint (`9 * n + 1`), integer potential, and per-operation
  amortized charges.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.code`, `dispatchCode`: structured
  `PQCode .exact rFib` bundle and unified operation dispatcher.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.FibInv`: full machine-state invariant
  over
  `Data rFib`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.FibInv.supported`, `potential_supported`:
  register and memory framing for `StateTransitionImpl`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci heaps and their uses in improved network optimization
  algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue Cslib.DataStructure.WordRAM
open scoped Cslib.WordRAM

/-! ## Register file (`rFib = 42`) and footprint size -/

/-- Total register count of the standalone/subroutine Fibonacci heap machine. -/
abbrev rFib : ℕ := 42

/-- Persistent register holding handle-universe size `n`. -/
abbrev nReg : Fin rFib := ⟨0, by decide⟩
/-- Persistent frontier register (`base` before `allocSpan`, `base + space n` after). -/
abbrev frontierReg : Fin rFib := ⟨1, by decide⟩
/-- Persistent base address of `key[0..n-1]` (`base`). -/
abbrev baseReg : Fin rFib := ⟨2, by decide⟩
/-- Persistent base address of `par[0..n-1]` (`base + n`). -/
abbrev parBase : Fin rFib := ⟨3, by decide⟩
/-- Persistent base address of `child[0..n-1]` (`base + 2 * n`). -/
abbrev childBase : Fin rFib := ⟨4, by decide⟩
/-- Persistent base address of `left[0..n-1]` (`base + 3 * n`). -/
abbrev leftBase : Fin rFib := ⟨5, by decide⟩
/-- Persistent base address of `right[0..n-1]` (`base + 4 * n`). -/
abbrev rightBase : Fin rFib := ⟨6, by decide⟩
/-- Persistent base address of `deg[0..n-1]` (`base + 5 * n`). -/
abbrev degBase : Fin rFib := ⟨7, by decide⟩
/-- Persistent base address of `mark[0..n-1]` (`base + 6 * n`). -/
abbrev markBase : Fin rFib := ⟨8, by decide⟩
/-- Persistent base address of `inHeap[0..n-1]` (`base + 7 * n`). -/
abbrev inBase : Fin rFib := ⟨9, by decide⟩
/-- Persistent base address of `cons[0..n]` (`base + 8 * n`). -/
abbrev consBase : Fin rFib := ⟨10, by decide⟩
/-- Persistent constant register `0`. -/
abbrev zeroP : Fin rFib := ⟨11, by decide⟩
/-- Persistent constant register `1`. -/
abbrev oneP : Fin rFib := ⟨12, by decide⟩
/-- Persistent nullable minimum-root pointer (`0` = empty, `m + 1` = `some m`). -/
abbrev minRootReg : Fin rFib := ⟨13, by decide⟩
/-- Persistent root-list length counter (`numRoots`). -/
abbrev numRootsReg : Fin rFib := ⟨14, by decide⟩
/-- Persistent marked-node counter (`numMarked`). -/
abbrev numMarkedReg : Fin rFib := ⟨15, by decide⟩
/-- Persistent live-element count (`sz`). -/
abbrev szReg : Fin rFib := ⟨16, by decide⟩

/-- Caller high tag bit (`≠ 0` selects `extractMin`). -/
abbrev tag2 : Fin rFib := ⟨17, by decide⟩
/-- Caller middle tag bit. -/
abbrev tag1 : Fin rFib := ⟨18, by decide⟩
/-- Caller low tag bit. -/
abbrev tag0 : Fin rFib := ⟨19, by decide⟩
/-- Caller handle argument register (`v.val`). -/
abbrev argV : Fin rFib := ⟨20, by decide⟩
/-- Caller key argument register (`k`). -/
abbrev argK : Fin rFib := ⟨21, by decide⟩
/-- Output flag register (`output = outFlag`). -/
abbrev outFlag : Fin rFib := ⟨22, by decide⟩
/-- Output handle register (`u.val` for non-empty `extractMin`). -/
abbrev outV : Fin rFib := ⟨23, by decide⟩
/-- Output key register (`k` for present `getKey` and non-empty `extractMin`). -/
abbrev outK : Fin rFib := ⟨24, by decide⟩

/-- Scratch pointer register for generic `SubroutineCode.zeroFillCode`. -/
abbrev curReg : Fin rFib := ⟨25, by decide⟩
/-- Scratch zero register for generic `SubroutineCode.zeroFillCode`. -/
abbrev zeroReg : Fin rFib := ⟨26, by decide⟩
/-- Scratch one register for generic `SubroutineCode.zeroFillCode`. -/
abbrev oneReg : Fin rFib := ⟨27, by decide⟩

/-- Outer scratch register: extracted vertex `z` or cascading-cut target `cur`. -/
abbrev zReg : Fin rFib := ⟨28, by decide⟩
/-- Outer scratch register: parent `p` in `decreaseKey` or `rStart` in `extractMin`. -/
abbrev pReg : Fin rFib := ⟨29, by decide⟩
/-- Outer loop counter (`rem`) in `extractMin` Phase A. -/
abbrev remReg : Fin rFib := ⟨30, by decide⟩
/-- Outer current-node register (`iterCur`) or cascading-cut loop guard. -/
abbrev iterCur : Fin rFib := ⟨31, by decide⟩
/-- Outer saved-next-node register (`iterNxt`) in `extractMin` Phase A. -/
abbrev iterNxt : Fin rFib := ⟨32, by decide⟩
/-- Maximum degree tracker (`maxDeg` / `limit`) in `extractMin`. -/
abbrev maxDegReg : Fin rFib := ⟨33, by decide⟩
/-- Degree index (`d` / `curD`) in `scatterRootCode` and `extractMin` Phase B. -/
abbrev curDReg : Fin rFib := ⟨34, by decide⟩

/-- Inner helper scratch register 0 (addresses). -/
abbrev s0 : Fin rFib := ⟨35, by decide⟩
/-- Inner helper scratch register 1. -/
abbrev s1 : Fin rFib := ⟨36, by decide⟩
/-- Inner helper scratch register 2. -/
abbrev s2 : Fin rFib := ⟨37, by decide⟩
/-- Inner helper scratch register 3. -/
abbrev s3 : Fin rFib := ⟨38, by decide⟩
/-- Inner helper scratch register 4. -/
abbrev s4 : Fin rFib := ⟨39, by decide⟩
/-- Inner helper scratch register 5. -/
abbrev s5 : Fin rFib := ⟨40, by decide⟩
/-- Inner helper scratch register 6. -/
abbrev s6 : Fin rFib := ⟨41, by decide⟩

/-- Persistent registers are `0..16` (`false`); caller/scratch registers are `17..41` (`true`). -/
def inputReg (i : Fin rFib) : Bool :=
  decide (17 ≤ i.val)

/-- Static memory footprint on `n` handles: `9 * n + 1` words. -/
def space (n : ℕ) : ℕ :=
  9 * n + 1

theorem space_lower (n : ℕ) : n + 1 ≤ space n := by
  unfold space
  omega

/-! ## Structured `Basis.exact` Fibonacci-heap subprograms -/

/-- Advance `frontierReg` from `base` to `base + 9 * n + 1` using only `+ nReg` and `+ #1`,
avoiding constants `> 1` so small word widths (`w ≥ 1` when `n = 0`) never fault. -/
def allocSpan : Code .exact rFib :=
  ram_exact[
    baseReg ← frontierReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    frontierReg ← frontierReg + nReg;
    s0 ← #1;
    frontierReg ← frontierReg + s0
  ]

/-- Initialize array-base pointers and zero scalar heap counters (`O(1)` steps). -/
def initSetup : Code .exact rFib :=
  ram_exact[
    parBase ← baseReg + nReg;
    childBase ← parBase + nReg;
    leftBase ← childBase + nReg;
    rightBase ← leftBase + nReg;
    degBase ← rightBase + nReg;
    markBase ← degBase + nReg;
    inBase ← markBase + nReg;
    consBase ← inBase + nReg;
    zeroP ← #0;
    oneP ← #1;
    minRootReg ← #0;
    numRootsReg ← #0;
    numMarkedReg ← #0;
    szReg ← #0
  ]

/-- Set `flagReg ← 1` if `(uReg, kuReg)` strictly precedes `(vReg, kvReg)` lexicographically
(`ku < kv ∨ (ku = kv ∧ u < v)`), and `flagReg ← 0` otherwise. Writes only `flagReg`. -/
def prioLTFlag (uReg kuReg vReg kvReg flagReg : Fin rFib) : Code .exact rFib :=
  ram_exact[
    if kuReg < kvReg then [
      flagReg ← oneP
    ] else [
      if kuReg = kvReg then [
        if uReg < vReg then [
          flagReg ← oneP
        ] else [
          flagReg ← zeroP
        ]
      ] else [
        flagReg ← zeroP
      ]
    ]
  ]

/-- Splice fresh vertex `uReg` immediately after `hReg` in a non-empty circular doubly-linked list
(`left[u] := h; left[right[h]] := u; right[u] := right[h]; right[h] := u`). Writes only `s0, s2`. -/
def insertIntoNonEmptyList (hReg uReg : Fin rFib) : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + hReg;
    s2 ← *s0;
    s0 ← leftBase + uReg;
    *s0 ← hReg;
    s0 ← leftBase + s2;
    *s0 ← uReg;
    s0 ← rightBase + uReg;
    *s0 ← s2;
    s0 ← rightBase + hReg;
    *s0 ← uReg
  ]

/-- Insert root `uReg` into the root circular list, update `minRootReg` under
`IndexedMinPQ.PrioLT`, and increment `numRootsReg`. Writes only `s0..s5, minRootReg, numRootsReg`.
-/
def addRootAndUpdateMin (uReg : Fin rFib) : Code .exact rFib :=
  ram_exact[
    if minRootReg = zeroP then [
      s0 ← leftBase + uReg;
      *s0 ← uReg;
      s0 ← rightBase + uReg;
      *s0 ← uReg;
      minRootReg ← uReg + oneP
    ] else [
      s1 ← minRootReg - oneP;
      ⟪insertIntoNonEmptyList s1 uReg⟫;
      s0 ← baseReg + uReg;
      s3 ← *s0;
      s0 ← baseReg + s1;
      s4 ← *s0;
      ⟪prioLTFlag uReg s3 s1 s4 s5⟫;
      if zeroP < s5 then [
        minRootReg ← uReg + oneP
      ] else [
        s0 ← zeroP
      ]
    ];
    numRootsReg ← numRootsReg + oneP
  ]

/-- `isEmpty`: sets `outFlag ← 1` if `minRootReg = 0`, else `0`. -/
def isEmptyCode : Code .exact rFib :=
  ram_exact[
    if minRootReg = zeroP then [
      outFlag ← oneP
    ] else [
      outFlag ← zeroP
    ]
  ]

/-- `getKey v`: loads `outFlag ← inHeap[argV]` and, if present, `outK ← key[argV]`. -/
def getKeyCode : Code .exact rFib :=
  ram_exact[
    s0 ← inBase + argV;
    outFlag ← *s0;
    if outFlag = zeroP then [
      s0 ← zeroP
    ] else [
      s0 ← baseReg + argV;
      outK ← *s0
    ]
  ]

/-- `insert v k`: initializes singleton root `argV` with key `argK`, splices into root list, and
increments `szReg`. -/
def insertCode : Code .exact rFib :=
  ram_exact[
    s0 ← baseReg + argV;
    *s0 ← argK;
    s0 ← parBase + argV;
    *s0 ← zeroP;
    s0 ← childBase + argV;
    *s0 ← zeroP;
    s0 ← degBase + argV;
    *s0 ← zeroP;
    s0 ← markBase + argV;
    *s0 ← zeroP;
    s0 ← inBase + argV;
    *s0 ← oneP;
    ⟪addRootAndUpdateMin argV⟫;
    szReg ← szReg + oneP
  ]

/-- Cut child `zReg` from parent `pReg` (`par[zReg] = pReg + 1`, `minRootReg ≥ 1`), splicing `zReg`
into the root circular list, clearing `par[zReg]` and `mark[zReg]` (updating `numMarkedReg` if
needed), and incrementing `numRootsReg`. Writes only `s0..s4, numMarkedReg, numRootsReg`. -/
def cutNodeCode : Code .exact rFib :=
  ram_exact[
    s0 ← degBase + pReg;
    s1 ← *s0;
    s1 ← s1 - oneP;
    *s0 ← s1;
    if s1 = zeroP then [
      s0 ← childBase + pReg;
      *s0 ← zeroP
    ] else [
      s0 ← rightBase + zReg;
      s2 ← *s0;
      s0 ← leftBase + zReg;
      s3 ← *s0;
      s0 ← leftBase + s2;
      *s0 ← s3;
      s0 ← rightBase + s3;
      *s0 ← s2;
      s4 ← s2 + oneP;
      s0 ← childBase + pReg;
      *s0 ← s4
    ];
    s1 ← minRootReg - oneP;
    ⟪insertIntoNonEmptyList s1 zReg⟫;
    s0 ← parBase + zReg;
    *s0 ← zeroP;
    s0 ← markBase + zReg;
    s1 ← *s0;
    if zeroP < s1 then [
      *s0 ← zeroP;
      numMarkedReg ← numMarkedReg - oneP
    ] else [
      *s0 ← zeroP
    ];
    numRootsReg ← numRootsReg + oneP
  ]

/-- Evaluate cascading-cut guard `iterCur ← 1` iff `par[zReg] ≠ 0 ∧ mark[zReg] ≠ 0`, else `0`. -/
def evalCascGuard : Code .exact rFib :=
  ram_exact[
    s0 ← parBase + zReg;
    s1 ← *s0;
    if zeroP < s1 then [
      s0 ← markBase + zReg;
      s2 ← *s0;
      if zeroP < s2 then [
        iterCur ← oneP
      ] else [
        iterCur ← zeroP
      ]
    ] else [
      iterCur ← zeroP
    ]
  ]

/-- `decreaseKey v k`: lowers `key[argV] ← argK`, cuts `argV` and runs cascading cuts if parent
order under `IndexedMinPQ.PrioLT` is violated, and updates `minRootReg`. -/
def decreaseKeyCode : Code .exact rFib :=
  ram_exact[
    s0 ← baseReg + argV;
    *s0 ← argK;
    s0 ← parBase + argV;
    s1 ← *s0;
    if zeroP < s1 then [
      pReg ← s1 - oneP;
      s0 ← baseReg + pReg;
      s2 ← *s0;
      ⟪prioLTFlag argV argK pReg s2 s3⟫;
      if zeroP < s3 then [
        zReg ← argV;
        ⟪cutNodeCode⟫;
        zReg ← pReg;
        ⟪evalCascGuard⟫;
        while zeroP < iterCur do [
          s0 ← parBase + zReg;
          s1 ← *s0;
          pReg ← s1 - oneP;
          ⟪cutNodeCode⟫;
          zReg ← pReg;
          ⟪evalCascGuard⟫
        ];
        s0 ← parBase + zReg;
        s1 ← *s0;
        if zeroP < s1 then [
          s0 ← markBase + zReg;
          *s0 ← oneP;
          numMarkedReg ← numMarkedReg + oneP
        ] else [
          s0 ← zeroP
        ]
      ] else [
        s0 ← zeroP
      ]
    ] else [
      s0 ← zeroP
    ];
    s1 ← minRootReg - oneP;
    s0 ← baseReg + s1;
    s2 ← *s0;
    ⟪prioLTFlag argV argK s1 s2 s3⟫;
    if zeroP < s3 then [
      minRootReg ← argV + oneP
    ] else [
      s0 ← zeroP
    ]
  ]

/-- Scatter root `iterCur` into `cons`, linking equal-degree roots under `IndexedMinPQ.PrioLT`
until reaching an empty slot and updating `maxDegReg`. Writes only `s0..s6, curDReg, maxDegReg`. -/
def scatterRootCode : Code .exact rFib :=
  ram_exact[
    s4 ← iterCur;
    s0 ← degBase + s4;
    curDReg ← *s0;
    s0 ← consBase + curDReg;
    s3 ← *s0;
    while zeroP < s3 do [
      s5 ← s3 - oneP;
      s0 ← consBase + curDReg;
      *s0 ← zeroP;
      s0 ← baseReg + s4;
      s1 ← *s0;
      s0 ← baseReg + s5;
      s2 ← *s0;
      ⟪prioLTFlag s5 s2 s4 s1 s6⟫;
      if zeroP < s6 then [
        s6 ← s4;
        s4 ← s5;
        s5 ← s6
      ] else [
        s0 ← zeroP
      ];
      s1 ← s4 + oneP;
      s0 ← parBase + s5;
      *s0 ← s1;
      s0 ← degBase + s4;
      s1 ← *s0;
      if s1 = zeroP then [
        s0 ← leftBase + s5;
        *s0 ← s5;
        s0 ← rightBase + s5;
        *s0 ← s5;
        s2 ← s5 + oneP;
        s0 ← childBase + s4;
        *s0 ← s2;
        s0 ← degBase + s4;
        *s0 ← oneP
      ] else [
        s0 ← childBase + s4;
        s6 ← *s0;
        s6 ← s6 - oneP;
        ⟪insertIntoNonEmptyList s6 s5⟫;
        s1 ← s1 + oneP;
        s0 ← degBase + s4;
        *s0 ← s1
      ];
      curDReg ← curDReg + oneP;
      s0 ← consBase + curDReg;
      s3 ← *s0
    ];
    s1 ← s4 + oneP;
    s0 ← consBase + curDReg;
    *s0 ← s1;
    if maxDegReg < curDReg then [
      maxDegReg ← curDReg
    ] else [
      s0 ← zeroP
    ]
  ]

/-- `extractMin`: returns `0` when empty, or removes `z = minRootReg - 1`, scatters `z`'s children
and the `numRoots - 1` remaining roots into `cons`, and scans `0 .. maxDeg` to rebuild the root
circular list and `minRootReg` while restoring `cons = 0` in `O(log n)` steps. -/
def extractMinCode : Code .exact rFib :=
  ram_exact[
    if minRootReg = zeroP then [
      outFlag ← zeroP
    ] else [
      zReg ← minRootReg - oneP;
      outFlag ← oneP;
      outV ← zReg;
      s0 ← baseReg + zReg;
      outK ← *s0;
      s0 ← inBase + zReg;
      *s0 ← zeroP;
      szReg ← szReg - oneP;
      s0 ← rightBase + zReg;
      pReg ← *s0;
      maxDegReg ← zeroP;
      s0 ← degBase + zReg;
      remReg ← *s0;
      if zeroP < remReg then [
        s0 ← childBase + zReg;
        s1 ← *s0;
        iterCur ← s1 - oneP;
        while zeroP < remReg do [
          s0 ← rightBase + iterCur;
          iterNxt ← *s0;
          s0 ← parBase + iterCur;
          *s0 ← zeroP;
          s0 ← markBase + iterCur;
          s1 ← *s0;
          if zeroP < s1 then [
            *s0 ← zeroP;
            numMarkedReg ← numMarkedReg - oneP
          ] else [
            s0 ← zeroP
          ];
          ⟪scatterRootCode⟫;
          iterCur ← iterNxt;
          remReg ← remReg - oneP
        ]
      ] else [
        s0 ← zeroP
      ];
      remReg ← numRootsReg - oneP;
      iterCur ← pReg;
      while zeroP < remReg do [
        s0 ← rightBase + iterCur;
        iterNxt ← *s0;
        ⟪scatterRootCode⟫;
        iterCur ← iterNxt;
        remReg ← remReg - oneP
      ];
      minRootReg ← zeroP;
      numRootsReg ← zeroP;
      maxDegReg ← maxDegReg + oneP;
      curDReg ← zeroP;
      while curDReg < maxDegReg do [
        s0 ← consBase + curDReg;
        s3 ← *s0;
        if zeroP < s3 then [
          *s0 ← zeroP;
          iterCur ← s3 - oneP;
          ⟪addRootAndUpdateMin iterCur⟫
        ] else [
          s0 ← zeroP
        ];
        curDReg ← curDReg + oneP
      ]
    ]
  ]

/-- Unified dispatcher over 1-bit tags `(tag2, tag1, tag0)`. -/
def dispatchCode : Code .exact rFib :=
  ram_exact[
    if tag2 = zeroP then [
      if tag1 = zeroP then [
        if tag0 = zeroP then [
          ⟪isEmptyCode⟫
        ] else [
          ⟪getKeyCode⟫
        ]
      ] else [
        if tag0 = zeroP then [
          ⟪insertCode⟫
        ] else [
          ⟪decreaseKeyCode⟫
        ]
      ]
    ] else [
      ⟪extractMinCode⟫
    ]
  ]

/-- Uniform `PQCode .exact rFib` bundle for the static-array Fibonacci heap. -/
def code : PQCode .exact rFib where
  allocSpan := allocSpan
  initSetup := initSetup
  code := dispatchCode
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := ![nReg]
  curReg := curReg
  zeroReg := zeroReg
  oneReg := oneReg
  incCur := .exactBin .add curReg curReg oneReg
  input := inputReg
  output := outFlag
  nReg := nReg
  tag2 := tag2
  tag1 := tag1
  tag0 := tag0
  argV := argV
  argK := argK
  outFlag := outFlag
  outV := outV
  outK := outK
  initParams_eq := rfl
  nReg_ne_frontier := by decide
  args_nodup := by decide
  tag2_input := by decide
  tag1_input := by decide
  tag0_input := by decide
  argV_input := by decide
  argK_input := by decide
  output_eq := rfl

/-! ## Concrete state projection, representation invariant, and amortized bounds -/

/-- Project `Data rFib` at `(n, base)` to a logical `RawState n`. -/
def RawState.ofData (n base : ℕ) (x : Data rFib) : RawState n where
  key v := x.mem (base + v.val)
  par v := x.mem (base + n + v.val)
  child v := x.mem (base + 2 * n + v.val)
  left v := x.mem (base + 3 * n + v.val)
  right v := x.mem (base + 4 * n + v.val)
  deg v := x.mem (base + 5 * n + v.val)
  mark v := x.mem (base + 6 * n + v.val)
  inHeap v := x.mem (base + 7 * n + v.val)
  cons d := if d ≤ n then x.mem (base + 8 * n + d) else 0
  minRoot := x.regs minRootReg
  numRoots := x.regs numRootsReg
  numMarked := x.regs numMarkedReg
  sz := x.regs szReg

/-- Persistent base-address and constant registers `0..12` hold their initialized values. -/
structure BaseRegs (n base : ℕ) (x : Data rFib) : Prop where
  /-- `nReg` holds the handle-universe size `n`. -/
  regs_nReg : x.regs nReg = n
  /-- `frontierReg` holds the end of the footprint. -/
  regs_frontierReg : x.regs frontierReg = base + space n
  /-- `baseReg` holds the base address of `key`. -/
  regs_baseReg : x.regs baseReg = base
  /-- `parBase` holds the base address of `par`. -/
  regs_parBase : x.regs parBase = base + n
  /-- `childBase` holds the base address of `child`. -/
  regs_childBase : x.regs childBase = base + 2 * n
  /-- `leftBase` holds the base address of `left`. -/
  regs_leftBase : x.regs leftBase = base + 3 * n
  /-- `rightBase` holds the base address of `right`. -/
  regs_rightBase : x.regs rightBase = base + 4 * n
  /-- `degBase` holds the base address of `deg`. -/
  regs_degBase : x.regs degBase = base + 5 * n
  /-- `markBase` holds the base address of `mark`. -/
  regs_markBase : x.regs markBase = base + 6 * n
  /-- `inBase` holds the base address of `inHeap`. -/
  regs_inBase : x.regs inBase = base + 7 * n
  /-- `consBase` holds the base address of `cons`. -/
  regs_consBase : x.regs consBase = base + 8 * n
  /-- `zeroP` holds `0`. -/
  regs_zeroP : x.regs zeroP = 0
  /-- `oneP` holds `1`. -/
  regs_oneP : x.regs oneP = 1

/-- Full Word-RAM representation invariant for `FibonacciHeap` at `(n, K_max, w, base)`. -/
def FibInv (n K_max w base : ℕ) (s : IndexedMinPQ.State n) (x : Data rFib) : Prop :=
  x.Bounded w ∧ BaseRegs n base x ∧ FibRawInv n K_max s (RawState.ofData n base x)

/-- Amortized credit per root (`80` instructions; marked nodes carry `2 * unitCredit = 160`). -/
abbrev unitCredit : ℕ := 80

/-- Internal consolidation-slot credit (`50` instructions per occupied degree slot). -/
abbrev slotCredit : ℕ := 50

/-- Concrete integer potential `80 * (numRoots + 2 * numMarked)`. -/
def potential (x : Data rFib) : ℕ :=
  unitCredit * (x.regs numRootsReg + 2 * x.regs numMarkedReg)

/-- Fresh-initialization instruction bound (`allocSpan` 12 + `initSetup` 14 = 26). -/
def tInit (_n : ℕ) : ℕ := 26
/-- Instruction bound for `isEmpty` (including dispatch). -/
def tEmpty (_n : ℕ) : ℕ := 12
/-- Instruction bound for `getKey` (including dispatch). -/
def tGet (_n : ℕ) : ℕ := 16
/-- Amortized instruction bound for `insert` (including dispatch and `+80` root potential). -/
def tIns (_n : ℕ) : ℕ := 130
/-- Amortized instruction bound for `decreaseKey` (including dispatch and cascading cuts). -/
def tDec (_n : ℕ) : ℕ := 340
/-- Amortized instruction bound for `extractMin` (`O(log n + 1)`). -/
def tExt (n : ℕ) : ℕ := 420 * (Nat.log 2 n + 1)

/-- Per-operation amortized instruction charge for `FibonacciHeap`, charging
`tExt (IndexedMinPQ.dom s).card` on `.extractMin` in terms of the current number of stored
elements `(IndexedMinPQ.dom s).card`. -/
def charge (n : ℕ) (s : IndexedMinPQ.State n) : IndexedMinPQ.Op n → ℕ
  | .isEmpty => tEmpty n
  | .getKey _ => tGet n
  | .insert _ _ => tIns n
  | .decreaseKey _ _ => tDec n
  | .extractMin => tExt (IndexedMinPQ.dom s).card

/-- The current number of stored elements `(IndexedMinPQ.dom s).card` is at most `n`, so
`charge n s .extractMin ≤ tExt n`. -/
theorem charge_extractMin_le_tExt (n : ℕ) (s : IndexedMinPQ.State n) :
    charge n s .extractMin ≤ tExt n := by
  simp only [charge, tExt]
  have hcard : (IndexedMinPQ.dom s).card ≤ n := by
    simpa using (IndexedMinPQ.dom s).card_le_univ
  have hlog : Nat.log 2 (IndexedMinPQ.dom s).card ≤ Nat.log 2 n :=
    Nat.log_mono_right hcard
  omega

/-! ## Exact-ALU step rules, footprint framing, and `RawState.ofData` update lemmas -/

theorem execWithin_exactAdd {w r : ℕ} {x : Data r} {d i j : Fin r}
    (hfit : Fits w (x.regs i + x.regs j)) :
    ExecWithin (B := .exact) w (.op (.exactBin .add d i j)) x
      (x.set d (x.regs i + x.regs j)) 1 :=
  ExecWithin.op (by
    rw [Op.eval_exactBin]
    simp only [BinOp.evalExact, Option.bind_some]
    exact Data.put_of_fits hfit)

theorem execWithin_exactSub {w r : ℕ} {x : Data r} {d i j : Fin r}
    (hle : x.regs j ≤ x.regs i) (hfit : Fits w (x.regs i - x.regs j)) :
    ExecWithin (B := .exact) w (.op (.exactBin .sub d i j)) x
      (x.set d (x.regs i - x.regs j)) 1 :=
  ExecWithin.op (by
    rw [Op.eval_exactBin]
    simp only [BinOp.evalExact, hle, ↓reduceIte, Option.bind_some]
    exact Data.put_of_fits hfit)

theorem modifies_block_trans {b : Block} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : Modifies b.footprint m₁ m₂) (h₂ : Modifies b.footprint m₂ m₃) :
    Modifies b.footprint m₁ m₃ := by
  simpa only [Finset.union_idempotent] using h₁.trans h₂

theorem BaseRegs.fits_stop {n base w : ℕ} {x : Data rFib} (hb : x.Bounded w)
    (hbr : BaseRegs n base x) : Fits w (base + space n) :=
  hbr.regs_frontierReg ▸ hb.1 frontierReg

/-- A value at most `base + 9 * n`, such as an address in one of the nine arrays, fits a word. -/
theorem BaseRegs.fits_of_le {n base w : ℕ} {x : Data rFib} (hb : x.Bounded w)
    (hbr : BaseRegs n base x) (v : ℕ) (hv : v ≤ base + 9 * n) : Fits w v :=
  (hbr.fits_stop hb).of_le (by unfold space; omega)

theorem BaseRegs.set_non_base {n base : ℕ} {x : Data rFib} (hbr : BaseRegs n base x)
    {d : Fin rFib} (hd : 13 ≤ d.val) (v : ℕ) : BaseRegs n base (x.set d v) := by
  have ne_of : ∀ r : Fin rFib, r.val < 13 → r ≠ d := fun r hr e => by subst e; omega
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hbr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of nReg (by decide))] using h0
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of frontierReg (by decide))] using h1
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of baseReg (by decide))] using h2
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of parBase (by decide))] using h3
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of childBase (by decide))] using h4
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of leftBase (by decide))] using h5
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of rightBase (by decide))] using h6
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of degBase (by decide))] using h7
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of markBase (by decide))] using h8
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of inBase (by decide))] using h9
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of consBase (by decide))] using h10
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of zeroP (by decide))] using h11
  · simpa only [Data.set_regs, Function.update_of_ne (ne_of oneP (by decide))] using h12

theorem BaseRegs.write_eq {n base : ℕ} {x : Data rFib} (hbr : BaseRegs n base x) (a v : ℕ) :
    BaseRegs n base (x.write a v) :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hbr
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Setting a register outside the base registers `0..12` keeps `BaseRegs`. -/
theorem BaseRegs.set_iff {n base : ℕ} {x : Data rFib} {d : Fin rFib} (hd : 13 ≤ d.val) (v : ℕ) :
    BaseRegs n base (x.set d v) ↔ BaseRegs n base x := by
  refine ⟨fun h => ?_, fun h => h.set_non_base hd v⟩
  have key (r : Fin rFib) (hr : r.val < 13) : x.regs r = (x.set d v).regs r :=
    (Data.set_regs_of_ne (fun e => by subst e; omega) v).symm
  exact ⟨(key nReg (by decide)).trans h.regs_nReg,
    (key frontierReg (by decide)).trans h.regs_frontierReg,
    (key baseReg (by decide)).trans h.regs_baseReg,
    (key parBase (by decide)).trans h.regs_parBase,
    (key childBase (by decide)).trans h.regs_childBase,
    (key leftBase (by decide)).trans h.regs_leftBase,
    (key rightBase (by decide)).trans h.regs_rightBase,
    (key degBase (by decide)).trans h.regs_degBase,
    (key markBase (by decide)).trans h.regs_markBase,
    (key inBase (by decide)).trans h.regs_inBase, (key consBase (by decide)).trans h.regs_consBase,
    (key zeroP (by decide)).trans h.regs_zeroP, (key oneP (by decide)).trans h.regs_oneP⟩

/-- Writing memory keeps `BaseRegs`. -/
theorem BaseRegs.write_iff {n base : ℕ} {x : Data rFib} (a v : ℕ) :
    BaseRegs n base (x.write a v) ↔ BaseRegs n base x :=
  ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, fun h => h.write_eq a v⟩

theorem BaseRegs.preserved {n base w T : ℕ} {c : Code .exact rFib} {x y : Data rFib}
    (he : ExecWithin w c x y T) (hbr : BaseRegs n base x)
    (hp0 : c.Preserves nReg) (hp1 : c.Preserves frontierReg) (hp2 : c.Preserves baseReg)
    (hp3 : c.Preserves parBase) (hp4 : c.Preserves childBase) (hp5 : c.Preserves leftBase)
    (hp6 : c.Preserves rightBase) (hp7 : c.Preserves degBase) (hp8 : c.Preserves markBase)
    (hp9 : c.Preserves inBase) (hp10 : c.Preserves consBase) (hp11 : c.Preserves zeroP)
    (hp12 : c.Preserves oneP) : BaseRegs n base y :=
  ⟨(he.regs_eq hp0).trans hbr.regs_nReg, (he.regs_eq hp1).trans hbr.regs_frontierReg,
    (he.regs_eq hp2).trans hbr.regs_baseReg, (he.regs_eq hp3).trans hbr.regs_parBase,
    (he.regs_eq hp4).trans hbr.regs_childBase, (he.regs_eq hp5).trans hbr.regs_leftBase,
    (he.regs_eq hp6).trans hbr.regs_rightBase, (he.regs_eq hp7).trans hbr.regs_degBase,
    (he.regs_eq hp8).trans hbr.regs_markBase,
    (he.regs_eq hp9).trans hbr.regs_inBase,
    (he.regs_eq hp10).trans hbr.regs_consBase,
    (he.regs_eq hp11).trans hbr.regs_zeroP,
    (he.regs_eq hp12).trans hbr.regs_oneP⟩

theorem ofData_set_scratch {n base : ℕ} (x : Data rFib) {d : Fin rFib} (hd : 17 ≤ d.val)
    (v : ℕ) : RawState.ofData n base (x.set d v) = RawState.ofData n base x := by
  have ne13 : minRootReg ≠ d := fun e => by subst e; change 17 ≤ 13 at hd; omega
  have ne14 : numRootsReg ≠ d := fun e => by subst e; change 17 ≤ 14 at hd; omega
  have ne15 : numMarkedReg ≠ d := fun e => by subst e; change 17 ≤ 15 at hd; omega
  have ne16 : szReg ≠ d := fun e => by subst e; change 17 ≤ 16 at hd; omega
  simp only [RawState.ofData, Data.set_mem, Data.set_regs, Function.update_of_ne ne13,
    Function.update_of_ne ne14, Function.update_of_ne ne15, Function.update_of_ne ne16]

theorem ofData_set_minRoot {n base : ℕ} (x : Data rFib) (v : ℕ) :
    RawState.ofData n base (x.set minRootReg v) =
      { RawState.ofData n base x with minRoot := v } := by
  simp only [RawState.ofData, Data.set_mem, Data.set_regs, Function.update_self]
  rfl

theorem ofData_set_numRoots {n base : ℕ} (x : Data rFib) (v : ℕ) :
    RawState.ofData n base (x.set numRootsReg v) =
      { RawState.ofData n base x with numRoots := v } := by
  simp only [RawState.ofData, Data.set_mem, Data.set_regs, Function.update_self]
  rfl

theorem ofData_set_numMarked {n base : ℕ} (x : Data rFib) (v : ℕ) :
    RawState.ofData n base (x.set numMarkedReg v) =
      { RawState.ofData n base x with numMarked := v } := by
  simp only [RawState.ofData, Data.set_mem, Data.set_regs, Function.update_self]
  rfl

theorem ofData_set_sz {n base : ℕ} (x : Data rFib) (v : ℕ) :
    RawState.ofData n base (x.set szReg v) =
      { RawState.ofData n base x with sz := v } := by
  simp only [RawState.ofData, Data.set_mem, Data.set_regs, Function.update_self]
  rfl

/-! The `ofData_write_*` lemmas: a write into one of the nine arrays updates that field of
`RawState.ofData` and leaves the other eight arrays alone, because the arrays occupy disjoint
address ranges. Each proof compares the two sides field by field: `Function.update_of_ne`, with
`omega` separating the address ranges, clears the untouched fields, and a case split on the
written slot finishes the updated one. -/

theorem ofData_write_key {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + v.val) val) =
      { RawState.ofData n base x with
        key := Function.update (RawState.ofData n base x).key v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_par {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + n + v.val) val) =
      { RawState.ofData n base x with
        par := Function.update (RawState.ofData n base x).par v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_child {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 2 * n + v.val) val) =
      { RawState.ofData n base x with
        child := Function.update (RawState.ofData n base x).child v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_left {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 3 * n + v.val) val) =
      { RawState.ofData n base x with
        left := Function.update (RawState.ofData n base x).left v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_right {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 4 * n + v.val) val) =
      { RawState.ofData n base x with
        right := Function.update (RawState.ofData n base x).right v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_deg {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 5 * n + v.val) val) =
      { RawState.ofData n base x with
        deg := Function.update (RawState.ofData n base x).deg v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_mark {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 6 * n + v.val) val) =
      { RawState.ofData n base x with
        mark := Function.update (RawState.ofData n base x).mark v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_inHeap {n base : ℕ} (x : Data rFib) (v : Fin n) (val : ℕ) :
    RawState.ofData n base (x.write (base + 7 * n + v.val) val) =
      { RawState.ofData n base x with
        inHeap := Function.update (RawState.ofData n base x).inHeap v val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem ofData_write_cons {n base d : ℕ} (hd : d ≤ n) (x : Data rFib) (val : ℕ) :
    RawState.ofData n base (x.write (base + 8 * n + d) val) =
      { RawState.ofData n base x with
        cons := Function.update (RawState.ofData n base x).cons d val } := by
  simp only [RawState.ofData, Data.write_mem, Data.write_regs, RawState.mk.injEq, and_true]
  and_intros <;> funext u <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem ofData_supported {n base : ℕ} {x x' : Data rFib}
    (hreg : ∀ i : Fin rFib, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n)).footprint, x'.mem a = x.mem a) :
    RawState.ofData n base x' = RawState.ofData n base x := by
  have hmem' : ∀ a, base ≤ a → a < base + (9 * n + 1) → x'.mem a = x.mem a := fun a h₁ h₂ =>
    hmem a (by simp only [Block.mem_footprint, Block.Owns, space]; omega)
  simp only [RawState.ofData, RawState.mk.injEq, hreg minRootReg (by decide),
    hreg numRootsReg (by decide), hreg numMarkedReg (by decide), hreg szReg (by decide), and_true]
  and_intros <;> funext u <;> (try split_ifs) <;> first | rfl | exact hmem' _ (by omega) (by omega)

theorem FibInv.supported {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x x' : Data rFib}
    (hreg : ∀ i : Fin rFib, inputReg i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n)).footprint, x'.mem a = x.mem a)
    (hb' : x'.Bounded w) (h : FibInv n K_max w base s x) :
    FibInv n K_max w base s x' := by
  obtain ⟨_, hbr, hraw⟩ := h
  refine ⟨hb', ?_, ?_⟩
  · exact ⟨(hreg nReg (by decide)).trans hbr.regs_nReg,
      (hreg frontierReg (by decide)).trans hbr.regs_frontierReg,
      (hreg baseReg (by decide)).trans hbr.regs_baseReg,
      (hreg parBase (by decide)).trans hbr.regs_parBase,
      (hreg childBase (by decide)).trans hbr.regs_childBase,
      (hreg leftBase (by decide)).trans hbr.regs_leftBase,
      (hreg rightBase (by decide)).trans hbr.regs_rightBase,
      (hreg degBase (by decide)).trans hbr.regs_degBase,
      (hreg markBase (by decide)).trans hbr.regs_markBase,
      (hreg inBase (by decide)).trans hbr.regs_inBase,
      (hreg consBase (by decide)).trans hbr.regs_consBase,
      (hreg zeroP (by decide)).trans hbr.regs_zeroP,
      (hreg oneP (by decide)).trans hbr.regs_oneP⟩
  · rw [ofData_supported hreg hmem]
    exact hraw

theorem potential_supported {x x' : Data rFib}
    (hreg : ∀ i : Fin rFib, inputReg i = false → x'.regs i = x.regs i) :
    potential x' = potential x := by
  simp only [potential, hreg numRootsReg (by decide), hreg numMarkedReg (by decide)]

/-- Setting a caller or scratch register keeps the potential. -/
theorem potential_set_scratch (x : Data rFib) {d : Fin rFib} (hd : 17 ≤ d.val) (v : ℕ) :
    potential (x.set d v) = potential x :=
  potential_supported fun i hi =>
    Data.set_regs_of_ne (fun e => by subst e; simp [inputReg, hd] at hi) v

/-- Writing memory keeps the potential. -/
theorem potential_write (x : Data rFib) (a v : ℕ) : potential (x.write a v) = potential x := rfl

/-- Setting the marked-node counter. -/
theorem potential_set_numMarked (x : Data rFib) (v : ℕ) :
    potential (x.set numMarkedReg v) = unitCredit * (x.regs numRootsReg + 2 * v) := by
  simp only [potential, Data.set_regs_self,
    Data.set_regs_of_ne (by decide : numRootsReg ≠ numMarkedReg)]

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
