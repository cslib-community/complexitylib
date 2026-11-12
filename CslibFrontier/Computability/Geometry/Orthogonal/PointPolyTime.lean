/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Geometry.Orthogonal.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Foundations.Geometry.Orthogonal.Macrocell
public import CslibFrontier.Foundations.Geometry.Orthogonal.Subdivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native polynomial-time point arithmetic

Polynomial-time certificates for the binary-coordinate point operations shared by the
orthogonal subdivision compiler and the exact-one and paired planar drawing compilers. They are
not global `@[fun_prop]` rules, since their encodings are fixed; clients that compose them add
them with `attribute [local fun_prop]`.

## Main results

* `Cslib.Orthogonal.computableInPolyTime_pointAdd`: adding two points.
* `Cslib.Orthogonal.computableInPolyTime_direction`: the unit direction between two points.
* `Cslib.Orthogonal.computableInPolyTime_translate`: translating a route by a point.
-/

public section

namespace Cslib.Orthogonal

open Turing.MultiTapeTM

/-- Adding two binary-coordinate points is native polynomial-time. -/
theorem computableInPolyTime_pointAdd :
    ComputableInPolyTime (fun p : Point × Point => p.1 + p.2)
      (encPair encPoint encPoint) encPoint := by
  change ComputableInPolyTime (fun p : Point × Point =>
    (p.1.1 + p.2.1, p.1.2 + p.2.2)) _ _
  unfold encPoint
  fun_prop

/-- The unit direction from one binary-coordinate point to another is native polynomial-time. -/
theorem computableInPolyTime_direction :
    ComputableInPolyTime (fun p : Point × Point => direction p.1 p.2)
      (encPair encPoint encPoint) encPoint := by
  unfold direction encPoint
  fun_prop

/-- Translating a route by a point is native polynomial-time. -/
theorem computableInPolyTime_translate :
    ComputableInPolyTime (fun p : Point × Route => translate p.1 p.2)
      (encPair encPoint encRoute) encRoute := by
  change ComputableInPolyTime (fun p : Point × Route =>
    p.2.map fun q => (q.1 + p.1.1, q.2 + p.1.2)) _ _
  unfold encPoint encRoute
  fun_prop

end Cslib.Orthogonal
