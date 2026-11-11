import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Complexity.FineGrained.Diameter
open Turing.MultiTapeTM

abbrev LCSParseState : Type := (((Bool × Bool) × Bool) × ℕ) × ℕ
