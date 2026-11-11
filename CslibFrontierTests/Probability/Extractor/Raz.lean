import CslibFrontier.Probability.Extractor.Raz
import CslibFrontier.Init

open Cslib.Probability Matrix

def M_test : ZMod 2 → Matrix (Fin 2) (Fin 2) (ZMod 2)
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]

#eval razExtractor M_test (![1, 0], ![0, 1]) 0
#eval razExtractor M_test (![1, 0], ![0, 1]) 1
