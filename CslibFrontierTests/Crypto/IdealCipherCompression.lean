import CslibFrontier.Languages.Probabilistic.IdealCipher
import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression
import CslibFrontier.Crypto.Primitives.IdealCipher.Compression

open Cslib.OracleComp Cslib.Crypto.BlockCipherCompression Cslib.Probability Cslib.IdealCipher

-- We can just test that the theorem typechecks properly and that cipherOutput is well-defined.
-- We'll use Fin 2 for both Key and Block.

example : cipherOutput (B := Fin 2) (fun _ _ => 1) (1, 0) = 1 := rfl

example : cipherOutput (B := Fin 2) (fun k b => k + b) (1, 1) = 1 := rfl
