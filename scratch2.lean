import CslibFrontier.Crypto.Protocols.MPC.Composition
import CslibFrontier.Crypto.Protocols.MPC.Advantage

namespace Cslib.Crypto.Protocols.MPC
open Probability Cslib.Crypto.Game

def Steps.countOracles {m : ℕ} {spec : MultiOracleSpec} {State Out : Fin m → Type} {sc : Schedule m spec} : Steps State Out sc → ℕ
| .done _ => 0
| .message _ next => next.countOracles
| .oracle _ next => next.countOracles + 1

end Cslib.Crypto.Protocols.MPC
