/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Support.Wires

/-!
# The real pre-H reset establishes the whole selected bank's zero support

Every original active wire is genuinely reset, including after bad arithmetic
branches. The resulting full-record density is supported on the recursive
zero-bank tuple. Thus the H/feed comparison receives its zero-bank condition
from actual execution, with no additional input or arithmetic premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

/-- Actual active-bank reset establishes the complete zero-bank support on every input. -/
lemma sampling_reset_bank_zero (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × (services.HiddenState ×
      (History × (parameters.reset (services := services) index).Path)))
    (basis : (ctx.register.prod Reference).Index)
    (absent : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits basis.1).1 ≠ Partner.zeroBits (index.lowerWidth + 1)) :
    (((parameters.reset index).execute environment Reference state).block record).matrix
      basis basis = 0 :=
  window_source_bank_zero_support (parameters.ports index).wires
    (parameters.ports index).qubits
    ((parameters.reset index).execute environment Reference state)
    (fun bit => parameters.reset_supported index environment state bit) record basis absent

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
