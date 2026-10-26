/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Naturality
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Step

/-!
# Actual reference naturality in fixed mathematical-source coordinates

The same reference unitary is written as the named source preparation
operator, before specializing any source width or concrete measured code.
The statement retains the actual code, complete records and original input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- The literal source-action head preserves actual execution on every complete input state. -/
lemma sourceAction_referenceNatural
    {code : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations services).Environment}
    (natural : Execution.ReferenceNatural code environment) {S : Register} (Reference : Register)
    (operator : UnitaryOperator S) {History : Type} [Fintype History]
    (state : State ctx (S.prod Reference) (services.HiddenState × History)) :
    code.execute environment (S.prod Reference)
        (state.applyUnitary (fun _ => sourcePreparationAction Reference operator)) =
      (code.execute environment (S.prod Reference) state).applyUnitary
        (fun _ => sourcePreparationAction Reference operator) :=
  natural (S.prod Reference)
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) state

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
