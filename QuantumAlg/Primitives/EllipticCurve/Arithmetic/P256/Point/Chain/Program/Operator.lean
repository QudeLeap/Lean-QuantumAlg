/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program
import all QuantumAlg.Components.Encoded.Circuit.Reference

/-!
# Exact native fragment operators on the original point program's wires

Every native fragment is the actual program matrix on the supplied whole
bank beside reference identity. The basis label uses the existing ordered
wire correspondence. These mathematical operators add no program syntax
and preserve the original complete physical label.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

/-- Original complete physical label beside its original arbitrary reference basis value. -/
def referenceKet (state : Window.Raw) {Reference : Register} (reference : Reference.Index) :
    HilbertVector (ctx.register.prod Reference) :=
  (NormalizedVector.ket (R := ctx.register.prod Reference)
    (measuredEncodedBasis (QubitLayout.canonical Window.encoding.width) parameters.sameWires state,
      reference)).vec

/-- The exact matrix of the original placed native fragment beside reference identity. -/
def nativeOperator (body : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical Window.encoding.width).toQuantum)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (ctx.register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((unitaryOfEqualWires _ _ parameters.sameWires body).matrix environment)
    (1 : UnitaryOperator Reference)

/-- A proved native action keeps the complete original address and reference in the actual bank. -/
lemma nativeOperator_original
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (environment : OracleModel.empty.Interpretation) (initial final : Window.Raw)
    (actual : body.applyNormalized environment (Window.ket initial) = Window.ket final)
    {Reference : Register} (reference : Reference.Index) :
    (parameters.nativeOperator body environment Reference).applyVec
        (parameters.referenceKet initial reference) =
      parameters.referenceKet final reference :=
  UnitaryCircuit.equalWires_reference_ket_of_eq
    (encoding := Window.encoding) (physical := QubitLayout.canonical Window.encoding.width)
    ctx.quantumLayout parameters.sameWires body environment initial final actual reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
