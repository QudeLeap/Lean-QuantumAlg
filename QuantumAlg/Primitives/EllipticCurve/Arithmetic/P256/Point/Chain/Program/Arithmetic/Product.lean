/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Enable
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Coherent
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Field.Update

/-!
# Original complete field action of the actual measured product call

The actual measured multiplication and actual inverse enable restore
the same full source with the selected Y product. Genuine N is
retained, including its inactive sector, and every measurement has the
same original coefficient beside an arbitrary untouched reference.
The preceding square and normal preparation remain separate fragments.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

/-- The actual multiplication and subsequent clear factors for one original retained record. -/
def productCallOperator (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (ctx.register.prod Reference) :=
  parameters.nativeOperator
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference *
    Arithmetic.Call.branchOperator (services := services) parameters.sameWires parameters.output
        parameters.mask .multiplication parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound store
        (Reset.outcomePath (services := services) .numerator parameters.sameWires parameters.output
          outcome anchor) environment Reference

attribute [local implicit_reducible] capacity width

attribute [local irreducible] modulus Arithmetic.Call.Endpoint.inputState
  Arithmetic.Call.Endpoint.multiplicationOutput Window.Enable.program Window.Enable.inverseProgram
  Arithmetic.Call.clearedInitial Residue.input Residue.word
  productCallOperator nativeOperator referenceKet Arithmetic.Call.branchOperator

/-- Both original normal sectors return the complete next source with one common coefficient. -/
lemma productCallOperator_residue
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address)
    (admitted : flags.2.1 = true →
      Arithmetic.Call.Endpoint.ActiveDomain (Residue.input x) (Residue.input y))
    {Reference : Register} (reference : Reference.Index) :
    (parameters.productCallOperator (services := services) store outcome anchor environment
      Reference).applyVec
        (parameters.referenceKet
          (Arithmetic.Call.Endpoint.inputState parameters.stream
            (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
            (Residue.input x) (Residue.input y) flags address)
          reference) =
      NormalizedVector.invSqrt2 ^ 256 • parameters.referenceKet
        (Arithmetic.Call.clearedInitial (Residue.input x)
          (Residue.input (if flags.2.1 then y * x else y)) flags address) reference := by
  let live : Window.Raw := Arithmetic.Call.Endpoint.inputState parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags address
  let result : Window.Raw := Arithmetic.Call.Endpoint.multiplicationOutput parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags address
  have measured := Arithmetic.Call.Endpoint.multiplication_at_anchor (services := services)
    parameters.sameWires parameters.output parameters.mask distinct parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment store
    outcome anchor (Residue.input x) (Residue.input y) flags admitted address reference
  have cleared := parameters.clearEnableOperator_original environment result reference
  have measuredLabel := parameters.referenceKet_action _ live result reference
    (NormalizedVector.invSqrt2 ^ 256) measured
  have clearedLabel := cleared.trans
    (congrArg (fun state : Window.Raw => parameters.referenceKet state reference)
      (Arithmetic.Call.Endpoint.multiplicationOutput_clear_residue parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        x y flags address))
  unfold productCallOperator
  exact measuredClear_applyVec _ _ _ _ _ _ measuredLabel clearedLabel

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
