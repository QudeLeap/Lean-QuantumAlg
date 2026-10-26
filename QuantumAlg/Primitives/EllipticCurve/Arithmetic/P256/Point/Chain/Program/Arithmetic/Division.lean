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
# Original complete field action of the real enabled division fragment

The ordered factors are the actual native enable, the actual measured
division call and the actual native inverse enable. The same real Store,
outcome path and external reference are retained. The common coefficient
does not depend on the digit, coordinates or original reference label.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

/-- The actual ordered three-fragment operator for one retained division outcome. -/
def divisionBranchOperator (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (ctx.register.prod Reference) :=
  parameters.nativeOperator
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
      environment Reference *
    (Arithmetic.Call.branchOperator (services := services) parameters.sameWires parameters.output
        parameters.mask .division parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound store
        (Reset.outcomePath (services := services) .numerator parameters.sameWires parameters.output
          outcome anchor) environment Reference *
      parameters.nativeOperator
        (Window.Enable.program parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)
        environment Reference)

attribute [local implicit_reducible] capacity width

attribute [local irreducible] modulus Arithmetic.Call.Endpoint.inputState
  Arithmetic.Call.Endpoint.divisionOutput Window.Enable.program Window.Enable.inverseProgram
  Arithmetic.Call.clearedInitial Residue.input Residue.word
  divisionBranchOperator nativeOperator referenceKet Arithmetic.Call.branchOperator

/-- The real fragment returns the exact next initializer beside the same original reference. -/
lemma divisionBranchOperator_residue [Fact modulus.Prime]
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (x y : ZMod modulus)
    (flags : Frame.Controls) (normalZero : flags.2.1 = false) (address : Window.Address)
    (admitted : Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input x) (Residue.input y) flags address = true →
        Arithmetic.Call.Endpoint.ActiveDomain (Residue.input x) (Residue.input y))
    {Reference : Register} (reference : Reference.Index) :
    (parameters.divisionBranchOperator (services := services) store outcome anchor environment
      Reference).applyVec
        (parameters.referenceKet
          (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
          reference) =
      NormalizedVector.invSqrt2 ^ 256 • parameters.referenceKet
        (Arithmetic.Call.clearedInitial (Residue.input x)
          (Residue.input
            (if Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
              (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
              (Residue.input x) (Residue.input y) flags address then y / x else y))
          flags address) reference := by
  let initial : Window.Raw :=
    Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let live : Window.Raw := Arithmetic.Call.Endpoint.inputState parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags address
  let result : Window.Raw := Arithmetic.Call.Endpoint.divisionOutput parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input x) (Residue.input y) flags address admitted
  have enabledLabel : Window.Enable.step parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial = live :=
    (Arithmetic.Call.Endpoint.inputState_eq parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input x) (Residue.input y) flags address).symm
  have prepared := parameters.enableOperator_original environment initial reference
  have measured := Arithmetic.Call.Endpoint.division_at_anchor (services := services)
    parameters.sameWires parameters.output parameters.mask distinct parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound environment store
    outcome anchor (Residue.input x) (Residue.input y) flags normalZero address admitted reference
  have cleared := parameters.clearEnableOperator_original environment result reference
  have preparedLabel := prepared.trans
    (congrArg (fun state : Window.Raw => parameters.referenceKet state reference) enabledLabel)
  have measuredLabel := parameters.referenceKet_action _ live result reference
    (NormalizedVector.invSqrt2 ^ 256) measured
  have clearedLabel := cleared.trans
    (congrArg (fun state : Window.Raw => parameters.referenceKet state reference)
      (Arithmetic.Call.Endpoint.divisionOutput_clear_residue parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        x y flags normalZero address admitted))
  unfold divisionBranchOperator
  exact measuredFactors_applyVec _ _ _ _ _ _ _ _ preparedLabel measuredLabel clearedLabel

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
