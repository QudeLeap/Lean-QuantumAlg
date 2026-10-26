/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Native

/-!
# Native prefixes inside the original chronological instruments

The native factors keep their actual unique paths and unchanged Store.
Their already proved complete-label action can therefore be composed
with the following real instrument at that same Store. The products
retain the original right-associated circuit syntax.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling

private lemma fourFactors_associative {R : Register} (first second third fourth :
    HilbertOperator R) :
    ((fourth * third) * second) * first = fourth * (third * (second * first)) :=
  (Matrix.mul_assoc (fourth * third) second first).trans
    (Matrix.mul_assoc fourth third (second * first))

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] InstrumentBranchAction referenceKet nativeOperator modulus
  Residue.input Arithmetic.Call.clearedInitial Arithmetic.Call.Endpoint.inputState

private lemma nativeThreeThen_instrument_operator {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (first second third : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (tail : Execution.Instrument code Outcome environment)
    (store : Store ctx) (outcome : Outcome) (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      (((parameters.nativeFragmentInstrument environment first).seq
        ((parameters.nativeFragmentInstrument environment second).seq
          ((parameters.nativeFragmentInstrument environment third).seq tail))).operator
        store ((), ((), ((), outcome)))) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference (tail.operator store
        outcome) *
        (parameters.nativeOperator third environment.quantum Reference *
          (parameters.nativeOperator second environment.quantum Reference *
            parameters.nativeOperator first environment.quantum Reference)) := by
  rw [seq_reference_operator, seq_reference_operator, seq_reference_operator,
    nativeFragmentInstrument_operator, nativeFragmentInstrument_operator,
    nativeFragmentInstrument_operator]
  exact fourFactors_associative _ _ _ _

private lemma nativeFour_instrument_operator
    (first second third fourth : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (store : Store ctx) (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      (((parameters.nativeFragmentInstrument environment first).seq
        ((parameters.nativeFragmentInstrument environment second).seq
          ((parameters.nativeFragmentInstrument environment third).seq
            (parameters.nativeFragmentInstrument environment fourth)))).operator
        store ((), ((), ((), ())))) =
      parameters.nativeOperator fourth environment.quantum Reference *
        (parameters.nativeOperator third environment.quantum Reference *
          (parameters.nativeOperator second environment.quantum Reference *
            parameters.nativeOperator first environment.quantum Reference)) := by
  rw [seq_reference_operator, seq_reference_operator, seq_reference_operator,
    nativeFragmentInstrument_operator, nativeFragmentInstrument_operator,
    nativeFragmentInstrument_operator, nativeFragmentInstrument_operator]
  exact fourFactors_associative _ _ _ _

/-- Three actual native factors compose with the next instrument at its original input Store. -/
lemma nativeThreeThen_branchAction {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (first second third : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (tail : Execution.Instrument code Outcome environment)
    (store : Store ctx) (outcome : Outcome) (coefficient : Complex)
    (initial middle final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (nativeAction : HilbertOperator.applyVec
      (parameters.nativeOperator third environment.quantum Reference *
        (parameters.nativeOperator second environment.quantum Reference *
          parameters.nativeOperator first environment.quantum Reference))
      (parameters.referenceKet initial reference) = parameters.referenceKet middle reference)
    (tailAction : parameters.InstrumentBranchAction environment tail store outcome
      coefficient middle final reference) :
    parameters.InstrumentBranchAction environment
      ((parameters.nativeFragmentInstrument environment first).seq
        ((parameters.nativeFragmentInstrument environment second).seq
          ((parameters.nativeFragmentInstrument environment third).seq tail)))
      store ((), ((), ((), outcome))) coefficient initial final reference := by
  unfold InstrumentBranchAction at tailAction ⊢
  rw [nativeThreeThen_instrument_operator, HilbertOperator.mul_applyVec, nativeAction]
  exact tailAction

/-- The real multiplication prefix is followed by its existing measured call and clear. -/
lemma multiplicationNativeThen_branchAction {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (tail : Execution.Instrument code Outcome environment)
    (store : Store ctx) (outcome : Outcome) (coefficient : Complex)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (tailAction : parameters.InstrumentBranchAction environment tail store outcome coefficient
      (Arithmetic.Call.Endpoint.inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input (parameters.nativeSquareValue x y flags address)) (Residue.input y)
        (parameters.nativeNormalFlags (parameters.nativeSquareValue x y flags address)
          y flags address) address) final reference) :
    parameters.InstrumentBranchAction environment
      ((parameters.nativeFragmentInstrument environment
        (Window.Enable.program parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
        ((parameters.nativeFragmentInstrument environment
          (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).seq
          ((parameters.nativeFragmentInstrument environment Normal.program).seq tail)))
      store ((), ((), ((), outcome))) coefficient
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      final reference := by
  apply parameters.nativeThreeThen_branchAction environment _ _ _ tail store outcome
    coefficient _ _ final reference _ tailAction
  exact parameters.multiplicationNativePrefixOperator_field environment.quantum
    x y flags address reference

/-- Four original native records retain their unique outcomes and full-label action. -/
lemma nativeFour_branchAction
    (first second third fourth : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (store : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (nativeAction : HilbertOperator.applyVec
      (parameters.nativeOperator fourth environment.quantum Reference *
        (parameters.nativeOperator third environment.quantum Reference *
          (parameters.nativeOperator second environment.quantum Reference *
            parameters.nativeOperator first environment.quantum Reference)))
      (parameters.referenceKet initial reference) = parameters.referenceKet final reference) :
    parameters.InstrumentBranchAction environment
      ((parameters.nativeFragmentInstrument environment first).seq
        ((parameters.nativeFragmentInstrument environment second).seq
          ((parameters.nativeFragmentInstrument environment third).seq
            (parameters.nativeFragmentInstrument environment fourth))))
      store ((), ((), ((), ()))) 1 initial final reference := by
  unfold InstrumentBranchAction
  rw [nativeFour_instrument_operator, one_smul]
  exact nativeAction

/-- The actual reflection tail preserves the complete label beside the same reference. -/
lemma reflectionNativeInstrument_field (store : Store ctx)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment
      ((parameters.nativeFragmentInstrument environment
        (Window.Enable.program parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
        ((parameters.nativeFragmentInstrument environment Normal.inverseProgram).seq
          ((parameters.nativeFragmentInstrument environment
            (Window.suffixProgram Arithmetic.Reflect.program)).seq
            (parameters.nativeFragmentInstrument environment
              (Window.Enable.inverseProgram parameters.stream
                (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)))))
      store ((), ((), ((), ()))) 1
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (Arithmetic.Call.clearedInitial
        (Residue.input (parameters.nativeReflectionValue x y flags address)) (Residue.input y)
        (parameters.nativeNormalFlags x y flags address) address) reference := by
  apply parameters.nativeFour_branchAction environment _ _ _ _ store _ _ reference
  exact parameters.reflectionNativeTailOperator_field environment.quantum x y flags address
    reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
