/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Phases
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Product
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Outcomes
import all QuantumAlg.Core.Execution.Instrument.Vector

/-!
# Actual arithmetic instruments on every retained original path

The literal division phase and the literal multiplication/clear tail
have the same already proved full-reference matrices. Bijectivity of
the original measurement path names covers every real outcome without
discarding records or selecting a new circuit. The actual native prefix
is separate from the multiplication tail and is not inserted twice.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution EncodedBit.WindowLookup Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma seq_reference_operator {First Second : Type} [Fintype First] [Fintype Second]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment}
    (head : Execution.Instrument first First environment)
    (tail : Execution.Instrument second Second environment)
    (store : Store ctx) (firstOutcome : First) (secondOutcome : Second) (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((head.seq tail).operator store (firstOutcome, secondOutcome)) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
          (tail.operator (head.record store firstOutcome).1 secondOutcome) *
        Execution.Instrument.referenceLift (Local := ctx.register) Reference (head.operator store
          firstOutcome) :=
  Execution.referenceLift_mul _ _

variable (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] enable clearEnable

/-- The original multiplication call and its own clear, after the existing native prefix. -/
def productTailInstrument :
    Execution.Instrument
      ((parameters.arithmetic (services := services) .multiplication).seq parameters.clearEnable)
      (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
        parameters.output × Unit) environment :=
  (parameters.arithmeticFragmentInstrument environment .multiplication).seq
    (parameters.nativeFragmentInstrument environment
      (Window.Enable.inverseProgram parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound))

/-- The exact same original full-label vector equation, for an actual named instrument. -/
def InstrumentBranchAction {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false}
    (actual : Execution.Instrument code Outcome environment) (store : Store ctx) (outcome : Outcome)
    (coefficient : Complex) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  (Execution.Instrument.referenceLift (Local := ctx.register) Reference (actual.operator store
    outcome)).applyVec
      (parameters.referenceKet initial reference) =
    coefficient • parameters.referenceKet final reference

/-- Full-label actions compose at the first actual record's literal returned Store. -/
lemma instrumentBranchAction_seq {First Second : Type} [Fintype First] [Fintype Second]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    (head : Execution.Instrument first First environment)
    (tail : Execution.Instrument second Second environment)
    (store : Store ctx) (firstOutcome : First) (secondOutcome : Second)
    (firstScalar secondScalar : Complex) (initial middle final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (headAction : parameters.InstrumentBranchAction environment head store firstOutcome
      firstScalar initial middle (Reference := Reference) reference)
    (tailAction : parameters.InstrumentBranchAction environment tail
      (head.record store firstOutcome).1 secondOutcome secondScalar middle final
      (Reference := Reference) reference) :
    parameters.InstrumentBranchAction environment (head.seq tail) store
      (firstOutcome, secondOutcome) (firstScalar * secondScalar) initial final
      (Reference := Reference) reference :=
  Execution.instrument_seq_reference_applyVec head tail store firstOutcome secondOutcome Reference
    (parameters.referenceKet initial reference) (parameters.referenceKet middle reference)
    (parameters.referenceKet final reference) firstScalar secondScalar headAction tailAction

private lemma nativeFragmentInstrument_store
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum)
    (store : Store ctx) :
    ((parameters.nativeFragmentInstrument environment body).record store ()).1 = store := rfl

/-- A named actual division record has exactly the proved three-factor operator. -/
lemma divisionInstrument_operator (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.divisionInstrument environment).operator store
      ((), (Reset.outcomePath (services := services) .numerator parameters.sameWires
        parameters.output outcome anchor, ()))) =
      parameters.divisionBranchOperator (services := services)
        store outcome anchor environment.quantum Reference := by
  unfold divisionInstrument
  rw [seq_reference_operator, seq_reference_operator,
    nativeFragmentInstrument_operator, arithmeticFragmentInstrument_operator,
    nativeFragmentInstrument_operator]
  simp only [nativeFragmentInstrument_store, divisionBranchOperator, Matrix.mul_assoc]

/-- A named actual product-tail record has exactly the proved call/clear operator. -/
lemma productTailInstrument_operator (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.productTailInstrument environment).operator store
      (Reset.outcomePath (services := services) .numerator parameters.sameWires
        parameters.output outcome anchor, ())) =
      parameters.productCallOperator (services := services)
        store outcome anchor environment.quantum Reference := by
  unfold productTailInstrument
  rw [seq_reference_operator, nativeFragmentInstrument_operator,
    arithmeticFragmentInstrument_operator]
  rfl

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial
  Arithmetic.Call.Endpoint.inputState Residue.input Residue.word InstrumentBranchAction
  referenceKet divisionInstrument productTailInstrument Reset.outcomePath
  Circuit.measurementSequence resultReadouts

/-- Every real division path returns the complete initializer with the original coefficient. -/
lemma divisionInstrument_residue [Fact modulus.Prime]
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (path : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) (anchor : Window.Raw)
    (x y : ZMod modulus) (flags : Frame.Controls) (normalZero : flags.2.1 = false)
    (address : Window.Address)
    (admitted : Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input x) (Residue.input y) flags address = true →
        Arithmetic.Call.Endpoint.ActiveDomain (Residue.input x) (Residue.input y))
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment (parameters.divisionInstrument environment)
      store ((), (path, ())) (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (Arithmetic.Call.clearedInitial (Residue.input x)
        (Residue.input
          (if Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
            (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
            (Residue.input x) (Residue.input y) flags address then y / x else y))
        flags address) reference := by
  obtain ⟨outcome, same⟩ :=
    (Reset.outcomePath_bijective (services := services) .numerator
      parameters.sameWires parameters.output anchor).surjective path
  subst path
  unfold InstrumentBranchAction
  rw [divisionInstrument_operator]
  exact parameters.divisionBranchOperator_residue (services := services) (Reference := Reference)
    distinct store outcome anchor environment.quantum x y flags normalZero address
    admitted reference

/-- Every real multiplication path retains the genuine normal sector and the whole initializer. -/
lemma productTailInstrument_residue
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (path : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) (anchor : Window.Raw)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (admitted : flags.2.1 = true →
      Arithmetic.Call.Endpoint.ActiveDomain (Residue.input x) (Residue.input y))
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction environment (parameters.productTailInstrument environment)
      store (path, ()) (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.Endpoint.inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input x) (Residue.input y) flags address)
      (Arithmetic.Call.clearedInitial (Residue.input x)
        (Residue.input (if flags.2.1 then y * x else y)) flags address) reference := by
  obtain ⟨outcome, same⟩ :=
    (Reset.outcomePath_bijective (services := services) .numerator
      parameters.sameWires parameters.output anchor).surjective path
  subst path
  unfold InstrumentBranchAction
  rw [productTailInstrument_operator]
  exact parameters.productCallOperator_residue (services := services) (Reference := Reference)
    distinct store outcome anchor environment.quantum x y flags address admitted reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
