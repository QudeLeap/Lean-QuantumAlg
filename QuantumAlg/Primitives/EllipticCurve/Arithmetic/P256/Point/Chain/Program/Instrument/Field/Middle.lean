/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Queries.Tables
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Field.Domain

/-!
# The two actual middle phases on their complete original labels

The multiplication phase uses the existing query, enable, square,
genuine normal flag, measured call and clear. The reflection phase uses
its real exceptional query before the matched inverse normal and retained
enable reflection. Each component reads its literal predecessor Store.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial Residue.input
  Arithmetic.Call.Endpoint.inputState InstrumentBranchAction queryFieldNext referenceKet


private lemma twoFactors_power {R : Register}
    (first second : HilbertOperator R)
    (initial middle final : HilbertVector R) (firstPower secondPower : Nat)
    (firstAction : first.applyVec initial =
      NormalizedVector.invSqrt2 ^ firstPower • middle)
    (secondAction : second.applyVec middle =
      NormalizedVector.invSqrt2 ^ secondPower • final) :
    HilbertOperator.applyVec (second * first) initial =
      NormalizedVector.invSqrt2 ^ (firstPower + secondPower) • final := by
  rw [HilbertOperator.mul_applyVec, firstAction,
    HilbertOperator.applyVec_smul, secondAction, smul_smul, ← pow_add]

private def middleCoordinates (occurrence : Fin 6)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    ZMod modulus × ZMod modulus :=
  let initial := Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address
  let column := Window.Tables.selectedFieldColumn curve point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound initial
    (Window.QueryColumns.column occurrence)
  parameters.queryFieldNext occurrence x y column flags address

private def middleInitialized (occurrence : Fin 6)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let first := parameters.middleCoordinates occurrence curve point x y flags address
  Arithmetic.Call.clearedInitial (Residue.input first.1) (Residue.input first.2) flags address

private def multiplicationNativeOutput (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  let square := parameters.nativeSquareValue x y flags address
  let normal := parameters.nativeNormalFlags square y flags address
  Arithmetic.Call.clearedInitial (Residue.input square)
    (Residue.input (if normal.2.1 then y * square else y)) normal address

private def reflectionNativeOutput (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Arithmetic.Call.clearedInitial
    (Residue.input (parameters.nativeReflectionValue x y flags address)) (Residue.input y)
    (parameters.nativeNormalFlags x y flags address) address

private def multiplicationRemainder :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.native (services := services)
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
    ((parameters.native (services := services)
      (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).seq
      ((parameters.native (services := services) Normal.program).seq
        ((parameters.arithmetic (services := services) .multiplication).seq
          parameters.clearEnable)))

private def reflectionRemainder :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (parameters.native (services := services)
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
    ((parameters.native (services := services) Normal.inverseProgram).seq
      ((parameters.native (services := services)
        (Window.suffixProgram Arithmetic.Reflect.program)).seq
        (parameters.native (services := services)
          (Window.Enable.inverseProgram parameters.stream
            (parameters.highRemaining + parameters.lowWidth) parameters.addressBound))))

private def multiplicationRemainderInstrument :
    Execution.Instrument (parameters.multiplicationRemainder (services := services))
      (Unit × (Unit × (Unit ×
        (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
          parameters.output × Unit)))) environment := by
  unfold multiplicationRemainder
  exact (parameters.nativeFragmentInstrument environment
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
    ((parameters.nativeFragmentInstrument environment
      (Window.suffixProgram Native.BorrowedControl.subtractSquareProgram)).seq
      ((parameters.nativeFragmentInstrument environment Normal.program).seq
        (parameters.productTailInstrument environment)))

private def reflectionRemainderInstrument :
    Execution.Instrument (parameters.reflectionRemainder (services := services))
      (Unit × (Unit × (Unit × Unit))) environment := by
  unfold reflectionRemainder
  exact (parameters.nativeFragmentInstrument environment
    (Window.Enable.program parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound)).seq
    ((parameters.nativeFragmentInstrument environment Normal.inverseProgram).seq
      ((parameters.nativeFragmentInstrument environment
        (Window.suffixProgram Arithmetic.Reflect.program)).seq
        (parameters.nativeFragmentInstrument environment
          (Window.Enable.inverseProgram parameters.stream
            (parameters.highRemaining + parameters.lowWidth) parameters.addressBound))))

attribute [local irreducible] multiplicationRemainder reflectionRemainder

attribute [local irreducible] middleCoordinates middleInitialized multiplicationNativeOutput
  reflectionNativeOutput

private lemma productTail_normal_field
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus)
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (path : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) (anchor : Window.Raw)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) {Reference : Register} (reference : Reference.Index) :
    let square := parameters.nativeSquareValue x y flags address
    let normal := parameters.nativeNormalFlags square y flags address
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.productTailInstrument environment) store (path, ())
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.Endpoint.inputState parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
        (Residue.input square) (Residue.input y) normal address)
      (Arithmetic.Call.clearedInitial (Residue.input square)
        (Residue.input (if normal.2.1 then y * square else y)) normal address) reference := by
  dsimp only
  let square := parameters.nativeSquareValue x y flags address
  let normal := parameters.nativeNormalFlags square y flags address
  have admitted : normal.2.1 = true → Arithmetic.Call.Endpoint.ActiveDomain
      (Residue.input square) (Residue.input y) := by
    let : Fact modulus.Prime := ⟨by
      rw [← sameModulus]
      exact curve.curve.prime⟩
    exact parameters.nativeNormalFlags_activeDomain square y flags address normalZero
  exact parameters.productTailInstrument_residue (Reference := Reference)
    environment distinct store path anchor square y normal address admitted reference

private def productPath
    (path : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) :
    Unit × (Unit × (Unit ×
      (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
        parameters.output × Unit))) :=
  ((), ((), ((), (path, ()))))

private def multiplicationPath (path : parameters.QueryOutcome (services := services) 2)
    (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) :
    parameters.QueryOutcome (services := services) 2 × (Unit × (Unit × (Unit ×
      (Reset.Instrument.Outcome (services := services) .numerator parameters.sameWires
        parameters.output × Unit)))) :=
  (path, parameters.productPath callPath)

private def reflectionTailPath : Unit × (Unit × (Unit × Unit)) := ((), ((), ((), ())))

private def reflectionPath (path : parameters.QueryOutcome (services := services) 3) :
    parameters.QueryOutcome (services := services) 3 × (Unit × (Unit × (Unit × Unit))) :=
  (path, reflectionTailPath)

private lemma multiplicationMiddle_operator (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 2)
    (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.multiplicationInstrument environment).operator
        store (parameters.multiplicationPath path callPath)) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.multiplicationRemainderInstrument environment).operator
          ((parameters.queryFragmentInstrument environment 2).record store path).1
          (parameters.productPath callPath)) *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 2).operator store path) := by
  unfold multiplicationInstrument multiplicationRemainderInstrument productTailInstrument
  exact Execution.referenceLift_mul _ _

private lemma multiplicationMiddle_action (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 2)
    (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (firstAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 2) store path
      (NormalizedVector.invSqrt2 ^ 256) initial middle reference)
    (lastAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.multiplicationRemainderInstrument environment)
      ((parameters.queryFragmentInstrument environment 2).record store path).1
      (parameters.productPath callPath)
      (NormalizedVector.invSqrt2 ^ 256) middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.multiplicationInstrument environment)
      store (parameters.multiplicationPath path callPath)
      (NormalizedVector.invSqrt2 ^ 512) initial final reference := by
  unfold InstrumentBranchAction at firstAction lastAction ⊢
  rw [parameters.multiplicationMiddle_operator environment store path callPath Reference]
  exact twoFactors_power (R := ctx.register.prod Reference) _ _
    (parameters.referenceKet initial reference) (parameters.referenceKet middle reference)
    (parameters.referenceKet final reference) 256 256 firstAction
    lastAction

private lemma reflectionMiddle_operator (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 3)
    (Reference : Register) :
    Execution.Instrument.referenceLift (Local := ctx.register) Reference
      ((parameters.reflectionInstrument environment).operator
        store (parameters.reflectionPath path)) =
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.reflectionRemainderInstrument environment).operator
          ((parameters.queryFragmentInstrument environment 3).record store path).1
          reflectionTailPath) *
      Execution.Instrument.referenceLift (Local := ctx.register) Reference
        ((parameters.queryFragmentInstrument environment 3).operator store path) := by
  unfold reflectionInstrument reflectionRemainderInstrument
  exact Execution.referenceLift_mul _ _

private lemma reflectionMiddle_action (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 3)
    (initial middle final : Window.Raw) {Reference : Register} (reference : Reference.Index)
    (firstAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment 3) store path
      (NormalizedVector.invSqrt2 ^ 256) initial middle reference)
    (lastAction : parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.reflectionRemainderInstrument environment)
      ((parameters.queryFragmentInstrument environment 3).record store path).1
      reflectionTailPath
      1 middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.reflectionInstrument environment)
      store (parameters.reflectionPath path)
      (NormalizedVector.invSqrt2 ^ 256) initial final reference := by
  unfold InstrumentBranchAction at firstAction lastAction ⊢
  rw [parameters.reflectionMiddle_operator environment store path Reference]
  exact twoFactors_power (R := ctx.register.prod Reference) _ _
    (parameters.referenceKet initial reference) (parameters.referenceKet middle reference)
    (parameters.referenceKet final reference) 256 0 firstAction
    (by simpa only [pow_zero] using lastAction)

private lemma middleQuery_table
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (occurrence : Fin 6) (separation : parameters.QueryFieldSeparation occurrence)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.queryFragmentInstrument environment occurrence) store path
      (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.middleInitialized occurrence curve point x y flags address) reference := by
  unfold middleInitialized middleCoordinates
  exact parameters.queryInstrument_table_residue (Reference := Reference)
    environment curve frame point sameModulus arrays store values occurrence separation
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    path x y flags address reference

private lemma multiplicationRemainder_field
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus)
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (store : Store ctx) (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output) (anchor : Window.Raw)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.multiplicationRemainderInstrument environment) store
      (parameters.productPath callPath) (NormalizedVector.invSqrt2 ^ 256)
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.multiplicationNativeOutput x y flags address) reference := by
  unfold multiplicationRemainderInstrument multiplicationNativeOutput
  have actual := parameters.multiplicationNativeThen_branchAction (Reference := Reference)
    environment (parameters.productTailInstrument environment) store (callPath, ())
    (NormalizedVector.invSqrt2 ^ 256) x y flags address _ reference
    (parameters.productTail_normal_field (Reference := Reference)
      environment curve sameModulus distinct store callPath anchor x y flags address
      normalZero reference)
  unfold InstrumentBranchAction multiplicationRemainder
  simpa only [InstrumentBranchAction, productPath, id] using actual

private lemma reflectionRemainder_field (store : Store ctx)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.reflectionRemainderInstrument environment) store
      reflectionTailPath 1
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.reflectionNativeOutput x y flags address) reference := by
  unfold reflectionRemainderInstrument reflectionNativeOutput
  have actual := parameters.reflectionNativeInstrument_field (Reference := Reference)
    environment store x y flags address reference
  unfold InstrumentBranchAction reflectionRemainder
  simpa only [InstrumentBranchAction, reflectionTailPath, id] using actual

private def MultiplicationFieldAction
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 2)
    (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  let first := parameters.middleCoordinates 2 curve point x y flags address
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.multiplicationInstrument environment)
      store (parameters.multiplicationPath path callPath)
    (NormalizedVector.invSqrt2 ^ 512)
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.multiplicationNativeOutput first.1 first.2 flags address) reference

attribute [local irreducible] MultiplicationFieldAction

/-- The actual multiplication phase retains the complete label, original paths and reference. -/
lemma multiplicationInstrument_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (distinct : Function.Injective fun index => (parameters.output index).key)
    (separation : parameters.QueryFieldSeparation 2)
    (path : parameters.QueryOutcome (services := services) 2)
    (callPath : Reset.Instrument.Outcome (services := services) .numerator
      parameters.sameWires parameters.output)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (normalZero : flags.2.1 = false) {Reference : Register} (reference : Reference.Index) :
    parameters.MultiplicationFieldAction (Reference := Reference) environment
      curve point store path callPath x y flags address reference := by
  unfold MultiplicationFieldAction
  dsimp only
  refine parameters.multiplicationMiddle_action (Reference := Reference)
    environment store path callPath
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.middleInitialized 2 curve point x y flags address)
    (parameters.multiplicationNativeOutput
      (parameters.middleCoordinates 2 curve point x y flags address).1
      (parameters.middleCoordinates 2 curve point x y flags address).2 flags address)
    reference ?_ ?_
  · exact parameters.middleQuery_table (Reference := Reference)
      environment curve frame point sameModulus arrays store values 2 separation path
      x y flags address reference
  · unfold middleInitialized
    exact parameters.multiplicationRemainder_field (Reference := Reference)
      environment curve sameModulus distinct
      ((parameters.queryFragmentInstrument environment 2).record store path).1
      callPath
      (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
      (parameters.middleCoordinates 2 curve point x y flags address).1
      (parameters.middleCoordinates 2 curve point x y flags address).2 flags address
      normalZero reference

private def ReflectionFieldAction
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (store : Store ctx)
    (path : parameters.QueryOutcome (services := services) 3)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  let first := parameters.middleCoordinates 3 curve point x y flags address
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.reflectionInstrument environment)
      store (parameters.reflectionPath path)
    (NormalizedVector.invSqrt2 ^ 256)
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.reflectionNativeOutput first.1 first.2 flags address) reference

attribute [local irreducible] ReflectionFieldAction

/-- The actual reflection phase retains the complete label, original paths and reference. -/
lemma reflectionInstrument_table_residue
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (frame : TableFrame ctx 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) (arrays : parameters.arrays = frame.arrays)
    (store : Store ctx) (values : TableFrame.TableValue curve frame point store)
    (separation : parameters.QueryFieldSeparation 3)
    (path : parameters.QueryOutcome (services := services) 3)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.ReflectionFieldAction (Reference := Reference) environment
      curve point store path x y flags address reference := by
  unfold ReflectionFieldAction
  dsimp only
  refine parameters.reflectionMiddle_action (Reference := Reference)
    environment store path
    (Arithmetic.Call.clearedInitial (Residue.input x) (Residue.input y) flags address)
    (parameters.middleInitialized 3 curve point x y flags address)
    (parameters.reflectionNativeOutput
      (parameters.middleCoordinates 3 curve point x y flags address).1
      (parameters.middleCoordinates 3 curve point x y flags address).2 flags address)
    reference ?_ ?_
  · exact parameters.middleQuery_table (Reference := Reference)
      environment curve frame point sameModulus arrays store values 3 separation path
      x y flags address reference
  · unfold middleInitialized
    exact parameters.reflectionRemainder_field (Reference := Reference)
      environment
      ((parameters.queryFragmentInstrument environment 3).record store path).1
      (parameters.middleCoordinates 3 curve point x y flags address).1
      (parameters.middleCoordinates 3 curve point x y flags address).2 flags address
      reference

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
