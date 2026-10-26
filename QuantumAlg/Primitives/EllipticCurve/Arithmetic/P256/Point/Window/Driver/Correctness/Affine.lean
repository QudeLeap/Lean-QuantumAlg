/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Allocation.Action
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Prepared
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification

/-!
# The specified affine action through the actual named five-table Driver

The original caller Store supplies the six real builder reads. The same
scratch frame and references supply point separation after structural
transport. Actual table preparation and the specified point certificate
are composed through their original allocator, retaining every outcome,
hidden state, physical coordinate and arbitrary reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open QuantumAlg.Execution.Instrument

open Sampling

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve.WindowTables
open QuantumAlg.ClassicalRoutines.Modular.NativePower
open Chain.Program.Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] modulus

private def kernelScratchReferences (kernel : Chain.Program.Parameters ctx)
    {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ kernel.lowWidth) → Fin parityCount) : Prop :=
  kernel.output = scratch.output ∧
  kernel.mask = scratch.mask ∧
  kernel.parity = (fun index => scratch.parity (position index)) ∧
  kernel.temporary = scratch.temporary

private lemma driverScratchReferences_transport (parameters : Driver.Parameters ctx)
    {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
    (assigned : driverScratchReferences parameters scratch position)
    {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
    (arrays : Arrays inner 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1))) :
    kernelScratchReferences (Driver.kernelParameters parameters lift same arrays)
      (scratch.transport lift) position := by
  unfold driverScratchReferences at assigned
  obtain ⟨outputSame, maskSame, paritySame, temporarySame⟩ := assigned
  unfold kernelScratchReferences
  dsimp only [Driver.kernelParameters, Storage.Frame.transport]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun output : Fin 256 → CWriteRef ctx (.finite 2) =>
      fun index => lift.liftWrite (output index)) outputSame
  · exact congrArg (fun output => lift.liftWrite output) maskSame
  · exact congrArg (fun parity : Fin (2 ^ parameters.lowWidth) → CWriteRef ctx .bit =>
      fun index => lift.liftWrite (parity index)) paritySame
  · exact congrArg (fun output => lift.liftWrite output) temporarySame

attribute [local irreducible] kernelScratchReferences

private def driverPointFieldInputs (parameters : Driver.Parameters ctx)
    {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
    (positionDistinct : Function.Injective position)
    (assigned : driverScratchReferences parameters scratch position)
    {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
    (table : TableFrame inner 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (curve : CurveSpec 256) (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (sameModulus : curve.field.modulus = modulus) :
    (Driver.kernelParameters parameters lift same table.arrays).PointFieldTableInputs := by
  have assignedInner := driverScratchReferences_transport parameters scratch position assigned
    lift same table.arrays
  unfold kernelScratchReferences at assignedInner
  with_unfolding_all
    exact pointFieldInputs_of_frame (Driver.kernelParameters parameters lift same table.arrays)
      (scratch.transport lift) position positionDistinct assignedInner.1 assignedInner.2.1
      assignedInner.2.2.1 assignedInner.2.2.2 curve table point sameModulus rfl

private def namedDriverBasisAction (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  let chosen := namedDriverInstrument (ctx := ctx) (services := services)
    parameters frame spec row environment
  letI : Fintype chosen.1 := chosen.2.1
  ∀ (hidden : services.HiddenState) (outcome : chosen.1),
    HilbertOperator.applyVec
      (referenceLift (Local := ctx.register) Reference
        (chosen.2.2.operator (before, hidden) outcome))
      (scopedReferenceKet physical same initial (Reference := Reference) reference) =
      scalar • scopedReferenceKet physical same final (Reference := Reference) reference

private def namedDriverKetAction (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  namedDriverBasisAction parameters frame spec row environment before
    (QubitLayout.canonical Window.encoding.width).toQuantum parameters.sameWires
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode initial))
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode final))
    (NormalizedVector.invSqrt2 ^ 2048) (Reference := Reference) reference

attribute [local irreducible] namedDriverInstrument tablePrefixInstrument
  Driver.kernelParameters pointProgramInstrument QueryOutcome

private def namedDriverChildAction (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ {inner : RuntimeCtx .quantum}
      (cells : Cells inner (Outer.tableShapes 256
        (2 ^ (parameters.highRemaining + parameters.lowWidth + 1))))
      (distinct : cells.Distinct) (lift : Transport ctx inner)
      (separated : cells.TransportSeparated lift)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      let table := frame.tableFrame lift cells distinct separated row
      let kernel := Driver.kernelParameters parameters lift
        (quantumLayout_wires_of_quantumWires innerSame) table.arrays
      let chosen := (tablePrefixInstrument (ctx := inner) (services := services)
        table spec environment
        (kernel.pointProgramInstrument environment).embedIdentity).pack
      letI : Fintype chosen.1 := chosen.2.1
      ∀ (current : Store inner × services.HiddenState) (outcome : chosen.1),
        lift.ReadsAs before current.1 →
        HilbertOperator.applyVec
          (referenceLift (Local := inner.register) Reference
            (chosen.2.2.operator current outcome))
          (scopedReferenceKet physical
            (same.trans (quantumLayout_wires_of_quantumWires innerSame))
            initial (Reference := Reference) reference) =
          scalar • scopedReferenceKet physical
            (same.trans (quantumLayout_wires_of_quantumWires innerSame))
            final (Reference := Reference) reference

attribute [local irreducible] namedDriverChildAction

private lemma namedDriverBasis_action (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ)
    {Reference : Register} (reference : Reference.Index)
    (childAction : namedDriverChildAction parameters frame spec row environment before
      physical same initial final scalar (Reference := Reference) reference) :
    namedDriverBasisAction parameters frame spec row environment before physical same
      initial final scalar (Reference := Reference) reference := by
  unfold namedDriverChildAction at childAction
  unfold namedDriverBasisAction namedDriverInstrument
  have retained := recordedWithCells_action (ctx := ctx) (operations := BitWord.model)
    (services := services) (environment := environment)
    (Outer.tableShapes 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    _
    (fun {inner} cells distinct lift separated same =>
      (tablePrefixInstrument (ctx := inner) (services := services)
        (frame.tableFrame lift cells distinct separated row) spec environment
        ((Driver.kernelParameters parameters lift (quantumLayout_wires_of_quantumWires same)
          (frame.tableFrame lift cells distinct separated row).arrays).pointProgramInstrument
            environment).embedIdentity).pack)
    before physical same
    initial
    final
    scalar Reference reference childAction
  exact retained

private def namedDriverChildKetAction (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  namedDriverChildAction parameters frame spec row environment before
    (QubitLayout.canonical Window.encoding.width).toQuantum parameters.sameWires
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode initial))
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode final))
    (NormalizedVector.invSqrt2 ^ 2048) (Reference := Reference) reference

attribute [local irreducible] namedDriverChildKetAction

private lemma namedDriverKet_action (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (childAction : namedDriverChildKetAction parameters frame spec row environment before
      initial final (Reference := Reference) reference) :
    namedDriverKetAction parameters frame spec row environment before initial final
      (Reference := Reference) reference := by
  unfold namedDriverChildKetAction at childAction
  unfold namedDriverKetAction
  have retained := namedDriverBasis_action parameters frame spec row environment before
    (QubitLayout.canonical Window.encoding.width).toQuantum parameters.sameWires
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode initial))
    ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
      (Window.encoding.encode final))
    (NormalizedVector.invSqrt2 ^ 2048) (Reference := Reference) reference childAction
  exact retained

private lemma pointReferenceKet_driver {inner : RuntimeCtx .quantum}
    (kernel : Chain.Program.Parameters inner) (state : Window.Raw)
    {Reference : Register} (reference : Reference.Index) :
    kernel.referenceKet state (Reference := Reference) reference =
      scopedReferenceKet (QubitLayout.canonical Window.encoding.width).toQuantum
        kernel.sameWires
        ((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
          (Window.encoding.encode state)) (Reference := Reference) reference := rfl

private lemma pointAffineBlank_driver {inner : RuntimeCtx .quantum}
    (kernel : Chain.Program.Parameters inner) (inputs : kernel.PointFieldTableInputs)
    (point : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) :
    (kernel.pointFieldState_of_affine inputs point flags).blank address =
      driverAffineBlank inputs.curve inputs.sameModulus point flags address := by
  simp only [PointFieldState.blank, driverAffineBlank,
    pointFieldState_of_affine_x, pointFieldState_of_affine_y, pointFieldState_of_affine_flags]

attribute [local irreducible] Residue.input Chain.Arithmetic.Call.clearedInitial
  Window.sourceBlank PointFieldState.blank PointFieldState.initialized
  pointFieldState_of_affine Window.Tables.selectedRow Chain.Program.Parameters.referenceKet
  driverAffineBlank driverAffineInitialized driverAffineEnabled driverSelectedRow
  driverInputValues affineRowGeometry driverScratchReferences
  namedDriverKetAction namedDriverBasisAction


private def namedDriverChildReferenceAction (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ {inner : RuntimeCtx .quantum}
      (cells : Cells inner (Outer.tableShapes 256
        (2 ^ (parameters.highRemaining + parameters.lowWidth + 1))))
      (distinct : cells.Distinct) (lift : Transport ctx inner)
      (separated : cells.TransportSeparated lift)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      let table := frame.tableFrame lift cells distinct separated row
      let kernel := Driver.kernelParameters parameters lift
        (quantumLayout_wires_of_quantumWires innerSame) table.arrays
      let chosen := (tablePrefixInstrument (ctx := inner) (services := services)
        table spec environment
        (kernel.pointProgramInstrument environment).embedIdentity).pack
      letI : Fintype chosen.1 := chosen.2.1
      ∀ (current : Store inner × services.HiddenState),
        lift.ReadsAs before current.1 → ∀ (outcome : chosen.1),
        HilbertOperator.applyVec
          (referenceLift (Local := inner.register) Reference
            (chosen.2.2.operator current outcome))
          (kernel.referenceKet initial (Reference := Reference) reference) =
          (NormalizedVector.invSqrt2 ^ 2048) •
            kernel.referenceKet final (Reference := Reference) reference

attribute [local irreducible] namedDriverChildReferenceAction

private lemma namedDriverChildReference_toKet (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (action : namedDriverChildReferenceAction parameters frame spec row environment before
      initial final (Reference := Reference) reference) :
    namedDriverChildKetAction parameters frame spec row environment before initial final
      (Reference := Reference) reference := by
  unfold namedDriverChildReferenceAction at action
  unfold namedDriverChildKetAction namedDriverChildAction
  intro inner cells distinct lift separated same
  dsimp only
  intro current outcome reads
  have actual := action cells distinct lift separated same current reads outcome
  let kernel : Chain.Program.Parameters inner := Driver.kernelParameters parameters lift
    (quantumLayout_wires_of_quantumWires same)
    (frame.tableFrame (width := 256)
      (length := 2 ^ (parameters.highRemaining + parameters.lowWidth + 1))
      lift cells distinct separated row).arrays
  have initialKet := pointReferenceKet_driver (Reference := Reference) kernel initial reference
  have finalKet := pointReferenceKet_driver (Reference := Reference) kernel final reference
  let operator : HilbertOperator (inner.register.prod Reference) :=
    referenceLift (Local := inner.register) Reference
      ((tablePrefixInstrument (ctx := inner) (services := services)
        (frame.tableFrame (width := 256)
          (length := 2 ^ (parameters.highRemaining + parameters.lowWidth + 1))
          lift cells distinct separated row) spec environment
        (kernel.pointProgramInstrument environment).embedIdentity).operator current outcome)
  exact (congrArg (fun vector : HilbertVector (inner.register.prod Reference) =>
      HilbertOperator.applyVec operator vector) initialKet.symm).trans
    (actual.trans (congrArg (fun vector : HilbertVector (inner.register.prod Reference) =>
      (NormalizedVector.invSqrt2 ^ 2048) • vector) finalKet))


attribute [local irreducible] SelectedAffineExclusions selectedSumTarget
  PreparedPointAllResultsAction tableInputValues

private def preparedDriverRawAction
    (kernel : Chain.Program.Parameters ctx) (inputs : kernel.PointFieldTableInputs)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (current : Store ctx × services.HiddenState) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ outcome,
    HilbertOperator.applyVec
      (referenceLift (Local := ctx.register) Reference
        ((tablePrefixInstrument (ctx := ctx) (services := services) inputs.frame
          inputs.curve.field environment
          (kernel.pointProgramInstrument (services := services) environment).embedIdentity
          ).operator current outcome))
      (kernel.referenceKet initial (Reference := Reference) reference) =
      (NormalizedVector.invSqrt2 ^ 2048) •
        kernel.referenceKet final (Reference := Reference) reference

attribute [local irreducible] preparedDriverRawAction

private lemma preparedDriverRawAction_of_point
    (kernel : Chain.Program.Parameters ctx) (inputs : kernel.PointFieldTableInputs)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (current : Store ctx × services.HiddenState)
    (initial final : PointFieldState) (address : Window.Address)
    (initialRaw finalRaw : Window.Raw)
    (initialSame : initial.blank address = initialRaw)
    (finalSame : final.blank address = finalRaw)
    {Reference : Register} (reference : Reference.Index)
    (action : kernel.PreparedPointAllResultsAction (ctx := ctx) (services := services)
      (Reference := Reference) environment inputs current initial final address reference) :
    preparedDriverRawAction (ctx := ctx) (services := services)
      kernel inputs environment current initialRaw finalRaw (Reference := Reference) reference := by
  unfold PreparedPointAllResultsAction at action
  unfold preparedDriverRawAction
  have initialKet := congrArg (fun state : Window.Raw =>
      kernel.referenceKet state (Reference := Reference) reference) initialSame
  have finalKet := congrArg (fun state : Window.Raw =>
      kernel.referenceKet state (Reference := Reference) reference) finalSame
  intro outcome
  have actual := action outcome
  let operator : HilbertOperator (ctx.register.prod Reference) :=
    referenceLift (Local := ctx.register) Reference
      ((tablePrefixInstrument (ctx := ctx) (services := services) inputs.frame
        inputs.curve.field environment
        (kernel.pointProgramInstrument (services := services) environment).embedIdentity
        ).operator current outcome)
  exact (congrArg (fun vector : HilbertVector (ctx.register.prod Reference) =>
      HilbertOperator.applyVec operator vector) initialKet.symm).trans
    (actual.trans (congrArg (fun vector : HilbertVector (ctx.register.prod Reference) =>
      (NormalizedVector.invSqrt2 ^ 2048) • vector) finalKet))

@[instance_reducible]
private def driverMathlibAddCommGroup {wordWidth : Nat} (curve : CurveSpec wordWidth) :
    AddCommGroup curve.curve.MathlibPoint := inferInstance

private def driverPointOrder {wordWidth : Nat} (curve : CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) : Nat :=
  addOrderOf point

private def preparedAffineExclusions (kernel : Chain.Program.Parameters ctx)
    (inputs : kernel.PointFieldTableInputs) (first : AffinePoint inputs.curve.curve)
    (flags : Frame.Controls) (address : Window.Address) : Prop :=
  kernel.SelectedAffineExclusions inputs
    (kernel.pointFieldState_of_affine inputs first flags) first address

private def preparedAffineTarget (kernel : Chain.Program.Parameters ctx)
    (inputs : kernel.PointFieldTableInputs) (first result : AffinePoint inputs.curve.curve)
    (flags : Frame.Controls) (address : Window.Address) : Prop :=
  result.toMathlib = selectedSumTarget inputs.curve first inputs.point
    (Window.Tables.selectedRow kernel.stream
      (kernel.highRemaining + kernel.lowWidth) kernel.addressBound
      ((kernel.pointFieldState_of_affine inputs first flags).initialized address)).val

attribute [local irreducible] driverPointOrder preparedAffineExclusions preparedAffineTarget

section PreparedAffineDriver

variable
    (kernel : Chain.Program.Parameters ctx) (inputs : kernel.PointFieldTableInputs)

local instance : AddCommGroup inputs.curve.curve.MathlibPoint :=
  driverMathlibAddCommGroup inputs.curve

attribute [local irreducible]
  QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve

variable
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (current : Store ctx × services.HiddenState)

variable
    (first result : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)

variable
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : driverPointOrder inputs.curve inputs.point = order)
    (tableFits : 2 ^ (kernel.highRemaining + kernel.lowWidth + 1) < order)

variable
    (values : tableInputValues inputs.frame inputs.curve inputs.point current.1)

variable
    (allowed : preparedAffineExclusions kernel inputs first flags address)

variable
    (target : preparedAffineTarget kernel inputs first result flags address)

variable
    {Reference : Register} (reference : Reference.Index)

include normalZero prime large original tableFits values allowed target in
private lemma preparedAffineDriver_action :
    preparedDriverRawAction (ctx := ctx) (services := services)
      kernel inputs environment current
      (driverAffineBlank inputs.curve inputs.sameModulus first flags address)
      (driverAffineBlank inputs.curve inputs.sameModulus result flags address)
      (Reference := Reference) reference := by
  unfold driverPointOrder at original
  unfold preparedAffineExclusions at allowed
  unfold preparedAffineTarget at target
  have prepared := kernel.preparedPointInstrument_affine_action (ctx := ctx)
    (services := services) (Reference := Reference) environment inputs current
    first result flags address normalZero order prime large original tableFits
    values allowed target reference
  have initialSame := pointAffineBlank_driver kernel inputs first flags address
  have finalSame := pointAffineBlank_driver kernel inputs result flags address
  exact preparedDriverRawAction_of_point (ctx := ctx) (services := services)
    kernel inputs environment current
    (kernel.pointFieldState_of_affine inputs first flags)
    (kernel.pointFieldState_of_affine inputs result flags) address
    (driverAffineBlank inputs.curve inputs.sameModulus first flags address)
    (driverAffineBlank inputs.curve inputs.sameModulus result flags address)
    initialSame finalSame (Reference := Reference) reference prepared

end PreparedAffineDriver

attribute [local irreducible] Outer.Frame.tableFrame


private def driverAffineChildAction
    (parameters : Driver.Parameters ctx) (frame : Outer.Frame ctx 256)
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (first result : AffinePoint curve.curve)
    (flags : Frame.Controls) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  namedDriverChildReferenceAction (ctx := ctx) (services := services)
    parameters frame curve.field row environment before
    (driverAffineBlank curve sameModulus first flags address)
    (driverAffineBlank curve sameModulus result flags address)
    (Reference := Reference) reference

attribute [local irreducible] driverAffineChildAction

private def affineCoordinateGeometry (curve : CurveSpec 256)
    (sameModulus : curve.field.modulus = modulus)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (size : Nat) (bounded : size ≤ 15)
    (first result : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) : Prop :=
  affineRowGeometry (Group := curve.curve.MathlibPoint)
    (Chain.Arithmetic.Call.Endpoint.divisionEnabled stream size bounded
      (Residue.input (MeasuredPointAddition.affineAtModulus curve sameModulus first).x)
      (Residue.input (MeasuredPointAddition.affineAtModulus curve sameModulus first).y)
      flags address)
    first.toMathlib result.toMathlib
    ((Window.Tables.selectedRow stream size bounded
      (Chain.Arithmetic.Call.clearedInitial
        (Residue.input (MeasuredPointAddition.affineAtModulus curve sameModulus first).x)
        (Residue.input (MeasuredPointAddition.affineAtModulus curve sameModulus first).y)
        flags address)).val • point)

attribute [local irreducible] affineCoordinateGeometry

private lemma preparedAffineGeometry_of_coordinates
    (kernel : Chain.Program.Parameters ctx) (inputs : kernel.PointFieldTableInputs)
    (first result : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address)
    (geometry : affineCoordinateGeometry inputs.curve inputs.sameModulus inputs.point
      kernel.stream (kernel.highRemaining + kernel.lowWidth) kernel.addressBound
      first result flags address) :
    preparedAffineExclusions kernel inputs first flags address ∧
      preparedAffineTarget kernel inputs first result flags address := by
  unfold affineCoordinateGeometry affineRowGeometry at geometry
  obtain ⟨allowed, target⟩ := geometry
  constructor
  · unfold preparedAffineExclusions SelectedAffineExclusions
    simp only [pointFieldState_of_affine_x kernel inputs first flags,
      pointFieldState_of_affine_y kernel inputs first flags,
      pointFieldState_of_affine_flags kernel inputs first flags,
      PointFieldState.initialized, nativeEnableValue]
    exact allowed
  · unfold preparedAffineTarget selectedSumTarget
    simp only [pointFieldState_of_affine_x kernel inputs first flags,
      pointFieldState_of_affine_y kernel inputs first flags,
      pointFieldState_of_affine_flags kernel inputs first flags,
      PointFieldState.initialized]
    exact target

private lemma preparedAffineDriver_of_coordinates
    (kernel : Chain.Program.Parameters ctx) (inputs : kernel.PointFieldTableInputs)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (current : Store ctx × services.HiddenState)
    (first result : AffinePoint inputs.curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : driverPointOrder inputs.curve inputs.point = order)
    (tableFits : 2 ^ (kernel.highRemaining + kernel.lowWidth + 1) < order)
    (values : tableInputValues inputs.frame inputs.curve inputs.point current.1)
    (geometry : affineCoordinateGeometry inputs.curve inputs.sameModulus inputs.point
      kernel.stream (kernel.highRemaining + kernel.lowWidth) kernel.addressBound
      first result flags address)
    {Reference : Register} (reference : Reference.Index) :
    preparedDriverRawAction (ctx := ctx) (services := services)
      kernel inputs environment current
      (driverAffineBlank inputs.curve inputs.sameModulus first flags address)
      (driverAffineBlank inputs.curve inputs.sameModulus result flags address)
      (Reference := Reference) reference := by
  have geometryValues := preparedAffineGeometry_of_coordinates kernel inputs
    first result flags address geometry
  exact preparedAffineDriver_action (ctx := ctx) (services := services)
    kernel inputs environment current first result flags address normalZero order prime large
    original tableFits values geometryValues.1 geometryValues.2 (Reference := Reference) reference

private def driverAffineGeometry (parameters : Driver.Parameters ctx)
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (first result : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) : Prop :=
  affineCoordinateGeometry curve sameModulus point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    first result flags address

attribute [local irreducible] driverAffineGeometry

section DriverChildClaim

attribute [local irreducible]
  QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve

private def driverAffineConditions (parameters : Driver.Parameters ctx)
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (first result : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (order : Nat) : Prop :=
  flags.2.1 = false ∧ order.Prime ∧ 3 < order ∧
    2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order ∧
    driverPointOrder curve point = order ∧
    driverAffineGeometry parameters curve sameModulus point first result flags address

attribute [local irreducible] driverAffineConditions

/-- The actual table-prefix and point operator on raw labels, independent of affine geometry. -/
private def constructedTableRawAction
    (kernel : Chain.Program.Parameters ctx)
    {window : Nat} (table : TableFrame ctx 256 (2 ^ window))
    (spec : ModulusSpec 256)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (current : Store ctx × services.HiddenState) (initial final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  ∀ outcome,
    HilbertOperator.applyVec
      (referenceLift (Local := ctx.register) Reference
        ((tablePrefixInstrument table spec environment
          (kernel.pointProgramInstrument (services := services) environment).embedIdentity
          ).operator current outcome))
      (kernel.referenceKet initial (Reference := Reference) reference) =
      (NormalizedVector.invSqrt2 ^ 2048) •
        kernel.referenceKet final (Reference := Reference) reference

attribute [local irreducible] constructedTableRawAction

private def constructedTableAffineStatement
    (ctx : RuntimeCtx .quantum) (services : ClassicalOracleModel) : Prop :=
  ∀ (parameters : Driver.Parameters ctx)
      {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
      (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
      (_positionDistinct : Function.Injective position)
      (_assigned : driverScratchReferences parameters scratch position)
      {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner 256
        (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
      (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
      (point : ClassicalAlgorithms.EllipticCurve.Point curve)
      (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
        services).Environment)
      (current : Store inner × services.HiddenState)
      (_values : tableInputValues table curve point current.1)
      (first result : AffinePoint curve.curve) (flags : Frame.Controls)
      (address : Window.Address) (order : Nat)
      {Reference : Register} (reference : Reference.Index)
      (_conditions : driverAffineConditions parameters curve sameModulus point
        first result flags address order),
    constructedTableRawAction
      (Driver.kernelParameters parameters lift same table.arrays) table curve.field
      environment current (driverAffineBlank curve sameModulus first flags address)
      (driverAffineBlank curve sameModulus result flags address)
      (Reference := Reference) reference

attribute [local irreducible] constructedTableAffineStatement

private lemma constructedTableAffineStatement_proof :
    constructedTableAffineStatement ctx services := by
  unfold constructedTableAffineStatement
  intro parameters parityCount scratch position positionDistinct assigned
    inner lift same table curve sameModulus point environment current values
    first result flags address order Reference reference conditions
  unfold driverAffineConditions at conditions
  obtain ⟨normalZero, prime, large, tableFits, orderProof, geometryProof⟩ := conditions
  let _ : AddCommGroup curve.curve.MathlibPoint := driverMathlibAddCommGroup curve
  let kernel : Chain.Program.Parameters inner := Driver.kernelParameters parameters lift
    same table.arrays
  let inputs : kernel.PointFieldTableInputs := driverPointFieldInputs parameters scratch
    position positionDistinct assigned lift same table curve point sameModulus
  have geometryInner : affineCoordinateGeometry inputs.curve inputs.sameModulus inputs.point
      kernel.stream (kernel.highRemaining + kernel.lowWidth) kernel.addressBound
      first result flags address := by
    unfold driverAffineGeometry at geometryProof
    simp only [kernel, inputs, Driver.kernelParameters, driverPointFieldInputs,
      pointFieldInputs_of_frame]
    with_unfolding_all
      exact geometryProof
  have orderInner : driverPointOrder inputs.curve inputs.point = order := by
    change driverPointOrder curve point = order
    exact orderProof
  have tableFitsInner : 2 ^ (kernel.highRemaining + kernel.lowWidth + 1) < order := by
    simpa only [kernel, Driver.kernelParameters] using tableFits
  have valuesInner : tableInputValues inputs.frame inputs.curve inputs.point current.1 := by
    simp only [kernel, inputs, driverPointFieldInputs, pointFieldInputs_of_frame]
    with_unfolding_all
      exact values
  have actual := preparedAffineDriver_of_coordinates (ctx := inner) (services := services)
    kernel inputs environment current first result flags address normalZero order prime large
    orderInner tableFitsInner valuesInner geometryInner (Reference := Reference) reference
  unfold preparedDriverRawAction at actual
  unfold constructedTableRawAction
  simp only [kernel, inputs, driverPointFieldInputs, pointFieldInputs_of_frame] at actual ⊢
  with_unfolding_all
    exact actual

private def namedDriverChildAffineStatement
    (ctx : RuntimeCtx .quantum) (services : ClassicalOracleModel) : Prop :=
  ∀ (parameters : Driver.Parameters ctx) (frame : Outer.Frame ctx 256)
      {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
      (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
      (_positionDistinct : Function.Injective position)
      (_assigned : driverScratchReferences parameters scratch position)
      (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
      (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)
      (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
        services).Environment)
      (before : Store ctx) (_values : driverInputValues frame curve point row before)
      (first result : AffinePoint curve.curve) (flags : Frame.Controls)
      (address : Window.Address) (_normalZero : flags.2.1 = false)
      (order : Nat) (_prime : order.Prime) (_large : 3 < order)
      (_tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)
      {Reference : Register} (reference : Reference.Index)
      (_orderProof : driverPointOrder curve point = order)
      (_geometryProof : driverAffineGeometry parameters curve sameModulus point
        first result flags address),
    namedDriverChildReferenceAction (ctx := ctx) (services := services)
      parameters frame curve.field row environment before
      (driverAffineBlank curve sameModulus first flags address)
      (driverAffineBlank curve sameModulus result flags address)
      (Reference := Reference) reference

attribute [local irreducible] namedDriverChildAffineStatement

private lemma namedDriverChildAffineStatement_proof :
    namedDriverChildAffineStatement ctx services := by
  unfold namedDriverChildAffineStatement
  intro parameters frame parityCount scratch position positionDistinct assigned
    curve sameModulus point row environment before values first result flags address
    normalZero order prime large tableFits Reference reference orderProof geometryProof
  let _ : AddCommGroup curve.curve.MathlibPoint := driverMathlibAddCommGroup curve
  unfold namedDriverChildReferenceAction
  intro inner cells distinct lift separated same
  dsimp only
  intro current reads
  let table : TableFrame inner 256
      (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)) :=
    frame.tableFrame (width := 256)
      (length := 2 ^ (parameters.highRemaining + parameters.lowWidth + 1))
      lift cells distinct separated row
  have inputValues := driverInputValues_transport (wordWidth := 256)
    (window := parameters.highRemaining + parameters.lowWidth + 1)
    frame curve point row before values lift cells distinct separated table rfl current.1 reads
  have conditions : driverAffineConditions parameters curve sameModulus point
      first result flags address order := by
    unfold driverAffineConditions
    exact ⟨normalZero, prime, large, tableFits, orderProof, geometryProof⟩
  have actual := constructedTableAffineStatement_proof (ctx := ctx) (services := services)
  unfold constructedTableAffineStatement at actual
  unfold constructedTableRawAction at actual
  exact actual parameters scratch position positionDistinct assigned lift
    (quantumLayout_wires_of_quantumWires same) table curve sameModulus point
    environment current inputValues first result flags address order
    (Reference := Reference) reference conditions

end DriverChildClaim

section DriverAffine

variable
    (parameters : Driver.Parameters ctx) (frame : Outer.Frame ctx 256)

variable
    {parityCount : Nat} (scratch : Storage.Frame ctx 256 parityCount)
    (position : Fin (2 ^ parameters.lowWidth) → Fin parityCount)
    (positionDistinct : Function.Injective position)
    (assigned : driverScratchReferences parameters scratch position)

variable
    (curve : CurveSpec 256) (sameModulus : curve.field.modulus = modulus)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve) (row : Fin 34)

local instance : AddCommGroup curve.curve.MathlibPoint :=
  driverMathlibAddCommGroup curve

attribute [local irreducible]
  QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.toWeierstrassCurve

variable
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx)
    (values : driverInputValues frame curve point row before)

variable
    (first result : AffinePoint curve.curve) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)

variable
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (tableFits : 2 ^ (parameters.highRemaining + parameters.lowWidth + 1) < order)

variable
    (geometry : affineRowGeometry
      (driverAffineEnabled parameters curve sameModulus first flags address)
      first.toMathlib result.toMathlib
      ((driverSelectedRow parameters curve sameModulus first flags address).val • point))

variable
    {Reference : Register} (reference : Reference.Index)

include positionDistinct assigned values normalZero prime large tableFits in
private lemma namedDriverChild_affine_action_core
    (orderProof : driverPointOrder curve point = order)
    (geometryProof : driverAffineGeometry parameters curve sameModulus point
      first result flags address) :
    namedDriverChildReferenceAction (ctx := ctx) (services := services)
      parameters frame curve.field row environment before
      (driverAffineBlank curve sameModulus first flags address)
      (driverAffineBlank curve sameModulus result flags address)
      (Reference := Reference) reference := by
  have actual := namedDriverChildAffineStatement_proof (ctx := ctx) (services := services)
  unfold namedDriverChildAffineStatement at actual
  exact actual parameters frame scratch position positionDistinct assigned
    curve sameModulus point row environment before values first result flags address
    normalZero order prime large tableFits (Reference := Reference) reference
    orderProof geometryProof


include positionDistinct assigned values normalZero prime large tableFits geometry in
private lemma namedDriverChild_affine_action
    (orderProof : driverPointOrder curve point = order) :
    driverAffineChildAction (ctx := ctx) (services := services)
      parameters frame curve sameModulus row environment before first result flags address
      (Reference := Reference) reference := by
  have geometryProof : driverAffineGeometry parameters curve sameModulus point
      first result flags address := by
    unfold driverAffineGeometry affineCoordinateGeometry
    simp only [driverAffineEnabled, driverSelectedRow, driverAffineInitialized] at geometry ⊢
    with_unfolding_all
      exact geometry
  unfold driverAffineChildAction
  exact namedDriverChild_affine_action_core (ctx := ctx) (services := services)
    parameters frame scratch position positionDistinct assigned curve sameModulus point row
    environment before values first result flags address normalZero order prime large
    tableFits (Reference := Reference) reference orderProof geometryProof


include positionDistinct assigned values normalZero prime large original tableFits geometry in
/-- Every outcome of the same paid named Driver reaches the specified affine group target. -/
lemma namedDriverInstrument_affine_action :
    namedDriverKetAction (ctx := ctx) (services := services) parameters frame
      curve.field row environment before
      (driverAffineBlank curve sameModulus first flags address)
      (driverAffineBlank curve sameModulus result flags address) (Reference := Reference)
      reference := by
  have orderProof : driverPointOrder curve point = order := by
    unfold driverPointOrder
    exact original
  have child := namedDriverChild_affine_action (ctx := ctx) (services := services)
    parameters frame scratch position positionDistinct assigned curve sameModulus point row
    environment before values first result flags address normalZero order prime large
    tableFits geometry (Reference := Reference) reference orderProof
  unfold driverAffineChildAction at child
  have childKet := namedDriverChildReference_toKet (ctx := ctx) (services := services)
    parameters frame curve.field row environment before
    (driverAffineBlank curve sameModulus first flags address)
    (driverAffineBlank curve sameModulus result flags address) (Reference := Reference) reference
    child
  have retained := namedDriverKet_action (ctx := ctx) (services := services)
    parameters frame curve.field row environment before
    (driverAffineBlank curve sameModulus first flags address)
    (driverAffineBlank curve sameModulus result flags address) (Reference := Reference) reference
    childKet
  exact retained

end DriverAffine

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
