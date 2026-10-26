/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Compose
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Finish
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Middle
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store.Stages

/-!
# The complete actual point action from its five proved field phases

The retained table is transported through four literal intermediate
records. Each phase then receives its own original measured paths and
the full output label of its predecessor. The first division uses only
its original conditional arithmetic domain; affine callers must prove
that domain from their original allowed input. No whole-point action
or probability certificate is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input Arithmetic.Call.clearedInitial
  Window.sourceBlank InstrumentBranchAction referenceKet

/-- Internal static table ownership and the original feedback-write separation. -/
structure PointFieldTableInputs (parameters : Parameters ctx) where
  curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256
  frame : TableFrame ctx 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1))
  point : ClassicalAlgorithms.EllipticCurve.Point curve
  sameModulus : curve.field.modulus = modulus
  arrays : parameters.arrays = frame.arrays
  distinct : Function.Injective fun index => (parameters.output index).key
  separation : ∀ occurrence, parameters.QueryFieldSeparation occurrence
  outputFree : ∀ index column, (parameters.output index).key ∉
    (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys
  maskFree : ∀ column, parameters.mask.key ∉
    (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys
  parityFree : ∀ index column, (parameters.parity index).key ∉
    (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys
  temporaryFree : ∀ column, parameters.temporary.key ∉
    (CInputRef.storage (frame.finishColumns column).toCStorageRef).storageKeys

/-- Exactly the six query paths and two arithmetic paths of the original program. -/
structure PointFieldPaths (parameters : Parameters ctx) (services : ClassicalOracleModel) where
  query : (occurrence : Fin 6) → parameters.QueryOutcome (services := services) occurrence
  division : Reset.Instrument.Outcome (services := services) .numerator
    parameters.sameWires parameters.output
  multiplication : Reset.Instrument.Outcome (services := services) .numerator
    parameters.sameWires parameters.output

private structure PointFieldState where
  x : ZMod modulus
  y : ZMod modulus
  flags : Frame.Controls

private def PointFieldState.initialized (state : PointFieldState)
    (address : Window.Address) : Window.Raw :=
  Arithmetic.Call.clearedInitial (Residue.input state.x) (Residue.input state.y) state.flags address

private def PointFieldState.blank (state : PointFieldState)
    (address : Window.Address) : Window.Raw :=
  Window.sourceBlank (Residue.input state.x) (Residue.input state.y) state.flags address

variable (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def PointFieldPaths.first (paths : PointFieldPaths parameters services) :=
  ((), (paths.query 0, paths.query 1))

private def PointFieldPaths.second (paths : PointFieldPaths parameters services) :=
  ((), (paths.division, ()))

private def PointFieldPaths.third (paths : PointFieldPaths parameters services) :=
  parameters.multiplicationPath (paths.query 2) paths.multiplication

private def PointFieldPaths.fourth (paths : PointFieldPaths parameters services) :=
  parameters.reflectionPath (paths.query 3)

private def PointFieldPaths.fifth (paths : PointFieldPaths parameters services) :=
  (paths.query 4, (paths.query 5, ()))

private def PointFieldPaths.complete (paths : PointFieldPaths parameters services) :=
  (paths.first parameters,
    (paths.second parameters,
      (paths.third parameters, (paths.fourth parameters, paths.fifth parameters))))

private def firstFieldState (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.differencesFirstCoordinates inputs.curve inputs.point
      state.x state.y state.flags address
  let initial : Window.Raw := state.initialized address
  let column : ZMod modulus := Window.Tables.selectedFieldColumn
    inputs.curve inputs.point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    initial (Window.QueryColumns.column (1 : Fin 6))
  let final : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 1 first.1 first.2 column state.flags address
  PointFieldState.mk final.1 final.2 state.flags
private def secondFieldState (state : PointFieldState) (address : Window.Address) :
    PointFieldState :=
  let enabled : Bool := parameters.nativeEnableValue state.x state.y state.flags address
  let quotient : ZMod modulus := if enabled then state.y * state.x⁻¹ else state.y
  PointFieldState.mk state.x quotient state.flags

private def thirdFieldState (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.middleCoordinates 2 inputs.curve inputs.point
      state.x state.y state.flags address
  let square : ZMod modulus := parameters.nativeSquareValue first.1 first.2 state.flags address
  let normal : Frame.Controls := parameters.nativeNormalFlags square first.2 state.flags address
  let product : ZMod modulus := if normal.2.1 then first.2 * square else first.2
  PointFieldState.mk square product normal

private def fourthFieldState (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : PointFieldState :=
  let first := parameters.middleCoordinates 3 inputs.curve inputs.point
    state.x state.y state.flags address
  ⟨parameters.nativeReflectionValue first.1 first.2 state.flags address,
    first.2, parameters.nativeNormalFlags first.1 first.2 state.flags address⟩

private def fifthFieldState (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : PointFieldState :=
  let final := parameters.finishLastCoordinates inputs.curve inputs.point
    state.x state.y state.flags address
  ⟨final.1, final.2, state.flags⟩

attribute [local irreducible] PointFieldState.initialized
  PointFieldState.blank firstFieldState secondFieldState thirdFieldState fourthFieldState
  fifthFieldState PointFieldPaths.first PointFieldPaths.second PointFieldPaths.third
  PointFieldPaths.fourth PointFieldPaths.fifth PointFieldPaths.complete

private lemma firstFieldState_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.differencesInstrument environment) store (paths.first parameters)
      (NormalizedVector.invSqrt2 ^ 512) (state.blank address)
      ((parameters.firstFieldState inputs state address).initialized address) reference := by
  have actual := parameters.differencesInstrument_table_residue (Reference := Reference)
    environment inputs.curve inputs.frame inputs.point inputs.sameModulus inputs.arrays
    store values (inputs.separation 0) (inputs.separation 1)
    inputs.outputFree inputs.maskFree inputs.parityFree inputs.temporaryFree
    (paths.query 0) (paths.query 1) state.x state.y state.flags address reference
  simpa only [DifferencesFieldAction, sourceFieldBlank, differencesFieldFinal,
    firstFieldState, PointFieldState.initialized, PointFieldState.blank,
    PointFieldPaths.first] using actual

private lemma secondFieldState_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx) (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) (normalZero : state.flags.2.1 = false)
    (admitted : Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input state.x) (Residue.input state.y) state.flags address = true →
        Arithmetic.Call.Endpoint.ActiveDomain (Residue.input state.x) (Residue.input state.y))
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.divisionInstrument environment) store (paths.second parameters)
      (NormalizedVector.invSqrt2 ^ 256) (state.initialized address)
      ((parameters.secondFieldState state address).initialized address) reference := by
  let : Fact modulus.Prime := ⟨by
    rw [← inputs.sameModulus]
    exact inputs.curve.curve.prime⟩
  have actual := parameters.divisionInstrument_residue (Reference := Reference)
    environment inputs.distinct store paths.division (state.initialized address)
    state.x state.y state.flags normalZero address admitted reference
  simp only [PointFieldState.initialized, PointFieldPaths.second, secondFieldState,
    nativeEnableValue, div_eq_mul_inv] at actual ⊢
  with_unfolding_all exact actual

private lemma thirdFieldState_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) (normalZero : state.flags.2.1 = false)
    {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.multiplicationInstrument environment) store (paths.third parameters)
      (NormalizedVector.invSqrt2 ^ 512) (state.initialized address)
      ((parameters.thirdFieldState inputs state address).initialized address) reference := by
  have actual := parameters.multiplicationInstrument_table_residue (Reference := Reference)
    environment inputs.curve inputs.frame inputs.point inputs.sameModulus inputs.arrays
    store values inputs.distinct (inputs.separation 2) (paths.query 2) paths.multiplication
    state.x state.y state.flags address normalZero reference
  simpa only [MultiplicationFieldAction, thirdFieldState, multiplicationNativeOutput,
    PointFieldState.initialized, PointFieldPaths.third] using actual

private lemma fourthFieldState_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.reflectionInstrument environment) store (paths.fourth parameters)
      (NormalizedVector.invSqrt2 ^ 256) (state.initialized address)
      ((parameters.fourthFieldState inputs state address).initialized address) reference := by
  have actual := parameters.reflectionInstrument_table_residue (Reference := Reference)
    environment inputs.curve inputs.frame inputs.point inputs.sameModulus inputs.arrays
    store values (inputs.separation 3) (paths.query 3)
    state.x state.y state.flags address reference
  simpa only [ReflectionFieldAction, fourthFieldState, reflectionNativeOutput,
    PointFieldState.initialized, PointFieldPaths.fourth] using actual

private lemma fifthFieldState_action (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index) :
    parameters.InstrumentBranchAction (Reference := Reference) environment
      (parameters.finishInstrument environment) store (paths.fifth parameters)
      (NormalizedVector.invSqrt2 ^ 512) (state.initialized address)
      ((parameters.fifthFieldState inputs state address).blank address) reference := by
  have actual := parameters.finishInstrument_table_residue (Reference := Reference)
    environment inputs.curve inputs.frame inputs.point inputs.sameModulus inputs.arrays
    store values (inputs.separation 4) (inputs.separation 5)
    inputs.outputFree inputs.maskFree inputs.parityFree inputs.temporaryFree
    (paths.query 4) (paths.query 5) state.x state.y state.flags address reference
  simpa only [FinishFieldAction, fifthFieldState, finishFieldBlank,
    PointFieldState.initialized, PointFieldState.blank, PointFieldPaths.fifth] using actual

private lemma firstRecord_tableValue (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) :
    TableFrame.TableValue inputs.curve inputs.frame inputs.point
      ((parameters.differencesInstrument environment).record store (paths.first parameters)).1 := by
  exact instrument_tableValue _ inputs.curve inputs.frame inputs.point store values
    (fun column => parameters.differencesInstrument_read environment _
      (fun index => inputs.outputFree index column) (inputs.maskFree column)
      (fun index => inputs.parityFree index column) (inputs.temporaryFree column)) _

private lemma secondRecord_tableValue (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) :
    TableFrame.TableValue inputs.curve inputs.frame inputs.point
      ((parameters.divisionInstrument environment).record store (paths.second parameters)).1 := by
  exact instrument_tableValue _ inputs.curve inputs.frame inputs.point store values
    (fun column => parameters.divisionInstrument_read environment _
      (fun index => inputs.outputFree index column) (inputs.maskFree column)) _

private lemma thirdRecord_tableValue (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) :
    TableFrame.TableValue inputs.curve inputs.frame inputs.point
      ((parameters.multiplicationInstrument environment).record
        store (paths.third parameters)).1 := by
  exact instrument_tableValue _ inputs.curve inputs.frame inputs.point store values
    (fun column => parameters.multiplicationInstrument_read environment _
      (fun index => inputs.outputFree index column) (inputs.maskFree column)
      (fun index => inputs.parityFree index column) (inputs.temporaryFree column)) _

private lemma fourthRecord_tableValue (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) :
    TableFrame.TableValue inputs.curve inputs.frame inputs.point
      ((parameters.reflectionInstrument environment).record store (paths.fourth parameters)).1 := by
  exact instrument_tableValue _ inputs.curve inputs.frame inputs.point store values
    (fun column => parameters.reflectionInstrument_read environment _
      (fun index => inputs.outputFree index column) (inputs.maskFree column)
      (fun index => inputs.parityFree index column) (inputs.temporaryFree column)) _

private def completeFieldState (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : PointFieldState :=
  let first := parameters.firstFieldState inputs state address
  let second := parameters.secondFieldState first address
  let third := parameters.thirdFieldState inputs second address
  let fourth := parameters.fourthFieldState inputs third address
  parameters.fifthFieldState inputs fourth address

private def CompletePointFieldAction (inputs : PointFieldTableInputs parameters)
    (store : Store ctx) (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) {Reference : Register} (reference : Reference.Index) : Prop :=
  parameters.InstrumentBranchAction (Reference := Reference) environment
    (parameters.pointProgramInstrument environment) store (paths.complete parameters)
    (NormalizedVector.invSqrt2 ^ 2048) (state.blank address)
    ((parameters.completeFieldState inputs state address).blank address) reference

attribute [local irreducible] completeFieldState CompletePointFieldAction

/-- All five actual phase actions follow internally from the same retained paid table. -/
lemma pointProgramInstrument_table_fieldTrace (inputs : PointFieldTableInputs parameters)
    (store : Store ctx)
    (values : TableFrame.TableValue inputs.curve inputs.frame inputs.point store)
    (paths : PointFieldPaths parameters services) (state : PointFieldState)
    (address : Window.Address) (normalZero : state.flags.2.1 = false)
    (admitted : Arithmetic.Call.Endpoint.divisionEnabled parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (Residue.input (parameters.firstFieldState inputs state address).x)
      (Residue.input (parameters.firstFieldState inputs state address).y)
      (parameters.firstFieldState inputs state address).flags address = true →
        Arithmetic.Call.Endpoint.ActiveDomain
          (Residue.input (parameters.firstFieldState inputs state address).x)
          (Residue.input (parameters.firstFieldState inputs state address).y))
    {Reference : Register} (reference : Reference.Index) :
    parameters.CompletePointFieldAction (Reference := Reference)
      environment inputs store paths state address reference := by
  let first := parameters.firstFieldState inputs state address
  let second := parameters.secondFieldState first address
  let third := parameters.thirdFieldState inputs second address
  let fourth := parameters.fourthFieldState inputs third address
  let store1 := ((parameters.differencesInstrument environment).record
    store (paths.first parameters)).1
  let store2 := ((parameters.divisionInstrument environment).record
    store1 (paths.second parameters)).1
  let store3 := ((parameters.multiplicationInstrument environment).record
    store2 (paths.third parameters)).1
  let store4 := ((parameters.reflectionInstrument environment).record
    store3 (paths.fourth parameters)).1
  have values1 := parameters.firstRecord_tableValue environment inputs store values paths
  have values2 := parameters.secondRecord_tableValue environment inputs store1 values1 paths
  have values3 := parameters.thirdRecord_tableValue environment inputs store2 values2 paths
  have values4 := parameters.fourthRecord_tableValue environment inputs store3 values3 paths
  have firstZero : first.flags.2.1 = false := by
    simpa only [first, firstFieldState] using normalZero
  have secondZero : second.flags.2.1 = false := by
    simpa only [second, secondFieldState, first, firstFieldState] using normalZero
  have action1 := parameters.firstFieldState_action (Reference := Reference)
    environment inputs store values paths state address reference
  have action2 := parameters.secondFieldState_action (Reference := Reference)
    environment inputs store1 paths first address firstZero admitted reference
  have action3 := parameters.thirdFieldState_action (Reference := Reference)
    environment inputs store2 values2 paths second address secondZero reference
  have action4 := parameters.fourthFieldState_action (Reference := Reference)
    environment inputs store3 values3 paths third address reference
  have action5 := parameters.fifthFieldState_action (Reference := Reference)
    environment inputs store4 values4 paths fourth address reference
  unfold CompletePointFieldAction pointProgramInstrument PointFieldPaths.complete
    completeFieldState
  have composed := parameters.fivePointInstruments_branchAction (Reference := Reference)
    environment (parameters.differencesInstrument environment)
    (parameters.divisionInstrument environment) (parameters.multiplicationInstrument environment)
    (parameters.reflectionInstrument environment) (parameters.finishInstrument environment)
    store (paths.first parameters) (paths.second parameters) (paths.third parameters)
    (paths.fourth parameters) (paths.fifth parameters)
    (state.blank address) (first.initialized address) (second.initialized address)
    (third.initialized address) (fourth.initialized address)
    ((parameters.fifthFieldState inputs fourth address).blank address)
    reference
  unfold FivePointActions at composed
  exact composed action1 action2 action3 action4 action5

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
