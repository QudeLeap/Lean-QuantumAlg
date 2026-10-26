/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Point
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Field.Schedule

/-!
# Field labels of the complete measured point program

Each chronological phase is compared separately with the same retained row.
The column family is invariant under numerical changes and genuine normal
flag updates. Composing these small equalities gives the original total field
schedule without unfolding the complete point trace in one simplification.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
namespace Program.Parameters
noncomputable section
open Execution Window.Sampling
variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Arithmetic.Call.clearedInitial Residue.input
  Window.Tables.selectedFieldColumn queryFieldNext nativeEnableValue
  PointFieldState.initialized firstFieldState secondFieldState thirdFieldState
  fourthFieldState fifthFieldState completeFieldState fieldProgramOutput
  nativeSquareValue nativeNormalFlags nativeReflectionValue Arithmetic.Call.Endpoint.setNormal

private def stateFieldColumns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) : Fin 5 → ZMod modulus :=
  Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (state.initialized address)

private def columnFirstState (columns : Fin 5 → ZMod modulus) (state : PointFieldState)
    (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 0 state.x state.y (columns 0) state.flags address
  let second : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 1 first.1 first.2 (columns 1) state.flags address
  ⟨second.1, second.2, state.flags⟩

private def columnThirdState (columns : Fin 5 → ZMod modulus) (state : PointFieldState)
    (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 2 state.x state.y (columns 2) state.flags address
  let square : ZMod modulus := parameters.nativeSquareValue first.1 first.2 state.flags address
  let normal : Frame.Controls := parameters.nativeNormalFlags square first.2 state.flags address
  let product : ZMod modulus := if normal.2.1 then first.2 * square else first.2
  PointFieldState.mk square product normal

private def columnFourthState (columns : Fin 5 → ZMod modulus) (state : PointFieldState)
    (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 3 state.x state.y (columns 3) state.flags address
  ⟨parameters.nativeReflectionValue first.1 first.2 state.flags address,
    first.2, parameters.nativeNormalFlags first.1 first.2 state.flags address⟩

private def columnFifthState (columns : Fin 5 → ZMod modulus) (state : PointFieldState)
    (address : Window.Address) : PointFieldState :=
  let first : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 4 state.x state.y (columns 4) state.flags address
  let second : ZMod modulus × ZMod modulus :=
    parameters.queryFieldNext 5 first.1 first.2 (columns 1) state.flags address
  ⟨second.1, second.2, state.flags⟩

private def columnCompleteState (columns : Fin 5 → ZMod modulus) (state : PointFieldState)
    (address : Window.Address) : PointFieldState :=
  let first := parameters.columnFirstState columns state address
  let second := parameters.secondFieldState first address
  let third := parameters.columnThirdState columns second address
  let fourth := parameters.columnFourthState columns third address
  parameters.columnFifthState columns fourth address

attribute [local irreducible] stateFieldColumns columnFirstState columnThirdState
  columnFourthState columnFifthState columnCompleteState

private lemma stateFieldColumns_sameFlags (inputs : PointFieldTableInputs parameters)
    (before after : PointFieldState) (address : Window.Address)
    (flags : after.flags = before.flags) :
    parameters.stateFieldColumns inputs after address =
      parameters.stateFieldColumns inputs before address := by
  funext column
  unfold stateFieldColumns PointFieldState.initialized
  rw [flags]
  exact Window.Tables.selectedFieldColumn_clearedInitial_values inputs.curve inputs.point
    parameters.stream (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input after.x) (Residue.input after.y)
    (Residue.input before.x) (Residue.input before.y) before.flags address column

private lemma stateFieldColumns_setNormal (inputs : PointFieldTableInputs parameters)
    (before after : PointFieldState) (address : Window.Address) (value : Bool)
    (flags : after.flags = Arithmetic.Call.Endpoint.setNormal before.flags value) :
    parameters.stateFieldColumns inputs after address =
      parameters.stateFieldColumns inputs before address := by
  funext column
  unfold stateFieldColumns PointFieldState.initialized
  rw [flags, Window.Tables.selectedFieldColumn_clearedInitial_setNormal]
  exact Window.Tables.selectedFieldColumn_clearedInitial_values inputs.curve inputs.point
    parameters.stream (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (Residue.input after.x) (Residue.input after.y)
    (Residue.input before.x) (Residue.input before.y) before.flags address column

private lemma firstFieldState_columns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.firstFieldState inputs state address =
      parameters.columnFirstState (parameters.stateFieldColumns inputs state address)
        state address := by
  unfold firstFieldState columnFirstState differencesFirstCoordinates stateFieldColumns
    PointFieldState.initialized
  rfl

private lemma thirdFieldState_columns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.thirdFieldState inputs state address =
      parameters.columnThirdState (parameters.stateFieldColumns inputs state address)
        state address := by
  unfold thirdFieldState columnThirdState middleCoordinates stateFieldColumns
    PointFieldState.initialized
  rfl

private lemma fourthFieldState_columns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.fourthFieldState inputs state address =
      parameters.columnFourthState (parameters.stateFieldColumns inputs state address)
        state address := by
  unfold fourthFieldState columnFourthState middleCoordinates stateFieldColumns
    PointFieldState.initialized
  rfl

private lemma fifthFieldState_columns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.fifthFieldState inputs state address =
      parameters.columnFifthState (parameters.stateFieldColumns inputs state address)
        state address := by
  unfold fifthFieldState columnFifthState finishLastCoordinates finishFirstCoordinates
    stateFieldColumns PointFieldState.initialized
  rfl

private lemma stateFieldColumns_first (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.stateFieldColumns inputs (parameters.firstFieldState inputs state address) address =
      parameters.stateFieldColumns inputs state address :=
  parameters.stateFieldColumns_sameFlags inputs state _ address
    (by simp only [firstFieldState])

private lemma stateFieldColumns_second (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.stateFieldColumns inputs (parameters.secondFieldState state address) address =
      parameters.stateFieldColumns inputs state address :=
  parameters.stateFieldColumns_sameFlags inputs state _ address
    (by simp only [secondFieldState])

private lemma stateFieldColumns_third (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.stateFieldColumns inputs (parameters.thirdFieldState inputs state address) address =
      parameters.stateFieldColumns inputs state address := by
  refine parameters.stateFieldColumns_setNormal inputs state _ address
    (parameters.thirdFieldState inputs state address).flags.2.1 ?_
  unfold thirdFieldState nativeNormalFlags Arithmetic.Call.Endpoint.setNormal
  rfl

private lemma stateFieldColumns_fourth (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.stateFieldColumns inputs (parameters.fourthFieldState inputs state address) address =
      parameters.stateFieldColumns inputs state address := by
  refine parameters.stateFieldColumns_setNormal inputs state _ address
    (parameters.fourthFieldState inputs state address).flags.2.1 ?_
  unfold fourthFieldState nativeNormalFlags Arithmetic.Call.Endpoint.setNormal
  rfl

private lemma completeFieldState_columns (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.completeFieldState inputs state address =
      parameters.columnCompleteState (parameters.stateFieldColumns inputs state address)
        state address := by
  let columns := parameters.stateFieldColumns inputs state address
  let first := parameters.firstFieldState inputs state address
  let second := parameters.secondFieldState first address
  let third := parameters.thirdFieldState inputs second address
  let fourth := parameters.fourthFieldState inputs third address
  have c1 := parameters.stateFieldColumns_first inputs state address
  have c2 := (parameters.stateFieldColumns_second inputs first address).trans c1
  have c3 := (parameters.stateFieldColumns_third inputs second address).trans c2
  have c4 := (parameters.stateFieldColumns_fourth inputs third address).trans c3
  have s1 := parameters.firstFieldState_columns inputs state address
  have s2 := congrArg (fun current => parameters.secondFieldState current address) s1
  have s3 := ((parameters.thirdFieldState_columns inputs second address).trans
    (congrArg (fun current => parameters.columnThirdState current second address) c2)).trans
      (congrArg (fun current => parameters.columnThirdState columns current address) s2)
  have s4 := ((parameters.fourthFieldState_columns inputs third address).trans
    (congrArg (fun current => parameters.columnFourthState current third address) c3)).trans
      (congrArg (fun current => parameters.columnFourthState columns current address) s3)
  have s5 := ((parameters.fifthFieldState_columns inputs fourth address).trans
    (congrArg (fun current => parameters.columnFifthState current fourth address) c4)).trans
      (congrArg (fun current => parameters.columnFifthState columns current address) s4)
  unfold completeFieldState columnCompleteState
  exact s5

private lemma columnSchedule_projection
    (query : Fin 6 → ZMod modulus → ZMod modulus → ZMod modulus →
      Frame.Controls → ZMod modulus × ZMod modulus)
    (quotient square product reflection :
      ZMod modulus → ZMod modulus → Frame.Controls → ZMod modulus)
    (normal : ZMod modulus → ZMod modulus → Frame.Controls → Frame.Controls)
    (columns : Fin 5 → ZMod modulus) (state : PointFieldState) :
    (let first : PointFieldState :=
      let a := query 0 state.x state.y (columns 0) state.flags
      let b := query 1 a.1 a.2 (columns 1) state.flags
      PointFieldState.mk b.1 b.2 state.flags
     let second : PointFieldState :=
      PointFieldState.mk first.x (quotient first.x first.y first.flags) first.flags
     let third : PointFieldState :=
      let a := query 2 second.x second.y (columns 2) second.flags
      let x := square a.1 a.2 second.flags
      let flags := normal x a.2 second.flags
      PointFieldState.mk x (product x a.2 flags) flags
     let fourth : PointFieldState :=
      let a := query 3 third.x third.y (columns 3) third.flags
      PointFieldState.mk (reflection a.1 a.2 third.flags) a.2
        (normal a.1 a.2 third.flags)
     let fifth : PointFieldState :=
      let a := query 4 fourth.x fourth.y (columns 4) fourth.flags
      let b := query 5 a.1 a.2 (columns 1) fourth.flags
      PointFieldState.mk b.1 b.2 fourth.flags
     ((fifth.x, fifth.y), fifth.flags)) =
    (let first := query 0 state.x state.y (columns 0) state.flags
     let second := query 1 first.1 first.2 (columns 1) state.flags
     let divided : ZMod modulus × ZMod modulus :=
      (second.1, quotient second.1 second.2 state.flags)
     let third := query 2 divided.1 divided.2 (columns 2) state.flags
     let squared := square third.1 third.2 state.flags
     let normalFlags := normal squared third.2 state.flags
     let multiplied := product squared third.2 normalFlags
     let fourth := query 3 squared multiplied (columns 3) normalFlags
     let restoredFlags := normal fourth.1 fourth.2 normalFlags
     let reflected := reflection fourth.1 fourth.2 normalFlags
     let fifth := query 4 reflected fourth.2 (columns 4) restoredFlags
     let sixth := query 5 fifth.1 fifth.2 (columns 1) restoredFlags
     (sixth, restoredFlags)) := by
  rfl


private lemma columnCompleteState_schedule (columns : Fin 5 → ZMod modulus)
    (state : PointFieldState) (address : Window.Address) :
    let result := parameters.columnCompleteState columns state address
    ((result.x, result.y), result.flags) =
      parameters.fieldProgramOutput columns state.x state.y state.flags address := by
  have actual := columnSchedule_projection
    (fun occurrence x y column flags =>
      parameters.queryFieldNext occurrence x y column flags address)
    (fun x y flags =>
      if parameters.nativeEnableValue x y flags address then y * x⁻¹ else y)
    (fun x y flags => parameters.nativeSquareValue x y flags address)
    (fun x y flags => if flags.2.1 then y * x else y)
    (fun x y flags => parameters.nativeReflectionValue x y flags address)
    (fun x y flags => parameters.nativeNormalFlags x y flags address)
    columns state
  unfold columnCompleteState columnFirstState secondFieldState columnThirdState
    columnFourthState columnFifthState fieldProgramOutput
  exact actual

private lemma completeFieldState_schedule (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    let result := parameters.completeFieldState inputs state address
    ((result.x, result.y), result.flags) =
      parameters.fieldProgramOutput
        (Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (state.initialized address)) state.x state.y state.flags address := by
  have actual := (congrArg
    (fun current : PointFieldState => ((current.x, current.y), current.flags))
    (parameters.completeFieldState_columns inputs state address)).trans
      (parameters.columnCompleteState_schedule
        (parameters.stateFieldColumns inputs state address) state address)
  unfold stateFieldColumns at actual
  exact actual

end
end Program.Parameters
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
