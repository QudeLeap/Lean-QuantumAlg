/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Field
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Readout

/-!
# Actual query action between complete original initialized labels

The two actual numerical reads determine the ordinary field update.
The original setter then gives the entire next initializer, retaining
source padding, small history, C/N/W, address and arbitrary Reference.
These field specializations do not replace the arbitrary-binary disabled
law. The actual enclosing table builder must still prove its source read.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open Execution EncodedBit.WindowLookup Arithmetic.Call Arithmetic.Call.Endpoint
open Window Window.QueryInsertion

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input

/-- The original occurrence reads X for its three horizontal queries and Y otherwise. -/
def queryTargetValue (occurrence : Fin 6) (x y : ZMod modulus) : ZMod modulus :=
  if occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4 then x else y

/-- Replace the same original numerical coordinate as the literal query target setter. -/
def queryFieldCoordinates (occurrence : Fin 6) (x y updated : ZMod modulus) :
    ZMod modulus × ZMod modulus :=
  if occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4 then
    (updated, y) else (x, updated)

/-- The complete original initialized label has the actual queried target field word. -/
lemma queryInitial_target_value (occurrence : Fin 6) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    (QueryColumns.assignment occurrence).target.value
        (clearedInitial (Residue.input x) (Residue.input y) flags address).1 =
      Residue.word (queryTargetValue occurrence x y) := by
  by_cases horizontal : occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4
  · simp only [queryTargetValue, QueryColumns.assignment, if_pos horizontal,
      Offset.Placed.horizontal]
    change Frame.work2
      (Inversion.initial (Residue.input x) (Residue.input y) (0, (0, false)) flags) = _
    have actual := Inversion.initial_value (Residue.input x) (Residue.input y)
      (0, (0, false)) flags
    rw [Residue.cast_input] at actual
    exact actual
  · simp only [queryTargetValue, QueryColumns.assignment, if_neg horizontal,
      Offset.Placed.vertical]
    exact queryInitial_numerator x y flags address

/-- The binary-input update is exactly the encoding of the same pair of field coordinates. -/
lemma queryUpdated_input (occurrence : Fin 6) (x y updated : ZMod modulus) :
    queryUpdated occurrence (Residue.input x) (Residue.input y) (Residue.input updated) =
      (Residue.input (queryFieldCoordinates occurrence x y updated).1,
        Residue.input (queryFieldCoordinates occurrence x y updated).2) := by
  by_cases horizontal : occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4
  · simp only [queryUpdated, queryFieldCoordinates, if_pos horizontal]
  · simp only [queryUpdated, queryFieldCoordinates, if_neg horizontal]

/-- The original field setter returns the whole next initializer, not just its X/Y reads. -/
lemma querySet_fieldCoordinates (occurrence : Fin 6) (x y updated : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    resultSetConstant (resultWord (QueryColumns.assignment occurrence).target)
        (Residue.word updated)
        (clearedInitial (Residue.input x) (Residue.input y) flags address) =
      clearedInitial (Residue.input (queryFieldCoordinates occurrence x y updated).1)
        (Residue.input (queryFieldCoordinates occurrence x y updated).2) flags address := by
  have actual := querySet_clearedInitial_residue occurrence x y updated flags address
  rw [queryUpdated_input] at actual
  exact actual

namespace Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

attribute [local irreducible] clearedInitial queryTargetValue queryFieldCoordinates

/-- Only the original stored-column read on the same complete initialized label. -/
structure QueryInitializedSource (occurrence : Fin 6) (store : Store ctx)
    (x y column : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) : Prop where
  sourceValue : selectedWord parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (RuntimeTable.tableValue (store.read (.storage (parameters.querySource occurrence))))
    (clearedInitial (Residue.input x) (Residue.input y) flags address) = Residue.word column

/-- The two actual reads specialize before the physical branch equation is elaborated. -/
lemma queryInitializedSource_values (occurrence : Fin 6) (store : Store ctx)
    (x y column : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (values : parameters.QueryInitializedSource occurrence store x y column flags address) :
    parameters.QueryFieldValues occurrence store
      (clearedInitial (Residue.input x) (Residue.input y) flags address)
      column (queryTargetValue occurrence x y) := by
  constructor
  · exact values.sourceValue
  · exact queryInitial_target_value occurrence x y flags address

/-- The ordinary selected update on the same complete initial label's original coordinates. -/
def queryFieldNext (occurrence : Fin 6) (x y column : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) : ZMod modulus × ZMod modulus :=
  let initial := clearedInitial (Residue.input x) (Residue.input y) flags address
  queryFieldCoordinates occurrence x y
    (queryTargetValue occurrence x y +
      if querySelected parameters.stream (parameters.highRemaining + parameters.lowWidth)
        parameters.addressBound (decide (occurrence.val = 3)) initial then column else 0)

attribute [local irreducible] referenceKet queryBranchOperator QueryBranchAction
  Circuit.measurementSequence resultReadouts queryFieldNext

/-- Every actual retained query record returns the complete next original initializer. -/
lemma queryBranchOperator_initialized_residue (occurrence : Fin 6) (store : Store ctx)
    (separation : parameters.QueryFieldSeparation occurrence)
    (environment : OracleModel.empty.Interpretation) (seed : Window.Raw)
    (path : parameters.QueryOutcome (services := services) occurrence)
    (x y column : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (values : parameters.QueryInitializedSource occurrence store x y column flags address)
    {Reference : Register} (reference : Reference.Index) :
    parameters.QueryBranchAction (services := services) (Reference := Reference)
      occurrence store path environment
      (clearedInitial (Residue.input x) (Residue.input y) flags address)
      (clearedInitial
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).1)
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).2)
        flags address) reference := by
  let initial := clearedInitial (Residue.input x) (Residue.input y) flags address
  let updated := queryTargetValue occurrence x y +
    if querySelected parameters.stream (parameters.highRemaining + parameters.lowWidth)
      parameters.addressBound (decide (occurrence.val = 3)) initial then column else 0
  have actual := parameters.queryBranchOperator_residue (services := services)
    (Reference := Reference) occurrence store separation environment seed initial path
    (queryInitial_clean (Residue.input x) (Residue.input y) flags address)
    (queryInitial_source_zero occurrence (Residue.input x) (Residue.input y) flags address)
    column (queryTargetValue occurrence x y)
    (parameters.queryInitializedSource_values occurrence store x y column flags address values)
    reference
  have label : resultSetConstant (resultWord (QueryColumns.assignment occurrence).target)
      (Residue.word updated) initial =
      clearedInitial
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).1)
        (Residue.input (parameters.queryFieldNext occurrence x y column flags address).2)
        flags address := by
    simpa only [queryFieldNext] using
      querySet_fieldCoordinates occurrence x y updated flags address
  unfold QueryBranchAction at actual ⊢
  exact actual.trans (congrArg (fun state : Window.Raw =>
    NormalizedVector.invSqrt2 ^ 256 •
      parameters.referenceKet (Reference := Reference) state reference) label)

end Parameters

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
