/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Observation
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Character

/-!
# Common actual measurement-unlookup branch coefficient

The original result word executes its real parallel H/MZ/stored-X reset.
Its actual final Store feeds unary preparation and every paid parity row.
The native inverse restores the reused result systems. On the original
lookup graph, the two exact measured characters cancel to the same positive
coefficient, with every original external reference coordinate retained.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution NormalizedVector

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (output : Fin resultWidth → CWriteRef ctx (.finite 2))

/-- The actual ordered result-measurement path of one complete original physical basis column. -/
def outcomePath (state : Data) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path :=
  Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires frame.result output)
    (measuredEncodedBasis physical sameWires state)

/-- Exact original word-reset Kraus operator followed by its true next-Store paid feedback tail. -/
def branchOperator (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path)
    (environment : OracleModel.Interpretation .empty) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor
    (frame.restorationOperator (services := services) physical sameWires
      (.storage mask.toCStorageRef) parity table environment
      (measuredWordFinalStore (oracles := .empty) (services := services)
        physical sameWires frame.result output mask store path))
    (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
      measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask store
        path environment Reference

/-- Clearing only the original result systems preserves the exact measured table character. -/
lemma restoredCharacter_resultSet_zero
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (value : CShape.Value (.bits resultWidth)) (state : Data) :
    frame.restoredCharacter table value (resultSetConstant frame.result 0 state) =
      if MaskParity.maskValue value (frame.tableAt table state) then (-1 : ℂ) else 1 := by
  change (if MaskParity.maskValue value
    (frame.tableAt table (resultSetConstant frame.result 0 state)) then (-1 : ℂ) else 1) = _
  rw [frame.tableAt_resultSet]

/-- Every actual named outcome has the same positive coefficient on the concrete lookup graph. -/
lemma branchOperator_graph_ket (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉
      (CInputRef.storage mask.toCStorageRef).storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx)
    (state : Data) (graph : frame.Graph table state) (clean : frame.high.CleanFrom 0 state)
    (outcome : Fin (2 ^ resultWidth)) {Reference : Register} (reference : Reference.Index) :
    (frame.branchOperator (services := services) physical sameWires output mask parity table store
      (frame.outcomePath (services := services) physical sameWires output
        (resultSetConstant frame.result outcome state)) environment Reference).applyVec
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires state, reference)).vec =
      invSqrt2 ^ resultWidth •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires
            (resultSetConstant frame.result 0 state), reference)).vec := by
  let measured := resultSetConstant frame.result outcome state
  let next := measuredWordFinalStore (oracles := .empty) (services := services)
    physical sameWires frame.result output mask store
      (frame.outcomePath (services := services) physical sameWires output measured)
  have reset := measuredWordKraus_encoded_ket (oracles := .empty) (services := services)
    physical sameWires frame.result frame.resultDistinct output mask environment store state
    measured (resultSetConstant_complement physical frame.result frame.resultDistinct outcome state)
    reference
  rw [measuredWordResetStep_set_eq_zero physical sameWires frame.result frame.resultDistinct
    output outputDistinct] at reset
  have coefficient := wordHadamardAmplitude_measuredMask (oracles := .empty) (services := services)
    physical sameWires frame.result output outputDistinct mask store state measured
    (frame.tableAt table state) graph
  rw [coefficient] at reset
  change (measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask store
    (frame.outcomePath (services := services) physical sameWires output measured)
      environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires state, reference)).vec =
    (invSqrt2 ^ resultWidth *
      (if MaskParity.maskValue (next.read (.storage mask.toCStorageRef))
        (frame.tableAt table state) then (-1 : ℂ) else 1)) •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires
          (resultSetConstant frame.result 0 state), reference)).vec at reset
  have feedback := frame.restorationOperator_reference_ket (services := services)
    physical sameWires (.storage mask.toCStorageRef) parity table separate environment next
    (resultSetConstant frame.result 0 state) (frame.resultSet_zero_low state)
    (frame.resultSet_clean 0 state clean) reference
  rw [frame.restoredCharacter_resultSet_zero] at feedback
  change HilbertOperator.applyVec (R := Register.prod ctx.register Reference) _ _ = _ at feedback
  unfold branchOperator
  rw [HilbertOperator.mul_applyVec, reset, HilbertOperator.applyVec_smul, feedback, smul_smul]
  change ((invSqrt2 ^ resultWidth *
      (if MaskParity.maskValue (next.read (.storage mask.toCStorageRef))
        (frame.tableAt table state) then (-1 : ℂ) else 1)) *
      (if MaskParity.maskValue (next.read (.storage mask.toCStorageRef))
        (frame.tableAt table state) then (-1 : ℂ) else 1)) • _ = _
  split_ifs <;> simp

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
