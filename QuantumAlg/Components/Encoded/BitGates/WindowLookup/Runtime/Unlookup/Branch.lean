/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Restoration.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Branch

/-!
# Actual runtime measurement-unlookup branch operator

The complete physical result-reset Kraus operator is followed by the actual
paid runtime restoration operator on its true returned Store. These are
mathematical observations of the same program, not extra runtime operations.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

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
    (temporary : CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path)
    (environment : OracleModel.Interpretation .empty) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor
    (restorationOperator frame (services := services) physical sameWires
      (.storage mask.toCStorageRef) parity temporary table environment
      (measuredWordFinalStore (oracles := .empty) (services := services)
        physical sameWires frame.result output mask store path))
    (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
      measuredWordKraus physical sameWires frame.result frame.resultDistinct output mask store
        path environment Reference

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup
