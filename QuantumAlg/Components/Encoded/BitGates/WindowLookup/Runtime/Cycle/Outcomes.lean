/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Coherent
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Path

/-!
# Common coherent coefficient for every actual query measurement record

The original result-word paths are in bijection with all finite words of
the measured width. The named-record coherent law therefore covers every
actual path of the inserted load/body/unlookup query. It does not restrict
the measurement outcomes, digit values, original history or Reference.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters

noncomputable section

open Execution NormalizedVector
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {wordWidth lowWidth highRemaining : Nat}
    (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)

/-- No actual measurement record is omitted from the common-coefficient query law. -/
lemma insertedBranchOperator_all_paths
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (outputDistinct : Function.Injective fun index => (parameters.output index).key)
    (protection : RuntimeRow.Protection (.storage parameters.mask.toCStorageRef)
      parameters.parity parameters.temporary
      (fun row : Bool × Fin (2 ^ highRemaining) =>
        splitInputs parameters.source row.1 row.2))
    (outputFree : ∀ index top row column,
      (parameters.output index).key ∉ (splitInputs parameters.source top row column).storageKeys)
    (maskFree : ∀ top row column,
      parameters.mask.key ∉ (splitInputs parameters.source top row column).storageKeys)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx) (seed : Data)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path)
    {Reference : Register} {Index : Type} [Fintype Index] (initial after : Index → Data)
    (lookupClean : ∀ index, parameters.lookup.CleanFrom 0 (initial index))
    (bodyActual : ∀ index, (body.matrix environment).applyVec
      (NormalizedVector.ket (measuredEncodedBasis parameters.physical parameters.sameWires
        (splitLookupStep parameters.lookup
          (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
            parameters.outsideStack)
          (tableValue (store.read parameters.source)) (initial index)))).vec =
      (NormalizedVector.ket
        (measuredEncodedBasis parameters.physical parameters.sameWires (after index))).vec)
    (graph : ∀ index, parameters.frame.Graph
      (fun top row => RuntimeRow.readTable (splitInputs parameters.source top row) store)
        (after index))
    (unlookupClean : ∀ index, parameters.frame.high.CleanFrom 0 (after index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (parameters.insertedBranchOperator body store path environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis parameters.physical parameters.sameWires (initial index),
            reference index)).vec) =
      invSqrt2 ^ wordWidth • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis parameters.physical parameters.sameWires
            (resultSetConstant parameters.frame.result 0 (after index)), reference index)).vec := by
  obtain ⟨outcome, same⟩ := (namedResultPath_bijective
    (oracles := .empty) (services := services) parameters.physical parameters.sameWires
    parameters.frame.result parameters.frame.resultDistinct parameters.output seed).surjective path
  rw [← same]
  exact parameters.insertedBranchOperator_coherent body outputDistinct protection outputFree
    maskFree environment store seed outcome initial after lookupClean bodyActual graph unlookupClean
    reference amplitude

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable.CycleParameters
