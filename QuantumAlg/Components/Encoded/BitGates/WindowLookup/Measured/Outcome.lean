/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Matrix
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Projection

/-!
# Original physical result values determine actual retained measurement paths

The actual path is the ordered product of the same existing qubit readings.
Complete ordered-wire placement changes only the dependent position types.
Path equality is exactly equality of the original physical result values,
independently of every incoming Store and reference coordinate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

private lemma labelsAgree_iff (readouts : List (ZReadout ctx))
    (first second : ctx.register.Index) :
    Circuit.measurementLabelsAgree readouts first second ↔
      ∀ readout ∈ readouts, first readout.wire = second readout.wire := by
  induction readouts with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail ih => simp [Circuit.measurementLabelsAgree, ih]

/-- Actual measurement paths agree precisely on the originally supplied physical result values. -/
lemma resultBasisPath_eq_iff (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (first second : physical.toQuantum.Basis) :
    Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires first) =
      Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires second) ↔
      ∀ index, first (target.bit index).wire = second (target.bit index).wire := by
  rw [Circuit.measurementBasisPath_eq_iff, labelsAgree_iff]
  constructor
  · intro agree index
    have values := congrArg Fin.val
      (agree (resultReadout physical sameWires (target.bit index) (output index))
        (List.mem_ofFn.mpr ⟨index, rfl⟩))
    apply Fin.ext
    exact (basisOfEqualWires_value physical.toQuantum ctx.quantumLayout sameWires first
      (target.bit index).wire).symm.trans (values.trans
        (basisOfEqualWires_value physical.toQuantum ctx.quantumLayout sameWires second
          (target.bit index).wire))
  · intro agree readout member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    apply Fin.ext
    exact (basisOfEqualWires_value physical.toQuantum ctx.quantumLayout sameWires first
      (target.bit index).wire).trans ((congrArg Fin.val (agree index)).trans
        (basisOfEqualWires_value physical.toQuantum ctx.quantumLayout sameWires second
          (target.bit index).wire).symm)

end

end QuantumAlg.EncodedBit.WindowLookup
