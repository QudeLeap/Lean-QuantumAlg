/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution

/-!
# Phase-wire coordinates of the actual source sampler

The physical Z-measurement positions are the phase prefix of the same binary
source basis used by the accepted native word. This tracks each actual wire
through owned-register preparation and retained classical-cell allocation.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- The actual phase wire has the corresponding source-basis value. -/
theorem phaseWire_value (t width : Nat)
    (basis : (post ctx noQuantum t width).register.Index) (index : Fin t) :
    (basis (phaseWire ctx noQuantum t width index)).val =
      ((OrderFinding.Native.sourceLayout t width).binaryIndexEquiv.symm
        (outputBasisEquiv ctx noQuantum t width basis)
        (Fin.castAdd width index)).val := by
  let oldBasis :=
    (MeasurementCells.basisEquiv (resultContext ctx noQuantum t width) 2 t).symm basis
  let physical := Execution.basisOfEqualWires
    (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width)
  let sourceBasis : (OrderFinding.Native.sourceLayout t width).toQuantumLayout.register.Index :=
    physical.symm oldBasis
  let sourceIndex := Fin.castAdd width index
  have samePosition : preparedWire ctx noQuantum t width sourceIndex =
      Execution.positionsOfEqualWires (Sampling.Native.runtimeLayout t width)
        (preparedContext ctx noQuantum t width).quantumLayout
        (prepared_wires ctx noQuantum t width) sourceIndex := by
    apply Fin.ext
    rfl
  have cells := MeasurementCells.basisEquiv_value
    (resultContext ctx noQuantum t width) 2 t oldBasis
    (preparedWire ctx noQuantum t width sourceIndex)
  rw [Equiv.apply_symm_apply] at cells
  have prepared := Execution.basisOfEqualWires_value
    (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width) sourceBasis sourceIndex
  rw [Equiv.apply_symm_apply] at prepared
  rw [← samePosition] at prepared
  have binaryBasis : outputBasisEquiv ctx noQuantum t width basis =
      (OrderFinding.Native.sourceLayout t width).binaryIndexEquiv sourceBasis := rfl
  rw [binaryBasis, Equiv.symm_apply_apply]
  exact cells.trans prepared

private theorem finiteBit_encoding (value : Fin 2) :
    decide (value.val = 1) = finTwoEquiv value := by
  fin_cases value <;> rfl

/-- The physical Z readout has the source Born model's binary bit order. -/
theorem phaseWire_bit (t width : Nat)
    (basis : (post ctx noQuantum t width).register.Index) (index : Fin t) :
    decide ((basis (phaseWire ctx noQuantum t width index)).val = 1) =
      (OrderFinding.Native.measurement t width).readout
        (outputBasisEquiv ctx noQuantum t width basis) index := by
  calc
    _ = finTwoEquiv
        ((OrderFinding.Native.sourceLayout t width).binaryIndexEquiv.symm
          (outputBasisEquiv ctx noQuantum t width basis)
          (Fin.castAdd width index)) :=
      (congrArg (fun value => decide (value = 1))
        (phaseWire_value ctx noQuantum t width basis index)).trans
        (finiteBit_encoding _)
    _ = _ := by
      have bit := (OrderFinding.Native.sourceLayout t width).binaryIndexEquiv_bit
        ((OrderFinding.Native.sourceLayout t width).binaryIndexEquiv.symm
          (outputBasisEquiv ctx noQuantum t width basis))
        (Fin.castAdd width index)
      rw [Equiv.apply_symm_apply] at bit
      change _ = (outputBasisEquiv ctx noQuantum t width basis).val.testBit
        (t + width - 1 - index.val)
      have position : t + width - 1 - index.val =
          (Fin.castAdd width index).rev.val := by
        have castValue : (Fin.castAdd width index).val = index.val := rfl
        simp only [Fin.rev]
        omega
      rw [position]
      exact bit.symm

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
