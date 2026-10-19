/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Measurement
import all QuantumAlg.Core.Execution.Preparation.Coordinates

/-!
# Stored numerator outcomes agree with the actual native word

The native frame encoding and the runtime measurement use the same physical
numerator positions. The correspondence below holds for every auxiliary
label and both arbitrary supplied input words. It relates actual stored
finite measurement values to the little-endian mask consumed by the native
reset and phase-correction gates, without a packed result register
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorMeasurement

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Binary labels of the same actual full runtime frame after retaining measurement cells. -/
def frameBasis (width : Nat) :
    (context width).register.Index ≃ (Qubits (OutputCopy.encoding width).width).Index :=
  (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm.trans
    (InverseAssembly.basisEquiv width)

private lemma supplied_value (width : Nat)
    (old : (InversePreparation.before width).register.Index) (index : Fin width) :
    decide ((old (suppliedWire width index)).val = 1) =
      (InversePreparation.inputBasisEquiv width old).2.val.testBit index.val := by
  let raw := (basisOfEqualWires (InversePreparation.inputLayout width)
    (InversePreparation.before width).quantumLayout (InversePreparation.input_wires width)).symm old
  have actual := basisOfEqualWires_value (InversePreparation.inputLayout width)
    (InversePreparation.before width).quantumLayout (InversePreparation.input_wires width)
      raw (sourcePosition width index)
  have stored : (old (suppliedWire width index)).val = (raw (sourcePosition width index)).val := by
    simpa only [raw, suppliedWire, Equiv.apply_symm_apply] using actual
  have reverse : (sourcePosition width index).rev.val = index.val := by
    simp only [sourcePosition, Fin.val_rev]
    have bound := index.isLt
    omega
  have bit := (InversePreparation.inputQubitLayout width).binaryIndexEquiv_bit
    raw (sourcePosition width index)
  rw [reverse] at bit
  have packed : prodEquiv (m := width) (n := width)
      (InversePreparation.inputBasisEquiv width old) =
        (InversePreparation.inputQubitLayout width).binaryIndexEquiv raw :=
    (prodEquiv (m := width) (n := width)).apply_symm_apply _
  have right := prodEquiv_testBit_right (InversePreparation.inputBasisEquiv width old).1
    (InversePreparation.inputBasisEquiv width old).2 index
  rw [packed, bit] at right
  have finite (value : Fin 2) : finTwoEquiv value = decide (value.val = 1) := by
    fin_cases value <;> rfl
  exact (congrArg (fun value : Nat => decide (value = 1)) stored).trans
    ((finite (raw (sourcePosition width index))).symm.trans right)

/-- Arbitrary fresh values never change the supplied numerator's actual finite wire value. -/
lemma preparedWire_value (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (InversePreparation.before width).register.Index) (index : Fin width) :
    (InversePreparation.assembly width (fresh, old) (preparedWire width index)).val =
      (old (suppliedWire width index)).val :=
  preparedLocalBasisEquiv_old_value (InversePreparation.before width)
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout width)
      (InversePreparation.auxiliary_fresh width) (InversePreparation.auxiliary_disjoint width)
        fresh old (suppliedWire width index)

/-- Every measured physical bit is exactly the corresponding low native-frame bit. -/
lemma wire_basis_bit (width : Nat) (basis : (context width).register.Index)
    (index : Fin width) :
    decide ((basis (wire width index)).val = 1) =
      (frameBasis width basis).val.testBit index.val := by
  obtain ⟨prepared, rfl⟩ :=
    (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).surjective basis
  obtain ⟨⟨fresh, old⟩, rfl⟩ := (InversePreparation.assembly width).surjective prepared
  have retained := MeasurementCells.basisEquiv_value (InversePreparation.after width) 2 width
    (InversePreparation.assembly width (fresh, old)) (preparedWire width index)
  have actual := retained.trans (preparedWire_value width fresh old index)
  have native := InverseAssembly.basisEquiv_target width fresh old index.rev
  rw [InverseAssembly.target_rev, Fin.rev_rev] at native
  have frame : frameBasis width
      (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width
        (InversePreparation.assembly width (fresh, old))) =
      InverseAssembly.basisEquiv width (InversePreparation.assembly width (fresh, old)) :=
    congrArg (InverseAssembly.basisEquiv width)
      ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm_apply_apply _)
  rw [frame]
  exact (congrArg (fun value : Nat => decide (value = 1)) actual).trans
    ((supplied_value width old index).trans native.symm)

/-- The actual stored result selects exactly the native numerator mask for that Z branch. -/
lemma stored_native_mask (width : Nat) (store : Store (context width))
    (basis : (context width).register.Index) (index : Fin width) :
    QubitReadouts.mask ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (allowAllocation := true)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model)
        (allowAllocation := true)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width) basis)).read (input width)) index =
        (frameBasis width basis).val.testBit index.val :=
  (stored_mask width store basis index).trans (wire_basis_bit width basis index)

end

end QuantumAlg.MeasuredUncompute.NumeratorMeasurement
