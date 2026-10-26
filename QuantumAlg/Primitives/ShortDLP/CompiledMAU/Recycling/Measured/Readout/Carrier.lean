/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Control

/-!
# Exact actual readout character on the complete control/unit/reference carrier

The real H/MZ/reset tail contributes its actual outcome-dependent Fourier
character and physically restores the same original control to zero. Every
unit seed, helper and external-reference coordinate remains in the branch
equation [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open EncodedBit.MeasuredUncompute
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

private lemma resetLabel_physicalLabel (label : (Recycling.Carrier.full modulus.toNat).Index) :
    resetLabel (Physical.layout width).control (Carrier.physicalLabel modulus label) =
      Carrier.physicalLabel modulus (0, label.2) := by
  rcases label with ⟨bit, seed⟩
  unfold resetLabel Carrier.physicalLabel
  rw [Physical.cleanLabel_control]
  fin_cases bit
  · rfl
  · change (Physical.layout width).control.flip
      (Physical.cleanLabel width true (Carrier.unitWord modulus seed)) = _
    rw [Physical.cleanLabel_control_flip]
    rfl

/-- Every actual physical readout branch has its exact character and restores control zero. -/
lemma readout_record_ket (environment : OracleModel.empty.Interpretation)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension)
    (Reference : Register)
    (column : ((Recycling.Carrier.full modulus.toNat).prod Reference).Index) :
    (krausOperator (oracles := .empty) (control base noQuantum m ell width)
      (control_qubit base noQuantum m ell width)
      environment outcome Reference).applyVec
        (NormalizedVector.ket
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference column)).vec =
      (NormalizedVector.invSqrt2 * character
        (placedOutcome (Physical.layout width).control (Physical.qubits width)
          (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
        (finTwoEquiv column.1.1)) •
        (NormalizedVector.ket
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference
            ((0, column.1.2), column.2))).vec := by
  rcases column with ⟨label, reference⟩
  rw [readoutKraus_eq_placed]
  have actual := placedKraus_coherent_reference (oracles := .empty) (Physical.layout width).control
    (Physical.qubits width) (Context base noQuantum m ell width)
    (context_wires base noQuantum m ell width) environment outcome
    (fun _ : Unit => Carrier.physicalLabel modulus label) (fun _ => reference) (fun _ => 1)
  change (placedKraus (oracles := .empty) (Physical.layout width).control (Physical.qubits width)
      (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
      environment outcome Reference).applyVec
      (encodedExpansion (Physical.qubits width) (context_wires base noQuantum m ell width)
        (fun _ : Unit => Carrier.physicalLabel modulus label) (fun _ => reference) (fun _ => 1)) =
      encodedExpansion (Physical.qubits width) (context_wires base noQuantum m ell width)
        (fun _ : Unit => resetLabel (Physical.layout width).control
          (Carrier.physicalLabel modulus label)) (fun _ => reference)
        (fun _ => 1 * (NormalizedVector.invSqrt2 * character
          (placedOutcome (Physical.layout width).control (Physical.qubits width)
            (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
          ((Physical.layout width).control.get (Carrier.physicalLabel modulus label)))) at actual
  have labels :
      (fun _ : Unit => resetLabel (Physical.layout width).control
        (Carrier.physicalLabel modulus label)) =
      (fun _ : Unit => Carrier.physicalLabel modulus (0, label.2)) := by
    funext _
    exact resetLabel_physicalLabel width modulus label
  have selected : (Physical.layout width).control.get (Carrier.physicalLabel modulus label) =
      finTwoEquiv label.1 := Physical.cleanLabel_control width _ _
  rw [labels, selected] at actual
  simpa only [one_mul, unit_expansion, one_smul] using actual

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
