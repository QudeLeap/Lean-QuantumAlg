/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Placement
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Branch
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Semantics

/-!
# Exact physical H/MZ/reset tail of the measured arithmetic stage

The actual direct native H and identity/X realization have the same complete
physical matrices as the encoded reset bridge, using the full ordered wire
certificate. The actual interpreter still writes and reads its real outcome
cell and retains every original Store/history fiber [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open EncodedBit.MeasuredUncompute
open MAU.Addition.Gidney.Measured.Instruction

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The literal final H followed by the actual retained-cell measurement/reset. -/
def readout (result : CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  (Circuit.unitary (single base noQuantum m ell width Gate.HOp)).seq
    (measuredReset base noQuantum m ell width result)

private lemma readout_correction_matrix (environment : OracleModel.empty.Interpretation)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    QuditShift.operator (Context base noQuantum m ell width).quantumLayout
        (control base noQuantum m ell width) (-outcome) =
      (placedCorrection (oracles := .empty) (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
        outcome).matrix environment := by
  rw [← QuditShift.qubitShiftCircuit_matrix _ _ (control_qubit base noQuantum m ell width)
    .empty (-outcome) environment]
  unfold placedCorrection
  rw [unitaryOfEqualWires_matrix]
  unfold correction
  have correspondingZero :
      actualOutcome (Physical.layout width).control (Physical.qubits width)
        (placedOutcome (Physical.layout width).control (Physical.qubits width)
          (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
          outcome) = 0 ↔ outcome = 0 := by
    constructor
    · intro same
      apply Fin.ext
      have values := congrArg
        (fun value : Fin ((Physical.qubits width).toQuantum.wire
          (Physical.layout width).control.wire).dimension => value.val) same
      exact values
    · intro same
      subst outcome
      apply Fin.ext
      rfl
  by_cases zero : outcome = 0
  · have nativeZero : -outcome = 0 := neg_eq_zero.mpr zero
    have physicalZero :
        -(actualOutcome (Physical.layout width).control (Physical.qubits width)
          (placedOutcome (Physical.layout width).control (Physical.qubits width)
            (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
            outcome)) = 0 := neg_eq_zero.mpr (correspondingZero.mpr zero)
    unfold QuditShift.qubitShiftCircuit
    rw [if_pos nativeZero, if_pos physicalZero]
    rw [UnitaryCircuit.identity_matrix, UnitaryCircuit.identity_matrix,
      UnitaryOperator.unitaryOperator_reindex_one]
  · have physicalNonzero := fun same => zero (correspondingZero.mp same)
    simp only [QuditShift.qubitShiftCircuit, neg_eq_zero, if_neg zero, if_neg physicalNonzero]
    exact Placement.measuredSingle_matrix base noQuantum m ell width environment Gate.XOp

/-- The actual direct readout branch is exactly the complete physically placed encoded branch. -/
lemma readoutKraus_eq_placed (environment : OracleModel.empty.Interpretation)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    krausOperator (oracles := .empty) (control base noQuantum m ell width)
        (control_qubit base noQuantum m ell width)
        environment outcome Reference =
      placedKraus (oracles := .empty) (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)
        environment outcome Reference := by
  unfold krausOperator placedKraus
  rw [readout_correction_matrix base noQuantum m ell width environment outcome]
  have hadamard :
      (placedHadamard (oracles := .empty) (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width)).matrix
          environment = (single base noQuantum m ell width Gate.HOp).matrix environment := by
    rw [placedHadamard, unitaryOfEqualWires_matrix]
    exact (Placement.measuredSingle_matrix base noQuantum m ell width environment Gate.HOp).symm
  rw [hadamard]
  rfl

/-- Every actual direct readout block is the full sum of real physical outcome branches. -/
lemma readout_block_matrix
    (resultCell : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (result : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × (readout base noQuantum m ell width resultCell).Path)))
    (left right : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (((readout base noQuantum m ell width resultCell).execute environment Reference state).block
      result).matrix left right =
      ∑ original : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome,
          if record (oracles := .empty)
              (control base noQuantum m ell width) (control_qubit base noQuantum m ell width)
              (finiteOutput (control_qubit base noQuantum m ell width) resultCell)
              BitWord.model .empty original outcome = result then
            (krausOperator (oracles := .empty) (control base noQuantum m ell width)
                (control_qubit base noQuantum m ell width) environment.quantum outcome Reference *
              (state.block original).matrix *
                (krausOperator (oracles := .empty) (control base noQuantum m ell width)
                  (control_qubit base noQuantum m ell width) environment.quantum outcome
                  Reference).conjTranspose) left right
          else 0 := by
  have actual := execute_block_matrix (control base noQuantum m ell width)
    (control_qubit base noQuantum m ell width)
    (finiteOutput (control_qubit base noQuantum m ell width) resultCell) environment state
    result left right
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs <;> simp_all

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
