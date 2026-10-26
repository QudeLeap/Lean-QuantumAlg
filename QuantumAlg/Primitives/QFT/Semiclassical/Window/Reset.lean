/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Entries
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Core.Base.Tensor.Reference
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Measure.Reset

/-!
# The actual corrected Fourier head is physically zero

The new Kraus word is the old literal H/MZ/phase word followed by the same
native identity/X whose exact negative-shift matrix is already certified.
Its full-layout row permutation moves precisely the measured sector to zero.
Every other physical system and arbitrary reference coordinate stays present.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private instance windowResetDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

private def priorKraus (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) :
    HilbertOperator (ctx.register.prod Reference) :=
  _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.nativeStageKraus
    (environment := environment) true (ports.wires 0) (ports.qubits 0)
    ports.tail.wires ports.tail.qubits Reference outcome

private lemma reference_product {Local Reference : Register}
    (second first : UnitaryOperator Local) :
    (UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) :
        HilbertOperator (Local.prod Reference)) *
      (UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) :
        HilbertOperator (Local.prod Reference)) =
      (UnitaryOperator.prodTensor (second * first) (1 : UnitaryOperator Reference) :
        HilbertOperator (Local.prod Reference)) := by
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, HilbertOperator.kronecker_identity_mul]
  rfl

/-- The same native negative-result shift follows the existing measured Fourier Kraus word. -/
lemma window_stageKraus_factor (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) :
    nativeStageKraus ports environment Reference outcome =
      (UnitaryOperator.prodTensor
        (QuditShift.operator ctx.quantumLayout (ports.wires 0) (-outcome))
          (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) *
        priorKraus ports environment Reference outcome := by
  dsimp only [nativeStageKraus, priorKraus, afterHead,
    _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.nativeStageKraus]
  rw [UnitaryCircuit.seq_matrix, QuditShift.qubitShiftCircuit_matrix, ← reference_product]
  simp only [Matrix.mul_assoc, CShape.Value.toFin]

/-- Reset is the certified physical row update on the entire bank and untouched reference. -/
lemma window_stageKraus_shift_entry (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension)
    (row column : (ctx.register.prod Reference).Index) :
    nativeStageKraus ports environment Reference outcome row column =
      priorKraus ports environment Reference outcome
        (Function.update row.1 (ports.wires 0) (row.1 (ports.wires 0) + outcome), row.2)
        column := by
  rw [window_stageKraus_factor, QuditShift.operator_reference_permutation]
  simp only [Matrix.mul_apply, UnitaryOperator.ofPerm_entry, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  change priorKraus ports environment Reference outcome
    (Function.update row.1 (ports.wires 0)
      (row.1 (ports.wires 0) - -outcome), row.2) column = _
  rw [sub_neg_eq_add]

/-- No nonzero original physical head row survives the actual measured and corrected stage. -/
lemma window_stageKraus_zero_row (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension)
    (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires 0) ≠ 0) :
    nativeStageKraus ports environment Reference outcome row column = 0 := by
  rw [window_stageKraus_shift_entry]
  unfold priorKraus
  rw [_root_.QuantumAlg.QuantumFourierTransform.Semiclassical.nativeStageKraus_physical_entry]
  have outside :
      (Function.update row.1 (ports.wires 0) (row.1 (ports.wires 0) + outcome))
          (ports.wires 0) ≠ outcome := by
    simp only [Function.update_self]
    exact fun same => nonzero ((ZReset.shiftedLabelEqOutcome outcome _).mp same)
  rw [if_neg outside, mul_zero, zero_mul]

private lemma conjugation_zero_row {Index : Type*} [Fintype Index]
    (operator density : Matrix Index Index ℂ) (row column : Index)
    (zero : ∀ middle, operator row middle = 0) :
    (operator * density * operator.conjTranspose) row column = 0 := by
  simp only [Matrix.mul_apply, zero, zero_mul, Finset.sum_const_zero]

/-- Every complete final store has physical head zero, for arbitrary original mixtures and Ref. -/
lemma window_stage_store_zero_row (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx)
    (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires 0) ≠ 0) :
    (ExecutionState.filterClassical
      ((stage ports).execute environment Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal.matrix row column = 0 := by
  rw [window_stage_store_matrix]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro original _
  apply Finset.sum_eq_zero
  intro outcome _
  by_cases written : original.1.write (ports.measuredOutput 0) (.finite outcome) = stored
  · rw [if_pos written]
    exact conjugation_zero_row _ _ row column
      (fun middle => window_stageKraus_zero_row ports environment.quantum Reference outcome
        row middle nonzero)
  · rw [if_neg written]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
