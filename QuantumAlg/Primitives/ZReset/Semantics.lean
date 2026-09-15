/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Circuit
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Measure.Reset
import all QuantumAlg.Components.QuditShift

/-!
# Complete execution semantics of measurement followed by cyclic correction

The proofs follow the actual circuit's Z measurement, write to classical
storage, read of that storage, and selected negative shift. They establish
that the selected system ends in its zero basis state and that the other
systems retain their complete joint marginal with an arbitrary external
reference. In particular, no separability assumption is imposed on the input.

The calculation uses unitary conjugation [dW19, qcnotes.tex:5405], projective
measurement [dW19, qcnotes.tex:5409], and the local projector tensored with the
reference identity [dW19, qcnotes.tex:5420]. It applies to every positive wire
dimension, including three, within the single circuit interpreter.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.pos⟩

private theorem permutation_entry {R : Register} (permutation : Equiv.Perm R.Index)
    (left right : R.Index) :
    (UnitaryOperator.ofPerm (R := R) permutation : HilbertOperator R) left right =
      if permutation left = right then 1 else 0 := by
  change permutation.toPEquiv.toMatrix left right = _
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

private theorem permutation_tensor_identity {R Reference : Register}
    (permutation : Equiv.Perm R.Index) :
    UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (R := R) permutation)
      (1 : UnitaryOperator Reference) =
      UnitaryOperator.ofPerm (R := Register.prod R Reference)
        (permutation.prodCongr (Equiv.refl Reference.Index)) := by
  apply Subtype.ext
  ext left right
  rcases right with ⟨rightLocal, rightRef⟩
  rw [UnitaryOperator.prodTensor_apply, permutation_entry, permutation_entry]
  change (if permutation left.1 = rightLocal then (1 : ℂ) else 0) *
      (if left.2 = rightRef then 1 else 0) =
    if (permutation left.1, left.2) = (rightLocal, rightRef) then 1 else 0
  by_cases localEqual : permutation left.1 = rightLocal <;>
    by_cases referenceEqual : left.2 = rightRef <;>
      simp [localEqual, referenceEqual]

private theorem shift_reference_entry {count : Nat} (layout : QuantumLayout count)
    (wire : Fin count) (amount : Fin (layout.wire wire).dimension) {Reference : Register}
    (state : DensityOperator (Register.prod layout.register Reference))
    (left right : layout.Basis) (leftRef rightRef : Reference.Index) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (QuditShift.operator layout wire amount)
        (1 : UnitaryOperator Reference)) state).matrix (left, leftRef) (right, rightRef) =
      state.matrix (Function.update left wire (left wire - amount), leftRef)
        (Function.update right wire (right wire - amount), rightRef) := by
  rw [QuditShift.operator,
    permutation_tensor_identity (R := layout.register) (Reference := Reference),
    ZReset.permutationDensityEntry]
  rfl

private theorem corrected_measurement_entry {count : Nat} (layout : QuantumLayout count)
    (wire : Fin count) (outcome : Fin (layout.wire wire).dimension) {Reference : Register}
    (state : DensityOperator (Register.prod layout.register Reference))
    (left right : layout.Basis) (leftRef rightRef : Reference.Index) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (QuditShift.program layout wire (-outcome)).matrix
        (1 : UnitaryOperator Reference))
      (ZMeasurement.branch (R := Register.prod layout.register Reference)
        (fun basis => basis.1 wire) outcome state)).matrix (left, leftRef) (right, rightRef) =
      if left wire = 0 ∧ right wire = 0 then
        state.matrix (Function.update left wire outcome, leftRef)
          (Function.update right wire outcome, rightRef)
      else 0 := by
  rw [QuditShift.program_matrix, shift_reference_entry]
  refine (ZMeasurement.branch_matrix (R := Register.prod layout.register Reference)
    (fun basis => basis.1 wire) outcome state
    (Function.update left wire (left wire - -outcome), leftRef)
    (Function.update right wire (right wire - -outcome), rightRef)).trans ?_
  simp only [Function.update_self, sub_neg_eq_add, ZReset.shiftedLabelEqOutcome]
  by_cases leftZero : left wire = 0 <;> by_cases rightZero : right wire = 0 <;>
    simp [leftZero, rightZero]

/-- Actual execution and actual stored-value selection give precisely the corrected Z branches. -/
private theorem circuit_quantumMarginal {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((circuit wire output).execute Reference state).quantumMarginal =
      ((ExecutionState.measureZ (R := Register.prod ctx.register Reference)
        (Outcome := Fin (ctx.quantumLayout.wire wire).dimension) state
        (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
          (fun result => UnitaryOperator.prodTensor
            (QuditShift.program ctx.quantumLayout wire (-result.2)).matrix
            (1 : UnitaryOperator Reference))).quantumMarginal := by
  rw [circuit, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.selectedUnitary_quantumMarginal, Circuit.execute_measureZ]
  simp only [State.measureZ, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.mapClassical_quantumMarginal, Store.read_write_same, CShape.Value.toFin_finite]

/-- The actual complete execution resets the selected wire and retains the other systems'
joint marginal with the arbitrary reference, including its off-diagonal entries. -/
private theorem circuit_entry {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((circuit wire output).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left wire = 0 ∧ right wire = 0 then
        ∑ entry : Store ctx × H, ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          (state.block entry).matrix (Function.update left wire outcome, leftRef)
            (Function.update right wire outcome, rightRef)
      else 0 := by
  rw [circuit_quantumMarginal]
  change (∑ result : (Store ctx × H) × Fin (ctx.quantumLayout.wire wire).dimension,
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (QuditShift.program ctx.quantumLayout wire (-result.2)).matrix
        (1 : UnitaryOperator Reference))
      (ZMeasurement.branch (R := Register.prod ctx.register Reference)
        (fun basis => basis.1 wire) result.2 (state.block result.1))).matrix)
          (left, leftRef) (right, rightRef) = _
  calc
    _ = ∑ result : (Store ctx × H) × Fin (ctx.quantumLayout.wire wire).dimension,
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (QuditShift.program ctx.quantumLayout wire (-result.2)).matrix
            (1 : UnitaryOperator Reference))
          (ZMeasurement.branch (R := Register.prod ctx.register Reference)
            (fun basis => basis.1 wire) result.2 (state.block result.1))).matrix
              (left, leftRef) (right, rightRef) :=
      Matrix.sum_apply (left, leftRef) (right, rightRef) Finset.univ _
    _ = _ := by
      simp only [Fintype.sum_prod_type, corrected_measurement_entry]
      by_cases bothZero : left wire = 0 ∧ right wire = 0 <;> simp [bothZero]

/-- No nonzero selected-wire row survives in the actual final quantum state. -/
private theorem circuit_selected_zero {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left wire ≠ 0) :
    ((circuit wire output).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 := by
  rw [circuit_entry]
  simp only [nonzero, false_and, if_false]

/-- The actual complete execution has support only at the selected zero label.
Its surviving entries are the original joint marginal of all other systems
and the arbitrary reference. Classical input blocks and all observed outcomes
are summed exactly once. -/
public theorem zReset_execute_entry {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((circuit wire output).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left wire = ctx.quantumLayout.zeroLabel wire ∧
          right wire = ctx.quantumLayout.zeroLabel wire then
        ∑ entry : Store ctx × H, ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          (state.block entry).matrix (Function.update left wire outcome, leftRef)
            (Function.update right wire outcome, rightRef)
      else 0 :=
  circuit_entry wire output state left right leftRef rightRef

/-- No nonzero selected-system row survives in the actual final quantum state,
including entries correlated with any external reference. -/
public theorem zReset_execute_selected_zero {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left wire ≠ ctx.quantumLayout.zeroLabel wire) :
    ((circuit wire output).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 :=
  circuit_selected_zero wire output state left right leftRef rightRef nonzero

end

end QuantumAlg.ZReset
