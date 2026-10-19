/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Selection
import all QuantumAlg.Core.Execution.Context.Embedding.Selection
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.Context.Relabeling.Layout
import all QuantumAlg.Core.Execution.Context.Union.Basis

/-!
# Finite values at physically placed selected wires

The execution basis and the selected-output basis use the same wire positions.
Each correspondence preserves the native finite value, including differing
wire dimensions [dW19, qcnotes.tex:389].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Joining the complete state places the original value on every local wire. -/
public lemma contextEmbedding_join_local_value
    (localValue : localCtx.register.Index) (frameValue : placement.frame.register.Index)
    (index : Fin localCtx.systemCount) :
    (placement.basis.symm (localValue, frameValue) (placement.position index)).val =
      (localValue index).val := by
  exact (ContextPermutation.basis_value placement.covers _ _).trans
    ((ContextUnion.contextUnion_join_left_value _ _ placement.separate _ _ _).trans
      (ContextRelabeling.basis_value localCtx placement.keys placement.physical localValue index))

/-- The same join keeps every complement wire's actual finite value unchanged. -/
public lemma contextEmbedding_join_frame_value
    (localValue : localCtx.register.Index) (frameValue : placement.frame.register.Index)
    (index : Fin placement.frame.systemCount) :
    (placement.basis.symm (localValue, frameValue) (placement.positions (.inr index))).val =
      (frameValue index).val :=
  (ContextPermutation.basis_value placement.covers _ _).trans
    (ContextUnion.contextUnion_join_right_value _ _ placement.separate _ _ index)

/-- Restricting to selected wires uses the same finite value at each selected position. -/
public lemma contextEmbedding_selectedBasis_value
    (selected : Finset (Fin localCtx.systemCount))
    (value : (localCtx.quantumLayout.selectedRegister selected).Index)
    (index : QuantumLayout.SelectedPosition selected) :
    (placement.selectedBasis selected value (placement.selectedPositions selected index)).val =
      (value index).val := by
  exact congrArg
    (fun result : Fin (caller.quantumLayout.wire
      (placement.selectedPositions selected index).val).dimension => result.val)
    (Equiv.piCongr_apply_apply
      (W := fun position : QuantumLayout.SelectedPosition selected =>
        Fin (localCtx.quantumLayout.wire position.val).dimension)
      (Z := fun position : QuantumLayout.SelectedPosition (placement.selection selected) =>
        Fin (caller.quantumLayout.wire position.val).dimension)
      (placement.selectedPositions selected)
      (fun position =>
        finCongr (congrArg PNat.val
          (placement.contextEmbedding_position_dimension position.val).symm)) value index)

end

end QuantumAlg.ContextEmbedding
