/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.Projector.Zero.SourceWork.Coordinates
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Complete native matrix of the known zero-projector flip

The operator equality observes every input basis label, including arbitrary
signal work. It therefore retains all superpositions and external correlations.
-/

namespace QuantumAlg.ZeroProjector.SourceWork
noncomputable section

private theorem controlledNot_entry {m n : Nat} (rowPhase phase : Fin 2)
    (rowAncilla ancilla : Fin (2 ^ m)) (rowSignal signal : Fin (2 ^ n)) :
    OrthogonalProjector.controlledNotOp (OrthogonalProjector.zeroAncilla m n)
      (triple rowPhase rowAncilla rowSignal) (triple phase ancilla signal) =
      if triple rowPhase rowAncilla rowSignal =
        (if ancilla = 0 then triple (WireAddress.flipBit (0 : Fin 1) phase) ancilla signal
          else triple phase ancilla signal) then 1 else 0 := by
  have flipZero : WireAddress.flipBit (0 : Fin 1) (0 : Fin 2) = 1 := by decide
  have flipOne : WireAddress.flipBit (0 : Fin 1) (1 : Fin 2) = 0 := by decide
  by_cases zero : ancilla = 0 <;>
    by_cases sameAncilla : rowAncilla = ancilla <;>
    by_cases sameSignal : rowSignal = signal <;>
    fin_cases rowPhase <;> fin_cases phase <;>
    simp [OrthogonalProjector.controlledNotOp, OrthogonalProjector.zeroAncilla,
      OrthogonalProjector.tensor, OrthogonalProjector.zero, OrthogonalProjector.basis,
      OrthogonalProjector.basisOp, OrthogonalProjector.identity,
      OrthogonalProjector.complement, HilbertOperator.tensor_apply, triple,
      Gate.XOp, UnitaryOperator.ofPerm, Matrix.one_apply,
      zero, sameAncilla, sameSignal, flipZero, flipOne]

private theorem program_entry (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel)
    (rowPhase phase : Fin 2) (rowAncilla ancilla : Fin (2 ^ m))
    (rowSignal signal : Fin (2 ^ n)) :
    UnitaryOperator.reindex physical.basisEquiv (program m n positive physical oracles).matrix
      (triple rowPhase rowAncilla rowSignal) (triple phase ancilla signal) =
      if triple rowPhase rowAncilla rowSignal =
        (if ancilla = 0 then triple (WireAddress.flipBit (0 : Fin 1) phase) ancilla signal
          else triple phase ancilla signal) then 1 else 0 := by
  have action := program_apply_triple m n positive physical oracles phase ancilla signal
  have entry := congrArg (fun state : NormalizedVector physical.toQuantum.register =>
    (state : HilbertVector physical.toQuantum.register)
      (physical.basisEquiv.symm (triple rowPhase rowAncilla rowSignal))) action
  change HilbertOperator.applyVec
    ((program m n positive physical oracles).matrix : HilbertOperator _)
      (NormalizedVector.ket (physical.basisEquiv.symm (triple phase ancilla signal)))
      (physical.basisEquiv.symm (triple rowPhase rowAncilla rowSignal)) = _ at entry
  rw [HilbertOperator.applyVec_ket] at entry
  simpa only [NormalizedVector.ket_apply, Equiv.apply_eq_iff_eq,
    UnitaryOperator.reindex, UnitaryOperator.coe_ofMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply] using entry

/-- All native leaves realize the original projector-controlled NOT on the full interface. -/
theorem program_matrix (m n : Nat) (positive : 0 < n)
    (physical : QubitLayout (1 + (m + n))) (oracles : OracleModel) :
    UnitaryOperator.reindex physical.basisEquiv (program m n positive physical oracles).matrix =
      OrthogonalProjector.controlledNotOp (OrthogonalProjector.zeroAncilla m n) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨rowPhase, rowRest⟩, rfl⟩ := prodEquiv.surjective row
  obtain ⟨⟨rowAncilla, rowSignal⟩, rfl⟩ := prodEquiv.surjective rowRest
  obtain ⟨⟨phase, rest⟩, rfl⟩ := prodEquiv.surjective column
  obtain ⟨⟨ancilla, signal⟩, rfl⟩ := prodEquiv.surjective rest
  exact (program_entry m n positive physical oracles rowPhase phase
    rowAncilla ancilla rowSignal signal).trans
    (controlledNot_entry rowPhase phase rowAncilla ancilla rowSignal signal).symm

end
end QuantumAlg.ZeroProjector.SourceWork
