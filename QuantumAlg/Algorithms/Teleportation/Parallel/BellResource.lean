/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Density

public import QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Algorithms.Teleportation.Parallel.Coordinates
import all QuantumAlg.Primitives.BellPair.Construction
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.State.Density.PureMarginal
import all QuantumAlg.Core.Execution.Reindex
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A local shared Bell promise preserves arbitrary external reference correlations

Only the supplied Bell subsystem is promised pure. The independent local
promise makes no statement about the unknown input, the classical result
cells, or an external reference. Positivity then forces the Bell factor in
every complete input-reference matrix entry [dW19, qcnotes.tex:785,809].
This is a consequence of the local promise, not an additional admission
condition on an external reference or on conditional classical slices.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open scoped BigOperators

/-- The shared resource is the normalized tensor of the source's Bell pairs. -/
public def bellBank : (count : Nat) → NormalizedVector (bellRegister count)
  | 0 => NormalizedVector.ket Fin.elim0
  | count + 1 =>
      NormalizedVector.reindex (Fin.consEquiv (fun _ : Fin (count + 1) => Fin 4))
        (NormalizedVector.prodTensor bell (bellBank count))

/-- Its tensor amplitudes retain both halves of every original shared pair. -/
lemma bellBank_apply (count : Nat) (basis : (bellRegister count).Index) :
    bellBank count basis = ∏ index : Fin count, bell (basis index) := by
  induction count with
  | zero => simp [bellBank, NormalizedVector.ket_apply, Subsingleton.elim basis Fin.elim0]
  | succ count ih =>
      rw [bellBank, NormalizedVector.reindex_apply, NormalizedVector.prodTensor_apply]
      change bell (basis 0) * bellBank count (fun index => basis index.succ) = _
      rw [ih, Fin.prod_univ_succ]

/-- Regroup exactly the supplied Bell wires before the original unknown input wires. -/
def bellInputBasis (count : Nat) : (context count).register.Index ≃
    ((bellRegister count).prod (inputRegister count)).Index :=
  (inputBellBasis count).trans (Equiv.prodComm _ _)

/-- Local Bell observation, defined entirely without an external reference. -/
public def localBellMarginal (count : Nat) (state : DensityOperator (context count).register) :
    DensityOperator (bellRegister count) :=
  (state.reindex (S := (bellRegister count).prod (inputRegister count))
    (bellInputBasis count)).marginalLeft

/-- The same physical regrouping retains the original input and the complete external reference. -/
def bellReferenceBasis (count : Nat) (Reference : Register) :
    ((context count).register.prod Reference).Index ≃
      ((bellRegister count).prod ((inputRegister count).prod Reference)).Index :=
  ((bellInputBasis count).prodCongr (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc _ _ _)

/-- Observing the Bell subsystem commutes with forgetting only the external reference. -/
lemma bellReference_marginal (count : Nat) (Reference : Register)
    (state : DensityOperator ((context count).register.prod Reference)) :
    (state.reindex (S := (bellRegister count).prod ((inputRegister count).prod Reference))
      (bellReferenceBasis count Reference)).marginalLeft =
        localBellMarginal count state.marginalLeft := by
  apply DensityOperator.ext
  ext row column
  simp only [localBellMarginal, DensityOperator.marginalLeft_matrix,
    DensityOperator.reindex_entry]
  change (∑ entry : (inputRegister count).Index × Reference.Index,
    state.matrix ((inputBellBasis count).symm (entry.1, row), entry.2)
      ((inputBellBasis count).symm (entry.1, column), entry.2)) =
    ∑ input : (inputRegister count).Index, ∑ reference : Reference.Index,
      state.matrix ((inputBellBasis count).symm (input, row), reference)
        ((inputBellBasis count).symm (input, column), reference)
  exact Fintype.sum_prod_type _

/-- The local pure resource forces the correct complete input-reference factorization. -/
lemma bellResource_joint_entry (count : Nat) (Reference : Register)
    (state : DensityOperator ((context count).register.prod Reference))
    (promised : localBellMarginal count state.marginalLeft =
      DensityOperator.ofPure (bellBank count))
    (row column : (inputRegister count).Index) (bellRow bellColumn : (bellRegister count).Index)
    (refRow refColumn : Reference.Index) :
    state.matrix ((inputBellBasis count).symm (row, bellRow), refRow)
      ((inputBellBasis count).symm (column, bellColumn), refColumn) =
      (bellBank count bellRow * star (bellBank count bellColumn)) *
        ∑ resource : (bellRegister count).Index,
          state.matrix ((inputBellBasis count).symm (row, resource), refRow)
            ((inputBellBasis count).symm (column, resource), refColumn) := by
  let framed : DensityOperator
      ((bellRegister count).prod ((inputRegister count).prod Reference)) :=
    state.reindex (bellReferenceBasis count Reference)
  have framedPure : framed.marginalLeft = DensityOperator.ofPure (bellBank count) :=
    (bellReference_marginal count Reference state).trans promised
  exact DensityOperator.pureMarginal_entry framed (bellBank count) framedPure
    bellRow bellColumn (row, refRow) (column, refColumn)

end

end QuantumAlg.QuantumTeleportation.Parallel
