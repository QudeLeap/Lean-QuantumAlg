/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Components.Gates.Construction
import all Mathlib.Data.List.OfFn

/-! # Equal-wire transport of one-qubit matrices and source intertwiners -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Placement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma single_equal_wires_matrix {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (same : left.wires = right.wires) (operator : UnitaryOperator (Qubits 1))
    (target : Fin leftCount) (leftQubit : (left.wire target).dimension = 2)
    (rightQubit :
      (right.wire (positionsOfEqualWires left right same target)).dimension = 2) :
    ((Gate.singleQubitAt right .empty operator
        (positionsOfEqualWires left right same target) rightQubit).matrix environment) =
      UnitaryOperator.reindex (basisOfEqualWires left right same)
        ((Gate.singleQubitAt left .empty operator target leftQubit).matrix environment) := by
  have countSame : leftCount = rightCount := by
    simpa only [QuantumLayout.wires_length] using congrArg List.length same
  subst rightCount
  have layoutSame : left = right :=
    QuantumLayout.eq_of_wire_eq (List.ofFn_injective same)
  subst right
  have corresponding : positionsOfEqualWires left left same = Equiv.refl (Fin leftCount) := by
    ext index
    rfl
  have positionSame (index : Fin leftCount) :
      positionsOfEqualWires left left same index = index :=
    congrArg (fun equivalence : Fin leftCount ≃ Fin leftCount => equivalence index)
      corresponding
  have basisSame : basisOfEqualWires left left same = Equiv.refl left.Basis := by
    ext basis index
    have value := basisOfEqualWires_value left left same basis index
    rw [positionSame index] at value
    exact value
  rw [basisSame]
  apply Subtype.ext
  ext row column
  rfl

private lemma reindex_intertwines {R S T : Register}
    (equivalence : R.Index ≃ T.Index) (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (native : UnitaryOperator R)
    (derived : (native : HilbertOperator R) * BasisEmbedding.matrix embedding =
      BasisEmbedding.matrix embedding * (source : HilbertOperator S)) :
    (UnitaryOperator.reindex equivalence native : HilbertOperator T) *
        BasisEmbedding.matrix (embedding.trans equivalence.toEmbedding) =
      BasisEmbedding.matrix (embedding.trans equivalence.toEmbedding) *
        (source : HilbertOperator S) := by
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  have nativeColumns : native (equivalence.symm row) (embedding column) =
      ∑ index : S.Index,
        if embedding index = equivalence.symm row then source index column else 0 := by
    have equal := congrArg (fun matrix => matrix (equivalence.symm row) column) derived
    simpa [Matrix.mul_apply, BasisEmbedding.matrix] using equal
  change native (equivalence.symm row) (equivalence.symm (equivalence (embedding column))) =
    ∑ index : S.Index, if equivalence (embedding index) = row then source index column else 0
  simpa only [Equiv.symm_apply_apply, equivalence.eq_symm_apply] using nativeColumns

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Placement
