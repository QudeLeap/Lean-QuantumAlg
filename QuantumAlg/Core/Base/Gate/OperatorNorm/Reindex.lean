/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Gate.OperatorNorm
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Exact operator-norm transport across basis labels

Changing finite basis labels is an isometric star-algebra equivalence. Thus
rotation certificates retain their original error and exact phase when their
mathematical matrices are placed in a physical layout's coordinate basis.
-/

namespace QuantumAlg.HilbertOperator

noncomputable section

variable {R S : Register}

private def reindexStarAlgEquiv (equivalence : R.Index ≃ S.Index) :
    HilbertOperator R ≃⋆ₐ[ℂ] HilbertOperator S :=
  { Matrix.reindexAlgEquiv ℂ ℂ equivalence with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Relabeling both matrix axes preserves the L2 operator norm exactly. -/
public lemma opNorm_reindex (equivalence : R.Index ≃ S.Index) (operator : HilbertOperator R) :
    opNorm (R := S) (operator.submatrix equivalence.symm equivalence.symm) =
      opNorm operator := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact NonUnitalStarAlgHom.norm_map (reindexStarAlgEquiv equivalence)
    (reindexStarAlgEquiv equivalence).injective operator

/-- The error between exact-phase unitary targets is unchanged by a common basis transport. -/
public lemma opNorm_reindex_sub (equivalence : R.Index ≃ S.Index)
    (first second : UnitaryOperator R) :
    opNorm ((UnitaryOperator.reindex equivalence first : HilbertOperator S) -
      (UnitaryOperator.reindex equivalence second : HilbertOperator S)) =
      opNorm ((first : HilbertOperator R) - (second : HilbertOperator R)) := by
  exact opNorm_reindex equivalence ((first : HilbertOperator R) - (second : HilbertOperator R))

end

end QuantumAlg.HilbertOperator
