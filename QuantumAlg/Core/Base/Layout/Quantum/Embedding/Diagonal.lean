/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding

/-!
# Diagonal operators on embedded physical subsystems

Identity extension retains the selected diagonal phase and leaves every
complementary coordinate unchanged. This is an operator equality, without a
basis-state or initialized-spectator assumption.
-/

namespace QuantumAlg.QuantumLayout.Embedding

noncomputable section

variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- A diagonal operator stays diagonal under physical embedding, with its exact selected phase. -/
public theorem embedding_liftOperator_diagonal (placement : Embedding source target)
    (operator : UnitaryOperator source.register) (weight : source.Basis → Complex)
    (diagonal : (operator : HilbertOperator source.register) = Matrix.diagonal weight) :
    (placement.liftOperator operator : HilbertOperator target.register) =
      Matrix.diagonal (fun basis => weight (placement.splitBasis basis).1) := by
  ext row column
  rw [liftOperator_entry, diagonal]
  by_cases same : row = column
  · subst column
    simp
  · by_cases selected : (placement.splitBasis row).1 = (placement.splitBasis column).1
    · have complement : (placement.splitBasis row).2 ≠ (placement.splitBasis column).2 :=
        fun equal => same (placement.splitBasis.injective (Prod.ext selected equal))
      simp [same, selected, complement]
    · simp [same, selected]

end

end QuantumAlg.QuantumLayout.Embedding
