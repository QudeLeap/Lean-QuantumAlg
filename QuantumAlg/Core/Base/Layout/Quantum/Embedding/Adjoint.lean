/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Gate.Unitary.Adjoint

/-!
# Adjoint targets on embedded physical subsystems

Identity on all complementary systems is retained when taking an adjoint.
The equality is used to verify an explicitly constructed inverse circuit.
-/

namespace QuantumAlg.QuantumLayout.Embedding

noncomputable section

/-- Extending by identity commutes with taking the exact adjoint operator. -/
public theorem embedding_liftOperator_star {small large : Nat}
    {source : QuantumLayout small} {target : QuantumLayout large}
    (embedding : Embedding source target) (operator : UnitaryOperator source.register) :
    embedding.liftOperator (star operator) = star (embedding.liftOperator operator) := by
  unfold liftOperator
  rw [← star_one, UnitaryOperator.unitaryOperator_prodTensor_star,
    UnitaryOperator.unitaryOperator_reindex_star, star_one]

end

end QuantumAlg.QuantumLayout.Embedding
