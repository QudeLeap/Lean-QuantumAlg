/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.State.Normalized
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact computational-basis action of the source zero reflection

This is a mathematical property of the existing independent source operator
`2|0><0| - I`. It does not define a circuit or grant a reflection event.
-/

namespace QuantumAlg.ZeroReflection

noncomputable section

/-- The source fixes the zero basis label and negates every other basis label. -/
lemma zeroReflectionOperator_applyVec_ket (width : Nat) (label : Fin (2 ^ width)) :
    (zeroReflectionOperator width).applyVec
        (NormalizedVector.ket (R := Qubits width) label).vec =
      if label = 0 then (NormalizedVector.ket (R := Qubits width) label).vec
      else -(NormalizedVector.ket (R := Qubits width) label).vec := by
  have overlap :
      inner ℂ (NormalizedVector.ket (R := Qubits width) 0).vec
          (NormalizedVector.ket (R := Qubits width) label).vec =
        if label = 0 then 1 else 0 := by
    change inner ℂ (EuclideanSpace.single (0 : Fin (2 ^ width)) (1 : ℂ))
      (EuclideanSpace.single label (1 : ℂ)) = _
    rw [EuclideanSpace.inner_single_left]
    simp [eq_comm]
  rw [zeroReflectionOperator, OrthogonalProjector.rankOneReflectionOp_applyVec, overlap]
  by_cases zero : label = 0
  · subst label
    simp [two_smul]
  · simp [zero]

end

end QuantumAlg.ZeroReflection
