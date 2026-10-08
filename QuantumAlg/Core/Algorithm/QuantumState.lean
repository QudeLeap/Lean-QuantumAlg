/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Sealed computational-basis state descriptions

`KnownPreparation n` selects a finite computational-basis value and derives its
normalized mathematical vector. It supplies no event, cost, depth or executable
transition. Actual owned initialization and its accounting belong to the typed
execution program.
-/

section

namespace QuantumAlg

/-- A sealed finite computational-basis description.

The constructor selects only basis values; normalization follows from the
mathematical ket. This descriptor does not grant a preparation instruction. -/
@[nolint structureInType]
structure KnownPreparation (qubitCount : Nat) where
  private mk ::
  private basisValue : Fin (2 ^ qubitCount)

namespace KnownPreparation

/-- Prepare the all-zero computational basis state of one fixed width. -/
def zero (qubitCount : Nat) : KnownPreparation qubitCount :=
  ⟨⟨0, Nat.two_pow_pos qubitCount⟩⟩

/-- Prepare one explicit member of the finite computational basis. -/
def basis {qubitCount : Nat} (value : Fin (2 ^ qubitCount)) :
    KnownPreparation qubitCount :=
  ⟨value⟩

/-- Normalized semantics fixed by a sealed preparation constructor. -/
noncomputable def normalized {qubitCount : Nat} :
    KnownPreparation qubitCount → NormalizedVector (Qubits qubitCount)
  | preparation => NormalizedVector.ket preparation.basisValue

/-- The public semantics of an explicit computational-basis preparation. -/
@[simp] theorem normalized_basis {qubitCount : Nat}
    (value : Fin (2 ^ qubitCount)) :
    (KnownPreparation.basis value).normalized =
      NormalizedVector.ket value :=
  rfl

/-- The public semantics of the all-zero preparation. -/
@[simp] theorem normalized_zero (qubitCount : Nat) :
    (KnownPreparation.zero qubitCount).normalized =
      NormalizedVector.ket (R := Qubits qubitCount)
        ⟨0, Nat.two_pow_pos qubitCount⟩ :=
  rfl


end KnownPreparation

end QuantumAlg

end
