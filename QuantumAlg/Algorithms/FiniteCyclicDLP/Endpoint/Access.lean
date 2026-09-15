/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Access
public import QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus

/-!
# One original encoding for finite-cyclic quantum and classical access

The original access fields require the quantum query and the classical group
operations to use the same word encoding. Their original derived recovery
parameters retain the known order, Fourier capacity and generator. This pure
interface owns no sampling, retry or classical execution implementation.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

noncomputable section

open ClassicalAlgorithms.Modular
open ClassicalRoutines.FiniteCyclicDLP

universe u

variable {G : Type u} [Group G]

/-- Quantum group access and the call-counted word implementation used by the
same endpoint.  The encoding-coherence equation prevents the recovery tail from
silently using a second group encoding. -/
public structure Access (P : KnownOrderProblem G) where
  /-- The single encoded group query used by every quantum attempt. -/
  ux : UxAccess P
  /-- Declared square and multiply calls used by classical recovery. -/
  recovery : CallCountedRecovery.Access G (orderWidth P)
  /-- Both parts use exactly the same fixed-width group encoding. -/
  recovery_encode : ∀ value,
    recovery.encode value = CShape.Value.unsignedWord (ux.encode value)

/-- The call-counted tail parameters are determined by the same known-order
problem, binary expansion, and public access. -/
def recoveryParameters (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    CallCountedRecovery.Parameters G where
  width := orderWidth P
  spec := resourceModulusSpec P (GateLevelAttempt.binaryExpansion_two_le P B)
  order_pos := by
    change 0 < P.order
    exact P.order_pos
  capacity := by
    change 12 * P.order ≤ 2 ^ orderWidth P
    simpa [oversampledOrder, fourierOversamplingFactor, fourierModulus] using
      oversampledOrder_le_fourierModulus P
  generator := P.generator
  access := A.recovery

@[simp]
theorem recoveryParameters_width (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    (recoveryParameters P B A).width = orderWidth P :=
  rfl

@[simp]
theorem recoveryParameters_modulus (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    (recoveryParameters P B A).spec.modulus = P.order :=
  rfl

@[simp]
theorem recoveryParameters_generator (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    (recoveryParameters P B A).generator = P.generator :=
  rfl

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
