/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256
public import QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Resources
import all QuantumAlg.Algorithms.EllipticCurve.P256
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Resources

/-!
# Complete original-input correctness and resources of the same actual window algorithm

The registered endpoint and all seven numeric coordinates use the same literal
paid algorithm. This consumer does not change the original public input domain,
owned-bank zero requirement or borrowed-state and Reference obligations.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

/-- The actual paid algorithm meets the full original problem and all seven independent bounds. -/
public lemma completeContract (I : DomainParameters.PublicKeyInstance) :
    (algorithm I).Solves (P256LogicalResources.problem I) ∧
      ∀ path : (algorithm I).run.code.Path, Resources.SevenCoordinateBounds I path :=
  ⟨P256LogicalResources.candidate_solves I, Resources.run_sevenCoordinates I⟩

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
