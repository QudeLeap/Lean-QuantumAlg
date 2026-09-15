/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Memory
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Bounds
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves

/-!
# Public P-256 correctness and logical-resource theorem

The fixed endpoint specializes the complete original measured ECDLP theorem.
The one named actual algorithm meets the independent one-percent failure,
native-event, resident-space, auxiliary-space and depth requirements. Its
quantum input and every external reference extension remain in the domain.
The public coordinates expose exact independent space allowances and proved
numeric ceilings for classical memory, native events and complete unit depth.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

/-- The original actual P-256 algorithm meets its independent complete-run resource problem. -/
public theorem main (I : P256.DomainParameters.PublicKeyInstance) :
    ∃ candidate : Algorithm .quantum (P256.ActualRun.Pre I)
        (P256.ActualRun.Post I) (P256.ActualRun.OutputShape I),
      candidate.Solves (problem I) :=
  ⟨algorithm I, algorithm_solves I⟩

end QuantumAlg.EllipticCurve.P256LogicalResources
