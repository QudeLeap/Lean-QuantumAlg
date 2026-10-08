/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.SevenCoordinates
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Memory
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.SevenCoordinates

/-!
# Complete original P-256 correctness, physical cycles and numeric resources

The registered main directly specializes the accepted arbitrary-width
contract to the standard parameters. It binds one named actual algorithm
to original ninety-nine-percent success, state and joint borrowed restoration,
physically complete cycles and every independent numeric resource coordinate.
The whole chronological depth is retained separately from maximum cycle depth.
All ceilings are conservative implementation bounds [PZ03, ecc.tex:448-556].
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

/-- The same original P-256 run satisfies correctness, complete cycles and all seven bounds. -/
public theorem main (I : P256.DomainParameters.PublicKeyInstance) :
    ∃ cycles : Algorithm.CycleSolves (algorithm I) (completeCycleProblem I),
      (algorithm I).Solves (problem I) ∧
        (∀ path : (algorithm I).run.code.Path, SevenCoordinateBounds I cycles path) ∧
        (∀ path : (algorithm I).run.code.Path,
          (algorithm I).run.code.depth (fun _ => 1) path ≤ Limits.wholeRunDepth) :=
  algorithm_completeContract I

end QuantumAlg.EllipticCurve.P256LogicalResources
