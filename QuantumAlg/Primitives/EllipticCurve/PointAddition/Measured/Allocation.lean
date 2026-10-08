/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Preparation
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Runtime
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State
import all QuantumAlg.Core.Execution.Context.Permutation.Local.Resources

/-!
# Measured point addition on the actual allocated workspace

The original body executes on exactly the entries produced by zero allocation,
fixed-bit loading, retained result cells and selector preparation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- The original measured body executes on the actually allocated entries. -/
def placedBody {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty) (after p.size) (after p.size) :=
  ContextPermutation.localCircuit (body E Q) (body_isLocal E Q) (after p.size) (body_entries p.size)

/-- One circuit initializes its own work and then executes measured controlled point addition. -/
def circuit {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty) (before p.size) (after p.size) :=
  .seq (initializeWork p) (placedBody E Q)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
