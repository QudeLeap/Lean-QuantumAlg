/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Exponents.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness

/-!
# Shared Montgomery seed in full-bank coordinates

The arithmetic seed, original auxiliary preparation and zero selector define
a full-bank basis label for every Reference coordinate. This label adds no
input-state assumption and does not construct or run an allocation program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Initialization

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement ScalarMultiplication.MeasuredPlacement.Allocation
open MAU.Inversion.SharedEEA ECDLP.Measured ContextUnion
open MeasuredPointAddition
open Recovery.Reference.Measured.CommonBank Recovery.Reference.Exponents

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)

variable [Fact p.Prime] (fieldTail m : Nat) (seed : AffinePoint E)

private def radixFieldWords (fieldTail : Nat) (x y : ZMod p) :
    Fin (2 ^ p.size) × Fin (2 ^ p.size) :=
  let scale : ZMod p := (2 : ZMod p) ^ fieldTail.succ
  (fieldWord (p := p) (scale * x), fieldWord (p := p) (scale * y))

/-- The complete arithmetic/selector seed at every external Reference label. -/
def resetBank (Reference : Register) (reference : Reference.Index) : Bank p.size Reference :=
  bankAssembly p.size (2 * m) Reference
    ((BasisPreparation.zero (indexedLayout p.size (2 * m))).value,
      (InPlacePreparation.preparation p).value,
      radixFieldWords fieldTail seed.x seed.y, reference)

end

end Initialization
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
