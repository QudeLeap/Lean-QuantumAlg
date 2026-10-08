/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BasisMap.Contract

/-!
# Clean composition for elliptic-curve circuit endpoints

This module packages the clean-work-register composition pattern used by
elliptic-curve point-operation stacks.  It is generic over the data and work
register labels; elliptic-curve modules instantiate it with point-operation
endpoints.  The clean-work convention reflects the source accounting rule that
auxiliary qubits for the elliptic-curve modular-arithmetic circuits are returned
to their original states [RNSL17, ECDLP.tex:555,657-684].
-/

section

namespace QuantumAlg
namespace EllipticCurve

namespace CleanComposition

variable {Data Work : Type}

/-- Sequentially compose a list of clean reversible maps, starting from the
identity map.  The list order is execution order. -/
def composeList (Data Work : Type)
    (steps : List (WorkRegister.CleanReversibleMap Data Work)) :
    WorkRegister.CleanReversibleMap Data Work :=
  steps.foldl WorkRegister.CleanReversibleMap.sequential
    (WorkRegister.CleanReversibleMap.identity Data Work)

/-- The composed clean map preserves the work-register label. -/
theorem composeList_preserves_work
    (steps : List (WorkRegister.CleanReversibleMap Data Work)) (x : Data × Work) :
    ((composeList Data Work steps).perm x).2 = x.2 :=
  (composeList Data Work steps).preservesWork x

end CleanComposition

end EllipticCurve
end QuantumAlg

end
