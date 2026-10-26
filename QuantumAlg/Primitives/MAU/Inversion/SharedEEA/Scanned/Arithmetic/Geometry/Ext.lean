/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout

/-! # Complete geometry frame equality retains both address and high carry -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open NumberTheory.SharedEEA

/-- Original source, full prefix and complete temporary target determine all actual state fields. -/
lemma data_eq_of_source_prefix_target (width : Nat) (first second : Data width)
    (source : first.1 = second.1) (prefixes : first.2.2.1 = second.2.2.1)
    (targets : targetValue width first = targetValue width second) : first = second := by
  refine Prod.ext source (Prod.ext ?_ (Prod.ext prefixes ?_))
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have bit := congrArg (fun value : BitVec (fullWidth width) => value.getMsbD (index + 1)) targets
    simpa only [targetValue, BitVec.getMsbD_cons_succ] using bit
  · have bit := congrArg (fun value : BitVec (fullWidth width) => value.getMsbD 0) targets
    simpa only [targetValue, BitVec.getMsbD_cons_zero] using bit

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
