/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Placement

/-!
# Exact diagonal action on selected physical systems

A diagonal interpretation of the actual model token remains diagonal when
placed in a larger layout. Its phase reads only the selected coordinates;
every complementary system is preserved. The premise concerns the existing
token operator and does not grant a new native gate or change its accounting.
-/

namespace QuantumAlg.GateModel.Application

noncomputable section

variable {model : GateModel} {count : Nat} {layout : QuantumLayout count}

/-- A placed diagonal token retains its exact phase and the full untouched complement. -/
public theorem application_operator_diagonal (application : Application model layout)
    (weight : (model.signature application.occurrence.token).Basis → Complex)
    (semantics :
      (model.operator application.occurrence.token :
        HilbertOperator (model.signature application.occurrence.token).register) =
          Matrix.diagonal weight) :
    (application.operator : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis => weight (application.basisEquiv basis).1) := by
  ext row column
  rw [application_operator_entry]
  change model.operator application.occurrence.token
    (application.basisEquiv row).1 (application.basisEquiv column).1 *
    (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [semantics]
  by_cases same : row = column
  · subst column
    simp
  · by_cases selected : (application.basisEquiv row).1 = (application.basisEquiv column).1
    · have complement : (application.basisEquiv row).2 ≠ (application.basisEquiv column).2 :=
        fun equal => same (application.basisEquiv.injective (Prod.ext selected equal))
      simp [same, selected, complement]
    · simp [same, selected]

end

end QuantumAlg.GateModel.Application
