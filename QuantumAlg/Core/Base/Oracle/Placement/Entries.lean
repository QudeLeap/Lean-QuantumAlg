/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.Oracle.Model
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Declared-query entries at the original physical coordinates

Splitting an actual application reads its declared argument values and the
entire untouched complement. The matrix entry comes from the fixed query
operator, with identity on that complement and no independent operator input.
-/

namespace QuantumAlg.OracleModel.Application

noncomputable section

variable {model : OracleModel} {count : Nat} {layout : QuantumLayout count}

/-- Read the declared argument order and the complete complementary subsystem. -/
@[expose]
public def basisEquiv (application : Application model layout) :
    layout.Basis ≃ (model.signature application.occurrence.query).Basis ×
      layout.ComplementBasis application.embedding.selection :=
  application.embedding.splitBasis.trans
    (Equiv.prodCongr application.occurrence.placement.indexEquiv (Equiv.refl _))

/-- The declared argument retains the original physical system's computational value. -/
public lemma oracleApplication_selected_value (application : Application model layout)
    (basis : layout.Basis)
    (index : Fin (model.signature application.occurrence.query).systemCount) :
    ((application.basisEquiv basis).1 index).val =
      (basis (application.embedding.position index)).val := by
  rfl

/-- The untouched complement retains every original computational value. -/
public lemma oracleApplication_complement_value (application : Application model layout)
    (basis : layout.Basis)
    (index : QuantumLayout.SelectedPosition application.embedding.selectionᶜ) :
    (application.basisEquiv basis).2 index = basis index.val := by
  rfl

/-- The actual matrix entry is the declared query entry times full complement identity. -/
public lemma oracleApplication_model_entry (application : Application model layout)
    (environment : Interpretation model)
    (row column : layout.Basis) :
    application.operator environment row column =
      environment.operator application.occurrence.query
        (application.basisEquiv row).1 (application.basisEquiv column).1 *
        (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) := by
  rw [oracle_application_operator_entry]
  rfl

end

end QuantumAlg.OracleModel.Application
