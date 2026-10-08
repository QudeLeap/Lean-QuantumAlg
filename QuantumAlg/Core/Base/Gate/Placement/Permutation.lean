/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Model
public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding

/-!
# Permutation semantics of a placed native gate

A proved permutation interpretation of the model's actual token lifts to its
selected wires, leaving every complementary coordinate unchanged. This is a
semantic theorem about an existing application, with no new circuit constructor
and no way to replace the model-owned operator.
-/

namespace QuantumAlg.GateModel.Application

noncomputable section

variable {model : GateModel} {count : Nat} {layout : QuantumLayout count}

/-- Read the model's ordered argument values and the full untouched complement. -/
@[expose]
public def basisEquiv (application : Application model layout) :
    layout.Basis ≃ (model.signature application.occurrence.token).Basis ×
      layout.ComplementBasis application.embedding.selection :=
  application.embedding.splitBasis.trans
    (Equiv.prodCongr application.occurrence.placement.indexEquiv (Equiv.refl _))

/-- Reassemble a local permutation result on the same physical wires and complement. -/
@[expose]
public def liftPermutation (application : Application model layout)
    (permutation : Equiv.Perm (model.signature application.occurrence.token).Basis) :
    Equiv.Perm layout.Basis :=
  (application.basisEquiv.trans (Equiv.prodCongr permutation (Equiv.refl _))).trans
    application.basisEquiv.symm

/-- Equality after the lifted action checks both local outputs and the whole complement. -/
public theorem liftPermutation_eq_iff (application : Application model layout)
    (permutation : Equiv.Perm (model.signature application.occurrence.token).Basis)
    (row column : layout.Basis) :
    application.liftPermutation permutation row = column ↔
      permutation (application.basisEquiv row).1 = (application.basisEquiv column).1 ∧
        (application.basisEquiv row).2 = (application.basisEquiv column).2 := by
  change application.basisEquiv.symm
    (permutation (application.basisEquiv row).1, (application.basisEquiv row).2) = column ↔ _
  rw [Equiv.symm_apply_eq]
  simp only [Prod.ext_iff]

/-- An exact permutation interpretation of the actual token determines its full ambient operator. -/
public theorem operator_ofPerm (application : Application model layout)
    (permutation : Equiv.Perm (model.signature application.occurrence.token).Basis)
    (semantics : model.operator application.occurrence.token =
      UnitaryOperator.ofPerm permutation) :
    application.operator = UnitaryOperator.ofPerm (application.liftPermutation permutation) := by
  apply Subtype.ext
  ext row column
  rw [application_operator_entry]
  change model.operator application.occurrence.token
    (application.basisEquiv row).1 (application.basisEquiv column).1 *
    (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [semantics, UnitaryOperator.ofPerm_entry, UnitaryOperator.ofPerm_entry]
  have matching := application.liftPermutation_eq_iff permutation row column
  by_cases actual : application.liftPermutation permutation row = column
  · obtain ⟨localMatch, complementMatch⟩ := matching.mp actual
    rw [if_pos actual, if_pos localMatch, if_pos complementMatch, one_mul]
  · by_cases localMatch :
        permutation (application.basisEquiv row).1 = (application.basisEquiv column).1
    · have complementMismatch :
          (application.basisEquiv row).2 ≠ (application.basisEquiv column).2 :=
        fun same => actual (matching.mpr ⟨localMatch, same⟩)
      rw [if_neg actual, if_pos localMatch, if_neg complementMismatch, mul_zero]
    · rw [if_neg actual, if_neg localMatch, zero_mul]

end

end QuantumAlg.GateModel.Application
