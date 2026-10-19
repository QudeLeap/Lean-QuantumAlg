/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Applying a native occurrence on its own physical layout

The entire ambient layout consists of the occurrence's declared systems. The
identity embedding introduces no spectator, so the full application has exactly
the model-owned local operator, including its phase.
-/

namespace QuantumAlg.GateModel.Application

variable {model : GateModel}

/-- Apply an occurrence to precisely its own ordered, dimension-correct physical systems. -/
@[expose]
public def onOwnLayout (occurrence : Occurrence model) :
    Application model occurrence.placement.layout where
  occurrence := occurrence
  embedding :=
    { position := Function.Embedding.refl _
      wire_eq := fun _ => rfl }

/-- The own-layout application retains the actual local operator without a residual spectator. -/
public lemma onOwnLayout_operator (occurrence : Occurrence model) :
    (onOwnLayout occurrence).operator = occurrence.operator := by
  apply Subtype.ext
  ext row column
  rw [application_operator_entry]
  have selected (basis : occurrence.placement.layout.Basis) :
      ((onOwnLayout occurrence).embedding.splitBasis basis).1 = basis := by
    funext index
    apply Fin.ext
    exact (onOwnLayout occurrence).embedding.embedding_splitBasis_selected_value basis index
  have complement :
      ((onOwnLayout occurrence).embedding.splitBasis row).2 =
        ((onOwnLayout occurrence).embedding.splitBasis column).2 := by
    funext position
    exact False.elim ((Finset.mem_compl.mp position.property)
      (Finset.mem_map_of_mem (onOwnLayout occurrence).embedding.position
        (Finset.mem_univ position.val)))
  rw [selected row, selected column, if_pos complement, mul_one]
  rfl

end QuantumAlg.GateModel.Application
