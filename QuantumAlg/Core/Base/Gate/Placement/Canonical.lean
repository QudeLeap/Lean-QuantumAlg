/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Canonical local applications of declared gate tokens

The token's own signature fixes its local wires and dimensions. The complete
signature is selected, so no additional spectator system is introduced.
-/

namespace QuantumAlg.GateModel.Application

noncomputable section

/-- Apply one declared token on its complete canonical local physical layout. -/
public def canonical (model : GateModel) (token : model.Token) :
    Application model (model.signature token).canonicalPlacement.layout where
  occurrence := ⟨token, (model.signature token).canonicalPlacement⟩
  embedding := { position := Function.Embedding.refl _, wire_eq := fun _ => rfl }

/-- A complete canonical application has exactly the token's declared operator. -/
public lemma gateApplication_canonical_operator (model : GateModel) (token : model.Token) :
    (canonical model token).operator = model.operator token := by
  apply Subtype.ext
  ext row column
  change (canonical model token).embedding.liftOperator
    (canonical model token).occurrence.operator row column = _
  refine (QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (canonical model token).embedding (fun value => ⟨value, rfl⟩)
    (canonical model token).occurrence.operator row column).trans ?_
  rfl

end

end QuantumAlg.GateModel.Application
