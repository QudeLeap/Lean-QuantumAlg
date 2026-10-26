/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection

/-!
# The same source feed in two complete complement coordinates

Two descriptions of the saved source may have different carriers. If they
select and replace the same current block of the same full label, they give
exactly the same feed on every physical, source and Reference coordinate.
Only mathematical source coordinates are compared here.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {S T FirstRest SecondRest Rest : Register}

/-- Complete current replacement, rather than a complement carrier, determines the feed. -/
lemma window_sourceFeed_partitions_basis (ports : Ports ctx totalBits active)
    (first : S.Index ≃ (Qubits active).Index × FirstRest.Index)
    (second : S.Index ≃ (Qubits active).Index × SecondRest.Index)
    (selected : ∀ label, (first label).1 = (second label).1)
    (replace : ∀ label current, first.symm (current, (first label).2) =
      second.symm (current, (second label).2))
    (Reference : Register) (row : (ctx.register.prod (S.prod Reference)).Index) :
    selectedFeedBasis ports first Reference row = selectedFeedBasis ports second Reference row := by
  dsimp only [selectedFeedBasis]
  rw [selected, replace]

/-- Equal full source replacements give the same mathematical feed unitary. -/
lemma window_sourceFeed_partitions_operator (ports : Ports ctx totalBits active)
    (first : S.Index ≃ (Qubits active).Index × FirstRest.Index)
    (second : S.Index ≃ (Qubits active).Index × SecondRest.Index)
    (selected : ∀ label, (first label).1 = (second label).1)
    (replace : ∀ label current, first.symm (current, (first label).2) =
      second.symm (current, (second label).2)) (Reference : Register) :
    selectedFeedOperator ports first Reference = selectedFeedOperator ports second Reference := by
  unfold selectedFeedOperator
  congr 1
  apply Equiv.ext
  exact window_sourceFeed_partitions_basis ports first second selected replace Reference

/-- The current source H tensor transports through the same full label coordinates. -/
lemma window_source_selectedPreparation_reindex
    (coordinates : S.Index ≃ T.Index)
    (partition : T.Index ≃ (Qubits active).Index × Rest.Index) :
    selectedUniformPreparation (coordinates.trans partition) =
      UnitaryOperator.reindex coordinates.symm (selectedUniformPreparation partition) := by
  apply Subtype.ext
  rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
