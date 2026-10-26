/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Feed

/-!
# Selected mathematical source blocks in one fixed observation space

All windows may use the same virtual source register. A proved basis
partition selects the current mathematical input block and retains every
other source coordinate. This is an observation-space construction, with
no Circuit, allocation, physical permutation or resource assertion.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

/-- Feed one selected mathematical block, keeping the entire source and actual complement. -/
def selectedFeedBasis (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (row : (ctx.register.prod (S.prod Reference)).Index) :
    (ctx.register.prod (S.prod Reference)).Index :=
  let physical := bankCoordinates ports.wires ports.qubits row.1
  let source := partition row.2.1
  ((bankCoordinates ports.wires ports.qubits).symm
      ((binaryEquiv active).symm source.1, physical.2),
    (partition.symm (binaryEquiv active physical.1, source.2), row.2.2))

lemma window_selectedSourceFeed_involutive (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register) :
    Function.Involutive (selectedFeedBasis ports partition Reference) := by
  rintro ⟨physical, source, reference⟩
  simp only [selectedFeedBasis, Equiv.apply_symm_apply, Equiv.symm_apply_apply, Prod.eta]

def selectedFeedEquiv (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register) :
    Equiv.Perm (ctx.register.prod (S.prod Reference)).Index :=
  (window_selectedSourceFeed_involutive ports partition Reference).toPerm
    (selectedFeedBasis ports partition Reference)

/-- Every selected feed is a mathematical unitary on the same fixed observation-space carrier. -/
def selectedFeedOperator (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register) :
    UnitaryOperator (ctx.register.prod (S.prod Reference)) :=
  UnitaryOperator.ofPerm (selectedFeedEquiv ports partition Reference)

lemma window_selectedSourceFeed_saved (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (row : (ctx.register.prod (S.prod Reference)).Index) :
    (partition (selectedFeedBasis ports partition Reference row).2.1).2 =
        (partition row.2.1).2 ∧
      (selectedFeedBasis ports partition Reference row).2.2 = row.2.2 := by
  simp only [selectedFeedBasis, Equiv.apply_symm_apply, and_self]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
