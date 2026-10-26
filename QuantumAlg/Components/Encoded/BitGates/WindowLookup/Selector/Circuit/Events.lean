/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Resources
import all QuantumAlg.Core.Base.Accounting.OracleWeight

/-!
# Complete native pools for actual hybrid selector traversals

The existing arbitrary-weight resource theorem applies to each literal event
indicator. This retains all callback coordinates, including width-indexed
classical labels, while the five native fork gates use their fixed alphabet.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

/-- The independent five native events of every actual hybrid selector fork. -/
def hybridForkEnvelope (oracles : OracleModel) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) :
    ResourcePool (.quantum AlgorithmGate.model oracles operations services) :=
  2 • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate .singleQubit) +
    (2 • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate .toffoli) +
      ResourcePool.singleton
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate .cnot))

/-- Arbitrary complete callback allowances compose over every real retained selector leaf. -/
lemma circuitAt_pool_le {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel} (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (budget : ResourcePool (.quantum AlgorithmGate.model oracles operations services))
    (callbackBound : ∀ label path, (callback label).resourcePool path ≤ budget)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (path : (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path) :
    (frame.circuitAt physical sameWires callback tree depth fits offset bounded).resourcePool path ≤
      tree.forks • hybridForkEnvelope oracles operations services + tree.leaves • budget := by
  classical
  apply ResourcePool.le_iff_count.mpr
  intro focus
  let weight : Resource.Event (.quantum AlgorithmGate.model oracles operations services) → Nat :=
    fun event => if event = focus then 1 else 0
  have indicator (pool : ResourcePool (.quantum AlgorithmGate.model oracles operations services)) :
      ResourcePool.weightedCount weight pool = ResourcePool.count focus pool :=
    ResourcePool.weightedCount_eq_count_of_indicator weight focus (fun _ => rfl) pool
  have actual := frame.circuitAt_weight_le physical sameWires callback weight
    (ResourcePool.count focus budget) (fun label selected => by
      rw [indicator]
      exact ResourcePool.le_iff_count.mp (callbackBound label selected) focus)
    tree depth fits offset bounded path
  rw [indicator] at actual
  simpa only [hybridForkWeight, weight, hybridForkEnvelope, ResourcePool.count_add,
    ResourcePool.count_nsmul, ResourcePool.count_singleton, Nat.mul_one, Nat.add_assoc] using actual

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame
