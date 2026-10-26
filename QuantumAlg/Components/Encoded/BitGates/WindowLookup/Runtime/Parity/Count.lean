/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Resources

/-! # Runtime classical AND/XOR instructions emit no quantum gate coordinates -/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {services : ClassicalOracleModel}

private lemma fold_gate_count (coordinate : AlgorithmGate.Coordinate)
    (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (foldProgram (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((foldProgram parity temporary pairs).resourcePool path) = 0 := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
        (ResourcePool.ofList
          ([.classicalOperation (.bit .and), .classicalOperation (.bit .xor)] ++
            (foldProgram parity temporary rest).eventTrace path.2)) = 0
      rw [ResourcePool.ofList_append, ResourcePool.count_add]
      change 0 + ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
        ((foldProgram parity temporary rest).resourcePool path.2) = 0
      rw [ih]

/-- Every complete real runtime parity program has zero multiplicity at every quantum gate. -/
lemma program_gate_count (coordinate : AlgorithmGate.Coordinate)
    (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (program (oracles := oracles) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((program parity temporary pairs).resourcePool path) = 0 := by
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
    (ResourcePool.ofList ([.classicalOperation (.bit .xor)] ++
      (foldProgram parity temporary pairs).eventTrace path.2)) = 0
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change 0 + ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
    ((foldProgram parity temporary pairs).resourcePool path.2) = 0
  rw [fold_gate_count]

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
