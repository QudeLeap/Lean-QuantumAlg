/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Native
import all QuantumAlg.Core.Base.Accounting.Weighted

/-! # Quantum-duration weight of the same original native gate word -/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.NativeResources

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Every original native instruction contributes exactly one of these three coordinates. -/
lemma word_length_coordinates (gates : List (GateSpec encoding)) :
    gates.length = (gates.map toffoliMultiplicity).sum +
      (gates.map cnotMultiplicity).sum + (gates.map xMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      cases gate <;>
        simp only [List.length_cons, List.map_cons, List.sum_cons,
          toffoliMultiplicity, cnotMultiplicity, xMultiplicity] <;> omega

/-- The actual full-model native pool has its literal gate-list length as quantum weight. -/
lemma word_quantumWeight (physical : QubitLayout encoding.width)
    (gates : List (GateSpec encoding)) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      ((programList physical oracles gates).eventCost operations services) = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change ResourcePool.weightedCount Resource.Event.quantumDuration
        ((gate.program physical oracles).eventCost operations services +
          (programList physical oracles rest).eventCost operations services) = _
      rw [ResourcePool.weightedCount_add, gate_eventCost, ih,
        ResourcePool.weightedCount_singleton]
      cases gate <;> simp [event, Nat.add_comm]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.NativeResources
