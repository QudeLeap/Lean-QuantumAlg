/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.FTQC.Toffoli7T.Base
public import QuantumAlg.Primitives.FTQC.CliffordLayers.Accounting
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Base
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Analysis.FTQC.CliffordT.Identities
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import Mathlib.Tactic

/-! # Literal resources of the strict seven-T, six-CNOT construction -/

namespace QuantumAlg.FTQC

open CliffordT UnitaryCircuit

noncomputable section

/-- Independent literal event budget for the six-CNOT construction. -/
public def toffoli7TEvents (oracles : OracleModel) :
    ResourcePool (.quantum CliffordTGate.model oracles) :=
  7 • {Letter.t.event oracles} +
    6 • {Resource.Event.gate (model := .quantum CliffordTGate.model oracles) .cnot} +
    2 • {Letter.h.event oracles} + 9 • {Letter.s.event oracles}

public lemma toffoli7T_eventCost (oracles : OracleModel) :
    (toffoli7TCircuit oracles).eventCost = toffoli7TEvents oracles := by
  simp only [toffoli7TCircuit, parity7T, blocks_eventCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, layer3_eventCost, cx_eventCost, ofWord_eventCost]
  apply Multiset.ext.mpr
  intro event
  cases event <;> try (rename_i coordinate; cases coordinate)
  all_goals
    simp [toffoli7TEvents, tDaggerWord, ResourcePool.ofList, ResourcePool.singleton,
      Letter.event]

public lemma toffoli7T_tCount (oracles : OracleModel) :
    circuitTCount (toffoli7TCircuit oracles) = 7 := by
  rw [circuitTCount, toffoli7T_eventCost]
  simp [toffoli7TEvents, ResourcePool.count, Letter.event]

public lemma toffoli7T_tDepth (oracles : OracleModel) :
    (toffoli7TCircuit oracles).evaluatedEventDepth (tDuration oracles) = 4 := by
  simp [toffoli7TCircuit, parity7T, tDaggerWord, tDuration, Letter.event]

/-- Every native leaf, including the S instructions in the adjoints, takes unit duration. -/
public lemma toffoli7T_eventDepth (oracles : OracleModel) :
    (toffoli7TCircuit oracles).evaluatedEventDepth (fun _ => 1) = 18 := by
  simp [toffoli7TCircuit, parity7T, tDaggerWord]

end
end QuantumAlg.FTQC
