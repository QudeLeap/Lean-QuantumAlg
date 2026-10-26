/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Base
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
import all QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Base
import all QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Entries.Low
import all QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Entries.High
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Realization
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Analysis.FTQC.CliffordT.Identities
import all QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.WireAddress
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Matrix.Diagonal
import all QuantumAlg.Util.Sum
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import Mathlib.Tactic

/-!
# A seven-T, three-stage Toffoli on three data qubits

The parity schedule implements the T-depth-three bound discussed in
Amy, Maslov, Mosca and Roetteler, MeetintheMiddlev4.tex:565-578.
It is a derived parity-network schedule, not a transcription of their figure.
The third stage is followed by exact uncomputation of the parity basis.

-/

public section

namespace QuantumAlg.FTQC

open CliffordT Gate UnitaryCircuit
open NormalizedVector

noncomputable section
lemma toffoliTDepth3Core_matrix (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    (toffoliTDepth3Core oracles).binaryMatrix environment = toffoliOp := by
  apply Subtype.ext
  ext i j
  fin_cases i
  · exact toffoliTDepth3Row0 environment j
  · exact toffoliTDepth3Row1 environment j
  · exact toffoliTDepth3Row2 environment j
  · exact toffoliTDepth3Row3 environment j
  · exact toffoliTDepth3Row4 environment j
  · exact toffoliTDepth3Row5 environment j
  · exact toffoliTDepth3Row6 environment j
  · exact toffoliTDepth3Row7 environment j

/-- Exact three-qubit realization with no auxiliary system or auxiliary-state hypothesis. -/
def toffoliTDepth3 (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization CliffordTGate.model oracles
      (QuantumSignature.qubits 3).canonicalPlacement.layout (fun _ => toffoliPhysicalOp) where
  circuit := toffoliTDepth3Core oracles
  matrix_eq environment := matrix_of_binaryMatrix_eq _ _ environment
    (toffoliTDepth3Core_matrix oracles environment)

lemma toffoliTDepth3_tCount (oracles : OracleModel) :
    circuitTCount (toffoliTDepth3Core oracles) = 7 := by
  simp [circuitTCount, toffoliTDepth3Core, parityTDepth3, parityBasis, tDaggerWord,
    Letter.circuit_eventCost, ResourcePool.count, ResourcePool.singleton,
    Letter.event]

lemma toffoliTDepth3_tDepth (oracles : OracleModel) :
    (toffoliTDepth3Core oracles).evaluatedEventDepth (tDuration oracles) = 3 := by
  simp [toffoliTDepth3Core, parityTDepth3, parityBasis, tDaggerWord, tDuration, Letter.event]

lemma toffoliTDepth3_eventDepth (oracles : OracleModel) :
    (toffoliTDepth3Core oracles).evaluatedEventDepth (fun _ => 1) = 21 := by
  simp [toffoliTDepth3Core, parityTDepth3, parityBasis, tDaggerWord]

lemma toffoliTDepth3_eventCost (oracles : OracleModel) :
    (toffoliTDepth3Core oracles).eventCost =
      7 • {Letter.t.event oracles} +
        10 • {Resource.Event.gate (model := .quantum CliffordTGate.model oracles) .cnot} +
        2 • {Letter.h.event oracles} + 9 • {Letter.s.event oracles} := by
  simp only [toffoliTDepth3Core, parityTDepth3, parityBasis, blocks_eventCost,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_append,
    List.sum_append, List.map_reverse, List.sum_reverse,
    layer3_eventCost, cx_eventCost, ofWord_eventCost]
  apply Multiset.ext.mpr
  intro event
  cases event <;> try (rename_i coordinate; cases coordinate)
  all_goals
    simp [tDaggerWord, ResourcePool.ofList, ResourcePool.singleton, Letter.event]

end

end QuantumAlg.FTQC
