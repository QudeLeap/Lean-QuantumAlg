/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Base
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Resources
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Base
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Entries.Low
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Entries.High
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
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
# Seven-T Toffoli with four T stages

The phase polynomial is a+b+c-(a xor b)-(b xor c)+(a xor b xor c)-(a xor c).
It equals 4abc modulo eight. Hadamard conjugation of its target gives Toffoli.
The seven-T, six-CNOT construction follows Nielsen and Chuang, Figure 4.9
(citation-only) and the resource construction discussed by Amy et al.,
MeetintheMiddlev4.tex:586-590.
Each T-dagger is explicitly expanded to T S S S.
-/

public section

namespace QuantumAlg.FTQC

open CliffordT UnitaryCircuit Gate
open NormalizedVector

noncomputable section
lemma toffoli7T_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    (toffoli7TCircuit oracles).binaryMatrix environment = toffoliOp := by
  apply Subtype.ext
  ext i j
  fin_cases i
  · exact toffoli7TRow0 environment j
  · exact toffoli7TRow1 environment j
  · exact toffoli7TRow2 environment j
  · exact toffoli7TRow3 environment j
  · exact toffoli7TRow4 environment j
  · exact toffoli7TRow5 environment j
  · exact toffoli7TRow6 environment j
  · exact toffoli7TRow7 environment j

/-- The physical, phase-exact Toffoli target is independent of its implementation. -/
def toffoliPhysicalOp :
    UnitaryOperator (QuantumSignature.qubits 3).canonicalPlacement.layout.register :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm toffoliOp

/-- Exact realization by the actual strict-model seven-T circuit. -/
def toffoli7T (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization CliffordTGate.model oracles
      (QuantumSignature.qubits 3).canonicalPlacement.layout (fun _ => toffoliPhysicalOp) where
  circuit := toffoli7TCircuit oracles
  matrix_eq environment := matrix_of_binaryMatrix_eq _ _ environment
    (toffoli7T_matrix oracles environment)

/-- Relocate the complete construction to an injectively renamed physical interface. -/
def toffoli7TAt (oracles : OracleModel) (physical : Nat ↪ Nat) :
    UnitaryCircuit CliffordTGate.model oracles
      ((QuantumSignature.qubits 3).canonicalPlacement.layout.relabel physical) :=
  (toffoli7TCircuit oracles).relabel physical

lemma toffoli7TAt_matrix (oracles : OracleModel) (physical : Nat ↪ Nat)
    (environment : oracles.Interpretation) :
    (toffoli7TAt oracles physical).matrix environment = toffoliPhysicalOp := by
  rw [toffoli7TAt, relabel_matrix]
  exact (toffoli7T oracles).matrix_eq environment

lemma toffoli7TAt_eventCost (oracles : OracleModel) (physical : Nat ↪ Nat) :
    (toffoli7TAt oracles physical).eventCost = toffoli7TEvents oracles := by
  rw [toffoli7TAt, relabel_eventCost, toffoli7T_eventCost]

end

end QuantumAlg.FTQC
