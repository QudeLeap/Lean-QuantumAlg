/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.Toffoli7T.Base
public import QuantumAlg.Primitives.FTQC.CliffordLayers.Accounting
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Primitives.FTQC.Toffoli7T.Base
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
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

/-- Parities after the four CNOTs are (a xor b xor c, a xor b, a xor c). -/
def parityBasis (oracles : OracleModel) : List (CliffordCircuit oracles 3) :=
  [cx oracles 0 1 (by decide), cx oracles 0 2 (by decide),
    cx oracles 1 0 (by decide), cx oracles 2 0 (by decide)]

/-- Three tensor stages realize all seven nonzero phase-polynomial terms. -/
def parityTDepth3 (oracles : OracleModel) : CliffordCircuit oracles 3 := blocks
  ([layer3 oracles [.t] [.t] [.t]] ++ parityBasis oracles ++
    [layer3 oracles [.t] tDaggerWord tDaggerWord,
      cx oracles 1 2 (by decide), layer3 oracles [] [] tDaggerWord, cx oracles 1 2 (by decide)] ++
    (parityBasis oracles).reverse)

/-- Three-stage implementation on the three data qubits. -/
def toffoliTDepth3Core (oracles : OracleModel) : CliffordCircuit oracles 3 := blocks
  [layer3 oracles [] [] [.h], parityTDepth3 oracles, layer3 oracles [] [] [.h]]

end

end QuantumAlg.FTQC
