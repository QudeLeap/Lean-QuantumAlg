/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Native.Matrix
public import QuantumAlg.Core.Measure
public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Algorithms.OrderFinding.Native.Matrix
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Coherent source state of the actual native order-finding word

The Born model starts from the all-zero phase and target registers and
applies exactly the accepted native word's binary matrix. Its terminal
selection reads the original phase prefix in logical order
[dW19, qcnotes.tex:2203-2225].
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- Canonical phase and target placement used by the native word. -/
public def sourceLayout (t width : Nat) : QubitLayout (t + width) :=
  QubitLayout.canonical (t + width)

/-- The original all-zero source input in big-endian binary labels. -/
public def zeroInput (t width : Nat) : NormalizedVector (Qubits (t + width)) :=
  NormalizedVector.ket 0

/-- Exact normalized vector after the declared query and native phase readout word. -/
public def evolvedVector {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    NormalizedVector (Qubits (t + width)) :=
  ((circuit t width).binaryMatrix (interpretation access)).apply (zeroInput t width)

/-- The native vector with the source's canonical physical-placement metadata. -/
def evolvedState {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    QubitLayout.State (sourceLayout t width) :=
  { state := PureState.ofNormalized
      (evolvedVector access)
      (sourceLayout t width).systemIdx
    system_idx_eq := rfl }

/-- The phase-prefix measurement retains the entire target register. -/
public def measurement (t width : Nat) : TerminalZMeasure (sourceLayout t width) t :=
  zMeasureAt (sourceLayout t width)
    (fun index => ⟨index.val, Nat.lt_add_right width index.isLt⟩)
    (fun _ _ equal => Fin.ext (Fin.mk.inj equal))

end

end QuantumAlg.OrderFinding.Native
