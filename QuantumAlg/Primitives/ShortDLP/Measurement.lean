/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Core.Measure.Distribution

/-!
# Short-DLP source register and terminal readout

The mathematical source layout, zero input and exponent readout do not depend
on the circuit implementation or on access to a group-operation query.
-/

namespace QuantumAlg.ShortDLP

noncomputable section

/-- Canonical physical layout for the complete circuit. -/
def layout (params : RegisterParameters) : QubitLayout (totalQubits params) where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp]
theorem layout_systemIdx (params : RegisterParameters) :
    (layout params).systemIdx = List.range (totalQubits params) := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Canonical all-zero initial state. -/
def inputState (params : RegisterParameters) : QubitLayout.State (layout params) where
  state := PureState.ofNormalized
    (NormalizedVector.ket (R := Qubits (totalQubits params)) 0)
    (layout params).systemIdx
  system_idx_eq := rfl

/-- Terminal measurement of both exponent registers. -/
def measurement (params : RegisterParameters) :
    TerminalZMeasure (layout params) (firstBits params + params.ell) :=
  zMeasureAt (layout params)
    (fun index => ⟨index.val, by unfold totalQubits; omega⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))



/-- Raw measured pair of exponent-register values. -/
abbrev Outcome (params : RegisterParameters) : Type :=
  TerminalZMeasure.Outcome (firstBits params + params.ell)

/-- Decode a terminal outcome into the source pair `(j,k)`. -/
def decodeOutcome (params : RegisterParameters) (outcome : Outcome params) :
    Fin (2 ^ firstBits params) × Fin (2 ^ params.ell) :=
  prodEquiv.symm (TerminalZMeasure.fullRegisterIndex outcome)

end

end QuantumAlg.ShortDLP
