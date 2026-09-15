/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Reflection.Support
import all QuantumAlg.Components.Encoded.BitGates.Small.ControlledZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ControlledZeroReflection

/-!
# Actual support of controlled elementary source reflection

Containment follows from the literal gates on certified encoded bit addresses.
Both source complements omit the external control, while the final control Z
is retained in the same complete physical support.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

theorem controlledTwoWireZeroReflection_physical_idx_subset_range
    (control first second : EncodedBit encoding)
    (controlFirst : control.wire ≠ first.wire)
    (controlSecond : control.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) :
    (control.controlledTwoWireZeroReflection first second controlFirst controlSecond
      firstSecond).physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.conjugateProgram_physical_idx_subset_range _ _
      (control.doubleControlledZ_physical_idx_subset_range first second
        controlFirst controlSecond firstSecond))
    control.pauliZ_physical_idx_subset_range

namespace Word.OneDirtyLayout

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)
variable (control : EncodedBit encoding)
variable (sourceNe : ∀ index, control.wire ≠ (layout.source.bit index).wire)
variable (outputNe : control.wire ≠ layout.output.wire)
variable (workNe : control.wire ≠ layout.work.wire)

theorem controlledNegativeZeroPhase_physical_idx_subset_range :
    (layout.controlledNegativeZeroPhase control sourceNe outputNe workNe).physical_idx ⊆
      List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range _)
      (layout.withControl control sourceNe outputNe workNe).phaseProgram_physical_idx_subset_range)
    (GateSpec.programList_physical_idx_subset_range _)

theorem controlledZeroReflectionProgram_physical_idx_subset_range :
    (layout.controlledZeroReflectionProgram control sourceNe outputNe workNe).physical_idx ⊆
      List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (layout.controlledNegativeZeroPhase_physical_idx_subset_range control sourceNe outputNe workNe)
    control.pauliZ_physical_idx_subset_range

end Word.OneDirtyLayout

end

end QuantumAlg.EncodedBit
