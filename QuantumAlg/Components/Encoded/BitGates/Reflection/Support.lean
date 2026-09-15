/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard
import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Conjugation
import all QuantumAlg.Components.Encoded.BitGates.DiagonalConjugation
import all QuantumAlg.Components.Encoded.BitGates.PauliZ
import all QuantumAlg.Components.Encoded.BitGates.Small.Phase
import all QuantumAlg.Components.Encoded.BitGates.Small.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.ZeroReflection
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Phase
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Actual physical support of the elementary reflection constructions

Every elementary gate uses a certified bit address of its supplied encoding.
The literal sequential compositions therefore remain inside that encoding's
actual physical register. This provides placement evidence independently of
their matrix or their event count.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

theorem hadamard_physical_idx_subset_range (target : EncodedBit encoding) :
    target.hadamard.physical_idx ⊆ List.range encoding.width := by
  rw [hadamard_physical_idx]
  intro wire present
  have same := List.mem_singleton.mp present
  subst wire
  exact List.mem_range.mpr target.wire.isLt

theorem pauliZ_physical_idx_subset_range (target : EncodedBit encoding) :
    target.pauliZ.physical_idx ⊆ List.range encoding.width := by
  rw [pauliZ_physical_idx]
  intro wire present
  have same := List.mem_singleton.mp present
  subst wire
  exact List.mem_range.mpr target.wire.isLt

theorem globalMinus_physical_idx_subset_range (target : EncodedBit encoding) :
    target.globalMinus.physical_idx ⊆ List.range encoding.width := by
  apply UnitaryCircuit.seq_physical_idx_subset
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact UnitaryCircuit.seq_physical_idx_subset _ _
        (GateSpec.program_physical_idx_subset_range (.x target))
        target.pauliZ_physical_idx_subset_range
    · exact GateSpec.program_physical_idx_subset_range (.x target)
  · exact target.pauliZ_physical_idx_subset_range

theorem conjugateHadamard_physical_idx_subset_range (target : EncodedBit encoding)
    (program : UnitaryCircuit (Qubits encoding.width))
    (contained : program.physical_idx ⊆ List.range encoding.width) :
    (target.conjugateHadamard program).physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _
      target.hadamard_physical_idx_subset_range contained)
    target.hadamard_physical_idx_subset_range

theorem GateSpec.conjugateProgram_physical_idx_subset_range
    (gates : List (GateSpec encoding)) (program : UnitaryCircuit (Qubits encoding.width))
    (contained : program.physical_idx ⊆ List.range encoding.width) :
    (GateSpec.conjugateProgram gates program).physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range gates) contained)
    (GateSpec.programList_physical_idx_subset_range gates.reverse)

theorem controlledZ_physical_idx_subset_range (control target : EncodedBit encoding)
    (different : control.wire ≠ target.wire) :
    (control.controlledZ target different).physical_idx ⊆ List.range encoding.width :=
  target.conjugateHadamard_physical_idx_subset_range _
    (GateSpec.program_physical_idx_subset_range (.cnot control target different))

theorem doubleControlledZ_physical_idx_subset_range (first second target : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstTarget : first.wire ≠ target.wire) (secondTarget : second.wire ≠ target.wire) :
    (first.doubleControlledZ second target firstSecond firstTarget secondTarget).physical_idx ⊆
      List.range encoding.width :=
  target.conjugateHadamard_physical_idx_subset_range _
    (GateSpec.program_physical_idx_subset_range
      (.toffoli first second target firstSecond firstTarget secondTarget))

theorem twoWireZeroReflection_physical_idx_subset_range (first second : EncodedBit encoding)
    (different : first.wire ≠ second.wire) :
    (first.twoWireZeroReflection second different).physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ first.pauliZ_physical_idx_subset_range
      second.pauliZ_physical_idx_subset_range)
    (first.controlledZ_physical_idx_subset_range second different)

theorem threeWireZeroReflection_physical_idx_subset_range
    (first second third : EncodedBit encoding)
    (firstSecond : first.wire ≠ second.wire)
    (firstThird : first.wire ≠ third.wire) (secondThird : second.wire ≠ third.wire) :
    (first.threeWireZeroReflection second third firstSecond firstThird secondThird).physical_idx ⊆
      List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.conjugateProgram_physical_idx_subset_range _ _
      (first.doubleControlledZ_physical_idx_subset_range second third
        firstSecond firstThird secondThird))
    third.globalMinus_physical_idx_subset_range

namespace Word.OneDirtyLayout

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)

theorem phaseProgram_physical_idx_subset_range :
    layout.phaseProgram.physical_idx ⊆ List.range encoding.width :=
  layout.output.conjugateHadamard_physical_idx_subset_range _
    (GateSpec.programList_physical_idx_subset_range layout.gates)

theorem negativeZeroPhase_physical_idx_subset_range :
    layout.negativeZeroPhase.physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range _)
      layout.phaseProgram_physical_idx_subset_range)
    (GateSpec.programList_physical_idx_subset_range _)

theorem zeroReflectionProgram_physical_idx_subset_range :
    layout.zeroReflectionProgram.physical_idx ⊆ List.range encoding.width :=
  UnitaryCircuit.seq_physical_idx_subset _ _ layout.negativeZeroPhase_physical_idx_subset_range
    layout.output.globalMinus_physical_idx_subset_range

end Word.OneDirtyLayout

end

end QuantumAlg.EncodedBit
