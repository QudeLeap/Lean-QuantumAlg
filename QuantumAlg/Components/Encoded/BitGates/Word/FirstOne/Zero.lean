/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Pattern
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate

/-!
# Actual full-subword zero tests for the first-one fork

The complete static source subword and retained parent enable are real
quantum controls. Negative source controls use actual X masks, and the
same arbitrary dirty work returns within the native conjunction word
[G17, paper.tex:278-293]. This component allocates no new system.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- Independent complete zero predicate on the actual original subword. -/
def zeroPredicate (source : Word encoding count) (state : Data) : Bool :=
  decide (∀ index, (source.bit index).get state = false)

/-- The parent enable selects a literal native masked conjunction using arbitrary restored work. -/
def zeroGates (layout : Word.OneDirtyLayout (encoding := encoding) count)
    (enable : EncodedBit encoding)
    (sources : ∀ index, enable.wire ≠ (layout.source.bit index).wire)
    (output : enable.wire ≠ layout.output.wire) (work : enable.wire ≠ layout.work.wire) :
    List (GateSpec encoding) :=
  layout.controlledPatternGates enable sources output work (fun _ => false)

/-- Exact full encoded-state zero-test action includes every source mask and cleanup. -/
lemma zeroGates_step (layout : Word.OneDirtyLayout (encoding := encoding) count)
    (enable : EncodedBit encoding)
    (sources : ∀ index, enable.wire ≠ (layout.source.bit index).wire)
    (output : enable.wire ≠ layout.output.wire) (work : enable.wire ≠ layout.work.wire)
    (state : Data) :
    GateSpec.stepList (zeroGates layout enable sources output work) state =
      predicateFlip layout.output
        (fun value => enable.get value && zeroPredicate layout.source value) state := by
  rw [zeroGates, Word.OneDirtyLayout.controlledPatternGates_step]
  simp only [predicateFlip, zeroPredicate]
  by_cases selected : enable.get state = true
  · simp only [selected, if_true, Bool.true_and, decide_eq_true_eq]
  · have inactive : enable.get state = false := Bool.eq_false_iff.mpr selected
    simp only [inactive, Bool.false_eq_true, if_false, Bool.false_and]

/-- The same complete native word has coherent semantics on arbitrary dirty work and references. -/
lemma zeroGates_realizes (layout : Word.OneDirtyLayout (encoding := encoding) count)
    (enable : EncodedBit encoding)
    (sources : ∀ index, enable.wire ≠ (layout.source.bit index).wire)
    (output : enable.wire ≠ layout.output.wire) (work : enable.wire ≠ layout.work.wire)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (zeroGates layout enable sources output work)) environment
      (predicateFlip layout.output
        (fun value => enable.get value && zeroPredicate layout.source value)) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (zeroGates_step layout enable sources output work) environment

/-- The actual subword test has linear size, including the real added control and all masks. -/
lemma zeroGates_length_le (layout : Word.OneDirtyLayout (encoding := encoding) count)
    (enable : EncodedBit encoding)
    (sources : ∀ index, enable.wire ≠ (layout.source.bit index).wire)
    (output : enable.wire ≠ layout.output.wire) (work : enable.wire ≠ layout.work.wire) :
    (zeroGates layout enable sources output work).length ≤ 10 * (count + 1) + 1 :=
  layout.controlledPatternGates_length_le enable sources output work (fun _ => false)

end

end QuantumAlg.EncodedBit.FirstOne
