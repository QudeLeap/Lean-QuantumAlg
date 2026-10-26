/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Zero

/-!
# Actual high-bit validity latch for narrow terminal length clipping

The retained original Ctrl and negative high prefix bit toggle the high
existing address position. Its initial value is arbitrary in semantics;
the narrow consumer must prove it zero before identifying the active flag.
The original Iter is named as work, but this two-control native case does
not require any initialization or additional quantum system.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def highIndex (width : Nat) : Fin (ScanMetadata.addressWidth width) :=
  ⟨0, by unfold ScanMetadata.addressWidth; omega⟩

/-- The original high prefix bit retains the full signed validity information. -/
def highBit (width : Nat) : EncodedBit (encoding width) := prefixBit width (highIndex width)

private lemma control_work (width : Nat) :
    (SharedEEA.controlBit width).wire ≠ (SharedEEA.iterationBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [SharedEEA.controlBit_wire, SharedEEA.iterationBit_wire] at values
  omega

/-- One original prefix source and the actual high address output are physically distinct. -/
def activeLayout (width : Nat) : Word.OneDirtyLayout (encoding := encoding width) 1 where
  source := ⟨fun _index => highBit width⟩
  output := LengthCopy.active width true
  work := sourceBit width (SharedEEA.iterationBit width)
  source_injective := fun _left _right _same => Subsingleton.elim _ _
  source_output_ne := fun _index => (address_prefix_ne width _ _).symm
  source_work_ne := fun _index => (source_prefix_ne width _ _).symm
  work_output_ne := source_address_ne width _ _

/-- The actual native negative-control word reads only original Ctrl and high prefix. -/
def activeGates (width : Nat) : List (GateSpec (encoding width)) :=
  FirstOne.zeroGates (activeLayout width) (sourceBit width (SharedEEA.controlBit width))
    (fun _index => source_prefix_ne width _ _)
    (source_address_ne width _ _)
    (source_source_ne width _ _ (control_work width))

private lemma zeroPredicate_eq (width : Nat) (state : Data width) :
    FirstOne.zeroPredicate (activeLayout width).source state = !(highBit width).get state := by
  change decide (∀ _index : Fin 1, (highBit width).get state = false) =
    !(highBit width).get state
  cases (highBit width).get state <;> simp

/-- Complete actual physical action of the validity toggle, before its clean-address premise. -/
lemma activeGates_step (width : Nat) (state : Data width) :
    GateSpec.stepList (activeGates width) state =
      predicateFlip (LengthCopy.active width true)
        (fun value => value.1.control && !(highBit width).get value) state := by
  have actual := FirstOne.zeroGates_step (activeLayout width)
    (sourceBit width (SharedEEA.controlBit width))
    (fun _index => source_prefix_ne width _ _)
    (source_address_ne width _ _)
    (source_source_ne width _ _ (control_work width)) state
  simp only [zeroPredicate_eq] at actual
  exact actual

/-- This same real gate word is coherent on arbitrary original inputs and references. -/
lemma activeGates_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (activeGates width)) environment
      (predicateFlip (LengthCopy.active width true)
        (fun value => value.1.control && !(highBit width).get value)) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (activeGates_step width) environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
