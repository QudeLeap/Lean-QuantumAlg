/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Readout
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Paid constant preparation of the complete geometry word

Public constants are loaded by actual X gates on the same conjunction
and address positions later used by native geometry arithmetic. The
original metadata and complete prefix survive on every finite label.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def littleTarget (width : Nat) : Word (encoding width) (fullWidth width) where
  bit index := (target width).bit index.rev

/-- Execute the constant's set bits as actual native X instructions on the existing pool. -/
def constantProgram (width : Nat) (constant : BitVec (fullWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (littleTarget width).xorConstantProgram (QubitLayout.canonical _) .empty constant.toFin

/-- The complete state action of those same emitted X instructions. -/
def constantStep (width : Nat) (constant : BitVec (fullWidth width)) : Data width → Data width :=
  (littleTarget width).xorConstantStep constant.toFin

/-- Actual constant preparation preserves every coherent amplitude and reference correlation. -/
lemma constantProgram_realizes (width : Nat) (constant : BitVec (fullWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (constantProgram width constant) environment
      (constantStep width constant) :=
  (littleTarget width).xorConstant_realizes (QubitLayout.canonical _) .empty constant.toFin
    environment

private lemma constant_read (width : Nat) (constant : BitVec (fullWidth width))
    (index : Fin (fullWidth width)) :
    constant.toFin.val.testBit index.rev.val = constant.getMsbD index.val := by
  simp only [BitVec.val_toFin, Fin.val_rev, BitVec.getMsbD_eq_getLsbD, index.isLt,
    decide_true, Bool.true_and, BitVec.getLsbD]
  congr 1
  omega

/-- Every full target bit has its original value xored with the actual public constant. -/
lemma constantStep_targetValue (width : Nat) (constant : BitVec (fullWidth width))
    (state : Data width) :
    targetValue width (constantStep width constant state) =
      targetValue width state ^^^ constant := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (littleTarget width).xorConstantStep_get_target constant.toFin
    (⟨index, within⟩ : Fin (fullWidth width)).rev (fun other different =>
      target_distinct width other.rev _ (fun same => different (Fin.rev_inj.mp same))) state
  simp only [littleTarget, Fin.rev_rev, target_get, constant_read] at actual
  exact actual.trans BitVec.getMsbD_xor.symm

private lemma constantStep_observed (width : Nat) (constant : BitVec (fullWidth width))
    (state : Data width) (observed : EncodedBit (encoding width))
    (outside : ∀ index, ((target width).bit index).wire ≠ observed.wire) :
    observed.get (constantStep width constant state) = observed.get state :=
  (littleTarget width).xorConstantStep_get_observed_of_target_ne constant.toFin observed
    (fun index => outside index.rev) state

/-- Original payload, metadata, phase and arbitrary control/Iter fields survive constant loading. -/
lemma constantStep_source (width : Nat) (constant : BitVec (fullWidth width))
    (state : Data width) : (constantStep width constant state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro observed
  apply constantStep_observed width constant state (sourceBit width observed)
  intro index
  unfold target
  dsimp only
  split
  · exact (source_conjunction_ne width observed).symm
  · exact (source_address_ne width observed _).symm

/-- Every real prefix and both high padding positions retain their original values. -/
lemma constantStep_prefix (width : Nat) (constant : BitVec (fullWidth width))
    (state : Data width) : (constantStep width constant state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have outside (other : Fin (fullWidth width)) :
      ((target width).bit other).wire ≠ (prefixBit width ⟨index, within⟩).wire := by
    unfold target
    dsimp only
    split
    · exact (prefix_conjunction_ne width _).symm
    · exact address_prefix_ne width _ _
  simpa only [prefixBit_get] using
    constantStep_observed width constant state (prefixBit width ⟨index, within⟩) outside

/-- Actual padding-zero promises identify the full source with its original metadata value. -/
lemma sourceValue_toNat_of_prefix_zero (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (sourceValue width positive field state).toNat = (fieldValue field state).toNat := by
  simp [sourceValue, prefixBit_get, clean]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
