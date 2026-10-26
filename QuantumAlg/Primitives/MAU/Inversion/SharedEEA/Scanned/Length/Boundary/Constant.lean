/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-! # Literal native loading of the terminal length boundary constant -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The same complete prefix with the constant-XOR API's least-significant-first order. -/
def littleTarget (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨fun index => prefixBit width index.rev⟩

/-- Only a fixed public physical-width constant is supplied to this actual loader. -/
def constant (width : Nat) (field : Field) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.ofNat (ScanMetadata.addressWidth width)
    (match field with
    | .coefficient => width + 3
    | .divisor => width + 3 - 1)

/-- Actual X gates execute the public constant XOR on the existing prefix. -/
def constantProgram (width : Nat) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (littleTarget width).xorConstantProgram (QubitLayout.canonical _) .empty
    (constant width field).toFin

/-- All-label action of the same physical native X instructions. -/
def constantStep (width : Nat) (field : Field) : Data width → Data width :=
  (littleTarget width).xorConstantStep (constant width field).toFin

/-- Complete coherent native semantics retain every original unselected system. -/
lemma constantProgram_realizes (width : Nat) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (constantProgram width field) environment
      (constantStep width field) :=
  (littleTarget width).xorConstant_realizes (QubitLayout.canonical _) .empty
    (constant width field).toFin environment

private lemma constant_read (width : Nat) (field : Field)
    (index : Fin (ScanMetadata.addressWidth width)) :
    (constant width field).toFin.val.testBit index.rev.val =
      (constant width field).getMsbD index.val := by
  simp only [BitVec.val_toFin, Fin.val_rev, BitVec.getMsbD_eq_getLsbD, index.isLt,
    decide_true, Bool.true_and, BitVec.getLsbD]
  congr 1
  omega

/-- The whole original prefix receives the actual constant XOR, even when initially dirty. -/
lemma constantStep_prefix (width : Nat) (field : Field) (state : Data width) :
    (constantStep width field state).2.2.1 = state.2.2.1 ^^^ constant width field := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (littleTarget width).xorConstantStep_get_target (constant width field).toFin
    (⟨index, within⟩ : Fin (ScanMetadata.addressWidth width)).rev
    (fun other different => prefix_prefix_ne width other.rev _
      (fun same => different (Fin.rev_inj.mp same))) state
  simp only [littleTarget, Fin.rev_rev, prefixBit_get, constant_read] at actual
  exact actual.trans BitVec.getMsbD_xor.symm

/-- Every actual bit outside the complete prefix retains its arbitrary original value. -/
lemma constantStep_observed (width : Nat) (field : Field) (state : Data width)
    (observed : EncodedBit (encoding width))
    (outside : ∀ index, (prefixBit width index).wire ≠ observed.wire) :
    observed.get (constantStep width field state) = observed.get state :=
  (littleTarget width).xorConstantStep_get_observed_of_target_ne (constant width field).toFin
    observed (fun index => outside index.rev) state

/-- All original work words, complete metadata and original flags remain unchanged. -/
lemma constantStep_original (width : Nat) (field : Field) (state : Data width)
    (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get (constantStep width field state) =
      (sourceBit width observed).get state :=
  constantStep_observed width field state _
    (fun index => (source_prefix_ne width observed index).symm)

/-- The actual padded conjunction retains its incoming value before boundary subtraction. -/
lemma constantStep_conjunction (width : Nat) (field : Field) (state : Data width) :
    (constantStep width field state).2.2.2 = state.2.2.2 :=
  constantStep_observed width field state _ (fun index => prefix_conjunction_ne width index)

/-- The complete address also remains unchanged during the native public load. -/
lemma constantStep_address (width : Nat) (field : Field) (state : Data width) :
    (constantStep width field state).2.1 = state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simpa only [addressBit_get] using
    constantStep_observed width field state (addressBit width ⟨index, within⟩)
      (fun other => (address_prefix_ne width ⟨index, within⟩ other).symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
