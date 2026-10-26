/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Actual address constant preparation preserving the separate conjunction

Every set constant bit executes an X on the original address. All
original source systems and every prefix and conjunction position
remain present and unchanged.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def littleTarget (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨fun index => addressBit width index.rev⟩

/-- A public constant is loaded through its literal actual native X gates. -/
def constantProgram (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (littleTarget width).xorConstantProgram (QubitLayout.canonical _) .empty constant.toFin

/-- The complete original-frame action of those actual native X gates. -/
def constantStep (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width)) :
    Data width → Data width :=
  (littleTarget width).xorConstantStep constant.toFin

/-- Actual coherent execution has this complete action on arbitrary address and workspace values. -/
lemma constantProgram_realizes (width : Nat)
    (constant : BitVec (ScanMetadata.addressWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (constantProgram width constant) environment
      (constantStep width constant) :=
  (littleTarget width).xorConstant_realizes (QubitLayout.canonical _) .empty constant.toFin
    environment

private lemma constant_read (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width))
    (index : Fin (ScanMetadata.addressWidth width)) :
    constant.toFin.val.testBit index.rev.val = constant.getMsbD index.val := by
  simp only [BitVec.val_toFin, Fin.val_rev, BitVec.getMsbD_eq_getLsbD, index.isLt,
    decide_true, Bool.true_and, BitVec.getLsbD]
  congr 1
  omega

/-- The full address, in its actual declared order, receives the public constant xor. -/
lemma constantStep_address (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width))
    (state : Data width) :
    (constantStep width constant state).2.1 = state.2.1 ^^^ constant := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (littleTarget width).xorConstantStep_get_target constant.toFin
    (⟨index, within⟩ : Fin (ScanMetadata.addressWidth width)).rev
    (fun other different => address_address_ne width other.rev _
      (fun same => different (Fin.rev_inj.mp same))) state
  simp only [littleTarget, Fin.rev_rev, addressBit_get, constant_read] at actual
  exact actual.trans BitVec.getMsbD_xor.symm

/-- Every actual physical bit outside the address is unchanged. -/
lemma constantStep_observed (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width))
    (state : Data width) (observed : EncodedBit (encoding width))
    (outside : ∀ index, (addressBit width index).wire ≠ observed.wire) :
    observed.get (constantStep width constant state) = observed.get state :=
  (littleTarget width).xorConstantStep_get_observed_of_target_ne constant.toFin observed
    (fun index => outside index.rev) state

/-- The complete original source fields survive the same paid constant preparation. -/
lemma constantStep_source (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width))
    (state : Data width) : (constantStep width constant state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro observed
  exact constantStep_observed width constant state (sourceBit width observed)
    (fun index => (source_address_ne width observed index).symm)

/-- The prefix and conjunction keep arbitrary original values during this same actual load. -/
lemma constantStep_workspace (width : Nat) (constant : BitVec (ScanMetadata.addressWidth width))
    (state : Data width) : (constantStep width constant state).2.2 = state.2.2 := by
  apply Prod.ext
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    exact (prefixBit_get width ⟨index, within⟩ _).symm.trans
      ((constantStep_observed width constant state (prefixBit width ⟨index, within⟩)
        (fun other => address_prefix_ne width other ⟨index, within⟩)).trans
        (prefixBit_get width ⟨index, within⟩ state))
  · exact constantStep_observed width constant state (conjunctionBit width)
      (fun index => address_conjunction_ne width index)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
