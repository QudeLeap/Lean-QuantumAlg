/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Control.Preparation
import all QuantumAlg.Util.FinPow

/-!
# Exact source-register coordinates of the prepared runtime frame

The runtime places the freshly prepared Ctrl before its old context, while
the source encoding places Ctrl after the words, lengths, and other four
flags [LYL+26, sec_EEA/sub_regshare.tex:16-26]. The equivalence below first
uses the actual preparation wire assembly, then concatenates the old body
and the fresh Ctrl in that original physical order. The width transport
preserves the complete integer label.

Every encoded bit is checked: the last physical identity reads the fresh
Ctrl value, and every preceding physical identity reads its original body
bit. The inverse source-register decoding uses the actual proved total
encoding map. No equivalence is chosen from dimension cardinalities alone.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PreparedFrame

noncomputable section

variable {runtimeEnvironment :
  (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution ControlPreparation

/-- The original complete source encoding, viewed as its actual proved bijection. -/
def registerLabelEquiv (width : Nat) :
    Registers width ≃ (Qubits (encoding width).width).Index :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, encoding_surjective width⟩

lemma registerLabelEquiv_encode (width : Nat) (state : Registers width) :
    registerLabelEquiv width state = (encoding width).encode state := rfl

/-- Reuse the exact runtime preparation assembly of the fresh and existing physical wires. -/
def assembly (width : Nat) :
    ((controlLayout width).register.Index × (before width).register.Index) ≃
      (after width).register.Index :=
  preparedLocalBasisEquiv (before width) controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width)

private def appendControlEquiv (width : Nat) :
    ((Qubits 1).Index × (Qubits (bodyWidth width)).Index) ≃
      (Qubits (encoding width).width).Index :=
  (Equiv.prodComm _ _).trans
    ((prodEquiv (m := bodyWidth width) (n := 1)).trans
      (finCongr (congrArg (fun count : Nat => 2 ^ count) (complete_width width))))

/-- Reorder only the actual new/old coordinates into the source's body-then-Ctrl bit order. -/
def basisEquiv (width : Nat) :
    (after width).register.Index ≃ (Qubits (encoding width).width).Index :=
  (assembly width).symm.trans
    ((Equiv.prodCongr (controlQubitLayout width).binaryIndexEquiv
      (OwnedQubits.basisEquiv (bodyWidth width))).trans (appendControlEquiv width))

/-- Decode all finite source fields from that exact runtime binary label. -/
def frameEquiv (width : Nat) : (after width).register.Index ≃ Registers width :=
  (basisEquiv width).trans (registerLabelEquiv width).symm

lemma encode_frameEquiv (width : Nat) (basis : (after width).register.Index) :
    (encoding width).encode (frameEquiv width basis) = basisEquiv width basis :=
  (registerLabelEquiv width).apply_symm_apply (basisEquiv width basis)

private lemma basisEquiv_assembly (width : Nat)
    (fresh : (controlLayout width).register.Index) (old : (before width).register.Index) :
    basisEquiv width (assembly width (fresh, old)) =
      appendControlEquiv width ((controlQubitLayout width).binaryIndexEquiv fresh,
        OwnedQubits.basisEquiv (bodyWidth width) old) := by
  let encodePair :
      ((controlLayout width).register.Index × (before width).register.Index) →
        (Qubits (encoding width).width).Index := fun pair =>
    appendControlEquiv width ((controlQubitLayout width).binaryIndexEquiv pair.1,
      OwnedQubits.basisEquiv (bodyWidth width) pair.2)
  change encodePair ((assembly width).symm (assembly width (fresh, old))) =
    encodePair (fresh, old)
  exact congrArg encodePair ((assembly width).symm_apply_apply (fresh, old))

/-- The exact integer binary label is the original body followed by the new Ctrl bit. -/
lemma basisEquiv_assembly_val (width : Nat)
    (fresh : (controlLayout width).register.Index) (old : (before width).register.Index) :
    (basisEquiv width (assembly width (fresh, old))).val =
      (prodEquiv (m := bodyWidth width) (n := 1)
        (OwnedQubits.basisEquiv (bodyWidth width) old,
          (controlQubitLayout width).binaryIndexEquiv fresh)).val := by
  rw [basisEquiv_assembly]
  rfl

/-- Every native semantic lens reads the unchanged bit at its actual physical source position. -/
lemma frameEquiv_bit (width : Nat) (bit : EncodedBit (encoding width))
    (fresh : (controlLayout width).register.Index) (old : (before width).register.Index) :
    bit.get (frameEquiv width (assembly width (fresh, old))) =
      if bit.wire.val = bodyWidth width then finTwoEquiv (fresh 0)
      else (OwnedQubits.basisEquiv (bodyWidth width) old).val.testBit
        (bodyWidth width - 1 - bit.wire.val) := by
  rw [← bit.get_eq, encode_frameEquiv, basisEquiv_assembly_val]
  have complete := complete_width width
  have within := bit.wire.isLt
  by_cases last : bit.wire.val = bodyWidth width
  · have reversed : (WireAddress.bitIndex bit.wire).val = 0 := by
      change (encoding width).width - 1 - bit.wire.val = 0
      omega
    rw [if_pos last, reversed]
    have lowBit := prodEquiv_testBit_right
      (OwnedQubits.basisEquiv (bodyWidth width) old)
      ((controlQubitLayout width).binaryIndexEquiv fresh) (0 : Fin 1)
    have freshBit := (controlQubitLayout width).binaryIndexEquiv_bit fresh (0 : Fin 1)
    exact lowBit.trans freshBit
  · have oldPosition : bit.wire.val < bodyWidth width := by omega
    let reversedOld : Fin (bodyWidth width) :=
      ⟨bodyWidth width - 1 - bit.wire.val, by omega⟩
    have reversed : (WireAddress.bitIndex bit.wire).val = 1 + reversedOld.val := by
      change (encoding width).width - 1 - bit.wire.val =
        1 + (bodyWidth width - 1 - bit.wire.val)
      omega
    rw [if_neg last, reversed]
    exact prodEquiv_testBit_left (OwnedQubits.basisEquiv (bodyWidth width) old)
      ((controlQubitLayout width).binaryIndexEquiv fresh) reversedOld

/-- The decoded source Ctrl is exactly the finite bit on the newly prepared physical system. -/
lemma frameEquiv_control (width : Nat) (fresh : (controlLayout width).register.Index)
    (old : (before width).register.Index) :
    (frameEquiv width (assembly width (fresh, old))).control = finTwoEquiv (fresh 0) := by
  have actual := frameEquiv_bit width (controlBit width) fresh old
  rw [controlBit_get, controlBit_wire] at actual
  change _ = (if bodyWidth width = bodyWidth width then _ else _) at actual
  exact actual.trans (if_pos rfl)

/-- Actual preparation therefore supplies the source program's internal Ctrl-zero invariant. -/
lemma frameEquiv_prepared_control (width : Nat) (old : (before width).register.Index) :
    (frameEquiv width (assembly width ((preparation width).value, old))).control = false := by
  rw [frameEquiv_control, prepared_control_zero]
  rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- The actual preparation has zero row support on every decoded source frame with Ctrl one. -/
lemma execute_dirty_frame_row (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (freshRow freshColumn : (controlLayout width).register.Index)
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index)
    (dirty : (frameEquiv width (assembly width (freshRow, oldRow.1))).control = true) :
    ((circuit width).execute runtimeEnvironment Reference state).quantumMarginal.matrix
      (joined width freshRow oldRow) (joined width freshColumn oldColumn) = 0 := by
  apply execute_nonzero_control_row width state freshRow freshColumn oldRow oldColumn
  intro zero
  rw [frameEquiv_control, zero] at dirty
  contradiction

/-- The complete matrix on the source Ctrl-zero subspace is the unchanged prior joint matrix. -/
lemma execute_prepared_frame_entry (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index) :
    ((circuit width).execute runtimeEnvironment Reference state).quantumMarginal.matrix
      (joined width (preparation width).value oldRow)
      (joined width (preparation width).value oldColumn) =
        state.quantumMarginal.matrix oldRow oldColumn :=
  execute_zero_entry width state oldRow oldColumn

end

end QuantumAlg.MAU.Inversion.SharedEEA.PreparedFrame
