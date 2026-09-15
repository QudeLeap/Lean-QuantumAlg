/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle.Resources
import all QuantumAlg.Core.Execution.Preparation.Laws

/-!
# Match oracle word order to actual input and preparation identities

The logical oracle orders exponent, power, auxiliary, target. The caller
supplies exponent and target first, and preparation appends power and
auxiliary. The explicit basis equivalence regroups those same fields, and
the physical map sends every gate wire to its corresponding actual word.
No new system or event is introduced by this placement.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.OwnedQubits

private def fieldsEquiv (exponentWidth width : Nat) :
    ((Fin (2 ^ width) × Fin (2 ^ width)) ×
      (Fin (2 ^ exponentWidth) × Fin (2 ^ width))) ≃ OracleRegisters exponentWidth width where
  toFun state := ((state.2.1, state.1), state.2.2)
  invFun state := (state.1.2, (state.1.1, state.2))
  left_inv := by rintro ⟨⟨power, auxiliary⟩, ⟨exponent, target⟩⟩; rfl
  right_inv := by rintro ⟨⟨exponent, power, auxiliary⟩, target⟩; rfl

private def oracleLabelEquiv (exponentWidth width : Nat) :
    OracleRegisters exponentWidth width ≃
      (Qubits (oracleEncoding exponentWidth width).width).Index :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := width) (n := width))).trans
      (prodEquiv (m := exponentWidth) (n := width + width)))
    (Equiv.refl _)).trans (prodEquiv (m := exponentWidth + (width + width)) (n := width))

private theorem oracleLabelEquiv_encode (exponentWidth width : Nat)
    (state : OracleRegisters exponentWidth width) :
    oracleLabelEquiv exponentWidth width state =
      (oracleEncoding exponentWidth width).encode state :=
  rfl

/-- Actual prepared/source basis fields are regrouped into the fixed oracle word order. -/
def preparedBasisEquiv (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).register.Index ≃
      (Qubits (oracleEncoding exponentWidth width).width).Index :=
  (Execution.preparedLocalBasisEquiv (context (exponentWidth + width))
    workKey (workLayout exponentWidth width)
    (gidneyExponentWork_fresh exponentWidth width)
    (gidneyExponentWork_disjoint exponentWidth width)).symm |>.trans
      (Equiv.prodCongr (workQubitLayout exponentWidth width).binaryIndexEquiv
        (basisEquiv (exponentWidth + width))) |>.trans
      (Equiv.prodCongr (prodEquiv (m := width) (n := width)).symm
        (prodEquiv (m := exponentWidth) (n := width)).symm) |>.trans
      (fieldsEquiv exponentWidth width) |>.trans (oracleLabelEquiv exponentWidth width)

/-- The basis map reads precisely the existing physical work and input words. -/
theorem gidneyExponentPreparedBasis_fields (exponentWidth width : Nat)
    (work : (workLayout exponentWidth width).Basis)
    (supplied : (context (exponentWidth + width)).register.Index) :
    preparedBasisEquiv exponentWidth width
        (Execution.preparedLocalBasisEquiv (context (exponentWidth + width))
          workKey (workLayout exponentWidth width)
          (gidneyExponentWork_fresh exponentWidth width)
          (gidneyExponentWork_disjoint exponentWidth width) (work, supplied)) =
      let workWords := (prodEquiv (m := width) (n := width)).symm
        ((workQubitLayout exponentWidth width).binaryIndexEquiv work)
      let inputWords := (prodEquiv (m := exponentWidth) (n := width)).symm
        (basisEquiv (exponentWidth + width) supplied)
      (oracleEncoding exponentWidth width).encode ((inputWords.1, workWords), inputWords.2) := by
  let readFields : (workLayout exponentWidth width).Basis ×
      (context (exponentWidth + width)).register.Index →
        (Qubits (oracleEncoding exponentWidth width).width).Index := fun fields =>
    let workWords := (prodEquiv (m := width) (n := width)).symm
      ((workQubitLayout exponentWidth width).binaryIndexEquiv fields.1)
    let inputWords := (prodEquiv (m := exponentWidth) (n := width)).symm
      (basisEquiv (exponentWidth + width) fields.2)
    oracleLabelEquiv exponentWidth width ((inputWords.1, workWords), inputWords.2)
  have restored := Equiv.symm_apply_apply
    (Execution.preparedLocalBasisEquiv (context (exponentWidth + width))
      workKey (workLayout exponentWidth width)
      (gidneyExponentWork_fresh exponentWidth width)
      (gidneyExponentWork_disjoint exponentWidth width)) (work, supplied)
  exact (congrArg readFields restored).trans (oracleLabelEquiv_encode exponentWidth width _)

/-- Send canonical exponent/work/target positions to actual input/work physical identities. -/
def nativePlacementWire (exponentWidth width wire : Nat) : Nat :=
  if wire < exponentWidth then wire
  else if wire < exponentWidth + 2 * width then wire + width
  else if wire < exponentWidth + 3 * width then wire - 2 * width
  else wire

private def inverseNativePlacementWire (exponentWidth width wire : Nat) : Nat :=
  if wire < exponentWidth then wire
  else if wire < exponentWidth + width then wire + 2 * width
  else if wire < exponentWidth + 3 * width then wire - width
  else wire

private theorem nativePlacementWire_left_inverse (exponentWidth width wire : Nat) :
    inverseNativePlacementWire exponentWidth width (nativePlacementWire exponentWidth width wire) =
      wire := by
  unfold inverseNativePlacementWire nativePlacementWire
  split_ifs <;> omega

theorem gidneyExponentNativePlacement_injective (exponentWidth width : Nat) :
    Function.Injective (nativePlacementWire exponentWidth width) := by
  intro left right same
  have inverse := congrArg (inverseNativePlacementWire exponentWidth width) same
  simpa only [nativePlacementWire_left_inverse] using inverse

theorem gidneyExponentNativePlacement_range (exponentWidth width wire : Nat)
    (inside : wire < exponentWidth + 3 * width) :
    nativePlacementWire exponentWidth width wire < exponentWidth + 3 * width := by
  unfold nativePlacementWire
  split_ifs <;> omega

theorem gidneyExponentNativePlacement_exponent (exponentWidth width : Nat)
    (wire : Fin exponentWidth) :
    nativePlacementWire exponentWidth width wire.val = wire.val := by
  unfold nativePlacementWire
  exact if_pos wire.isLt

theorem gidneyExponentNativePlacement_power (exponentWidth width : Nat) (wire : Fin width) :
    nativePlacementWire exponentWidth width (exponentWidth + wire.val) =
      exponentWidth + width + wire.val := by
  unfold nativePlacementWire
  split_ifs <;> omega

theorem gidneyExponentNativePlacement_auxiliary (exponentWidth width : Nat) (wire : Fin width) :
    nativePlacementWire exponentWidth width (exponentWidth + width + wire.val) =
      exponentWidth + 2 * width + wire.val := by
  unfold nativePlacementWire
  split_ifs <;> omega

theorem gidneyExponentNativePlacement_target (exponentWidth width : Nat) (wire : Fin width) :
    nativePlacementWire exponentWidth width (exponentWidth + 2 * width + wire.val) =
      exponentWidth + wire.val := by
  unfold nativePlacementWire
  split_ifs <;> omega

end

end QuantumAlg.MAU.Exponentiation.Gidney
