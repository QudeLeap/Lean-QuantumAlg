/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Register.Binary
public import QuantumAlg.Components.Gates.Swap.Register
public import QuantumAlg.Components.Control
import all QuantumAlg.Components.Gates.Swap.Controlled.Register.Binary
import all QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.Swap.Register
import all QuantumAlg.Components.Control
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Exact full operator of the actual controlled register exchange

The native CNOT/Toffoli words implement the independently specified controlled
exchange of both original binary registers, on every state and with exact phase.
-/

namespace QuantumAlg.Gate.ControlledRegisterSwap

noncomputable section

private lemma decoded_eq_iff (width : Nat) (firstControl secondControl : Fin 2)
    (firstLeft firstRight secondLeft secondRight : Fin (2 ^ width)) :
    decoded width firstControl firstLeft firstRight =
        decoded width secondControl secondLeft secondRight ↔
      firstControl = secondControl ∧ firstLeft = secondLeft ∧ firstRight = secondRight := by
  constructor
  · intro same
    have labels := (QuantumSignature.qubitsIndexEquiv (1 + (width + width))).symm.injective same
    have pairs := (prodEquiv (m := 1) (n := width + width)).injective labels
    have words := (prodEquiv (m := width) (n := width)).injective (congrArg Prod.snd pairs)
    exact ⟨congrArg Prod.fst pairs, congrArg Prod.fst words, congrArg Prod.snd words⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma target_entry (width : Nat) (firstControl secondControl : Fin 2)
    (firstLeft firstRight secondLeft secondRight : Fin (2 ^ width)) :
    UnitaryOperator.controlledQubits (swapRegistersOp width)
        (prodEquiv (firstControl, prodEquiv (firstLeft, firstRight)))
        (prodEquiv (secondControl, prodEquiv (secondLeft, secondRight))) =
      if firstControl = secondControl then
        if firstControl = 1 then
          if firstRight = secondLeft ∧ firstLeft = secondRight then 1 else 0
        else if firstLeft = secondLeft ∧ firstRight = secondRight then 1 else 0
      else 0 := by
  change UnitaryOperator.controlled (Qubits 1) (1 : Fin 2) (swapRegistersOp width)
    ((prodEquiv (m := 1) (n := width + width)).symm
      (prodEquiv (firstControl, prodEquiv (firstLeft, firstRight))))
    ((prodEquiv (m := 1) (n := width + width)).symm
      (prodEquiv (secondControl, prodEquiv (secondLeft, secondRight)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, UnitaryOperator.controlled_apply]
  simp only [swapRegistersOp, UnitaryOperator.ofPerm_entry, swapRegistersPerm,
    Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_apply, Prod.swap,
    Equiv.apply_eq_iff_eq, Prod.mk.injEq]

/-- Actual native circuit matrix equals the original controlled register SWAP on every input. -/
public lemma controlledRegisterSwap_binaryMatrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((circuit oracles width).binaryMatrix environment) =
      UnitaryOperator.controlledQubits (swapRegistersOp width) := by
  classical
  apply Subtype.ext
  ext row column
  obtain ⟨⟨firstControl, firstWords⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := width + width)).surjective row
  obtain ⟨⟨firstLeft, firstRight⟩, rfl⟩ :=
    (prodEquiv (m := width) (n := width)).surjective firstWords
  obtain ⟨⟨secondControl, secondWords⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := width + width)).surjective column
  obtain ⟨⟨secondLeft, secondRight⟩, rfl⟩ :=
    (prodEquiv (m := width) (n := width)).surjective secondWords
  change ((circuit oracles width).matrix environment)
    (decoded width firstControl firstLeft firstRight)
    (decoded width secondControl secondLeft secondRight) = _
  rw [circuit, UnitaryCircuit.macroCall_matrix, sequence_matrix]
  refine (UnitaryOperator.ofPerm_entry (R := (layout width).register)
    (sequencePermutation width (List.finRange width))
    (decoded width firstControl firstLeft firstRight)
    (decoded width secondControl secondLeft secondRight)).trans ?_
  rw [complete_decoded, target_entry]
  by_cases zero : firstControl = 0
  · rw [if_pos zero]
    refine (if_congr (decoded_eq_iff width firstControl secondControl
      firstLeft firstRight secondLeft secondRight) rfl rfl).trans ?_
    fin_cases firstControl <;> fin_cases secondControl <;> simp_all
  · rw [if_neg zero]
    refine (if_congr (decoded_eq_iff width firstControl secondControl
      firstRight firstLeft secondLeft secondRight) rfl rfl).trans ?_
    fin_cases firstControl <;> fin_cases secondControl <;> simp_all

end

end QuantumAlg.Gate.ControlledRegisterSwap
