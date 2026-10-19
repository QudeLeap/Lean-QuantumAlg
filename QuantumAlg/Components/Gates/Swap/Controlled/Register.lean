/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Qubits
import all QuantumAlg.Components.Gates.Swap.Controlled.Qubits
import all QuantumAlg.Components.Gates.Swap.Controlled.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Actual native controlled exchange of two equal-width registers

One original leading control drives the exchange of corresponding original
word positions. No work wire is allocated. The empty word has an empty circuit.
-/

namespace QuantumAlg.Gate.ControlledRegisterSwap

noncomputable section

/-- Control, left word and right word in their original big-endian physical order. -/
@[expose, implicit_reducible]
public def layout (width : Nat) : QuantumLayout (1 + (width + width)) :=
  (QuantumSignature.qubits (1 + (width + width))).canonicalPlacement.layout

/-- Leading control, shared by every actual three-gate word. -/
def control (width : Nat) : Fin (1 + (width + width)) := 0

/-- A position in the first original word. -/
def left (width : Nat) (index : Fin width) : Fin (1 + (width + width)) :=
  ⟨1 + index.val, by omega⟩

/-- The corresponding position in the second original word. -/
def right (width : Nat) (index : Fin width) : Fin (1 + (width + width)) :=
  ⟨1 + width + index.val, by omega⟩

private lemma control_left (width : Nat) (index : Fin width) :
    control width ≠ left width index := by
  intro same
  have := congrArg Fin.val same
  change 0 = 1 + index.val at this
  omega

private lemma control_right (width : Nat) (index : Fin width) :
    control width ≠ right width index := by
  intro same
  have := congrArg Fin.val same
  change 0 = 1 + width + index.val at this
  omega

private lemma left_right (width : Nat) (index : Fin width) :
    left width index ≠ right width index := by
  intro same
  have := congrArg Fin.val same
  change 1 + index.val = 1 + width + index.val at this
  omega

/-- Actual CNOT/Toffoli/CNOT on one corresponding pair, with the original leading control. -/
def pairCircuit (oracles : OracleModel) (width : Nat) (index : Fin width) :
    UnitaryCircuit AlgorithmGate.model oracles (layout width) :=
  ControlledSwap.circuitAt (layout width) (control width) (left width index) (right width index)
    (control_left width index) (control_right width index) (left_right width index) rfl rfl rfl
    oracles

/-- The independently specified complete row permutation for one pair. -/
def pairPermutation (width : Nat) (index : Fin width) : Equiv.Perm (layout width).Basis :=
  ControlledSwap.qubitPermutation (control width) (left width index) (right width index)
    (control_left width index) (control_right width index)

lemma pair_matrix (oracles : OracleModel) (width : Nat) (index : Fin width)
    (environment : oracles.Interpretation) :
    ((pairCircuit oracles width index).matrix environment) =
      UnitaryOperator.ofPerm (pairPermutation width index) :=
  ControlledSwap.controlledSwap_qubits_matrix _ _ _ _ _ _ oracles environment

/-- Sequential native words retain their common control dependency. -/
def sequence (oracles : OracleModel) (width : Nat) : List (Fin width) →
    UnitaryCircuit AlgorithmGate.model oracles (layout width)
  | [] => .identity _ _ _
  | index :: rest => (pairCircuit oracles width index).seq (sequence oracles width rest)

/-- Row-coordinate permutation of the same ordered pair list. -/
def sequencePermutation (width : Nat) : List (Fin width) → Equiv.Perm (layout width).Basis
  | [] => Equiv.refl _
  | index :: rest => (sequencePermutation width rest).trans (pairPermutation width index)

/-- Exact full matrix, prior to simplifying the complete all-position exchange. -/
lemma sequence_matrix (oracles : OracleModel) (width : Nat) (indices : List (Fin width))
    (environment : oracles.Interpretation) :
    ((sequence oracles width indices).matrix environment) =
      UnitaryOperator.ofPerm (sequencePermutation width indices) := by
  induction indices with
  | nil =>
      apply Subtype.ext
      ext row column
      rw [sequence, UnitaryCircuit.identity_matrix, sequencePermutation,
        UnitaryOperator.ofPerm_entry]
      rfl
  | cons index rest ih =>
      rw [sequence, UnitaryCircuit.seq_matrix, ih, pair_matrix, UnitaryOperator.ofPerm_mul]
      rfl

/-- The trace records every actual CNOT and Toffoli, including repetitions. -/
lemma sequence_events (oracles : OracleModel) (width : Nat) (indices : List (Fin width)) :
    (sequence oracles width indices).eventTrace =
      indices.flatMap (fun _ => [.gate .cnot, .gate .toffoli, .gate .cnot]) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [sequence, UnitaryCircuit.seq_eventTrace, pairCircuit,
        ControlledSwap.controlledSwap_circuitAt_events, ih]
      rfl

/-- Every pair has three sequential gates; every pair shares the original control. -/
lemma sequence_depth (oracles : OracleModel) (width : Nat) (indices : List (Fin width)) :
    (sequence oracles width indices).evaluatedEventDepth (fun _ => 1) = 3 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [sequence, UnitaryCircuit.evaluatedEventDepth_seq, pairCircuit,
        ControlledSwap.controlledSwap_circuitAt_unit_depth, ih, List.length_cons]
      omega

/-- Execute exactly one native controlled exchange per word position. -/
public def circuit (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles (layout width) :=
  .macroCall "controlled-register-swap" (sequence oracles width (List.finRange width))

/-- The zero-width case performs no native instruction. -/
public lemma controlledRegisterSwap_zero_events (oracles : OracleModel) :
    (circuit oracles 0).eventTrace = [] := by
  rw [circuit, UnitaryCircuit.macroCall_eventTrace]
  change (sequence oracles 0 []).eventTrace = []
  rw [sequence, UnitaryCircuit.identity_eventTrace]

/-- The actual shared-control word has exactly three steps per target pair. -/
public lemma controlledRegisterSwap_unit_depth (oracles : OracleModel) (width : Nat) :
    (circuit oracles width).evaluatedEventDepth (fun _ => 1) = 3 * width := by
  change (sequence oracles width (List.finRange width)).evaluatedEventDepth (fun _ => 1) = _
  rw [sequence_depth, List.length_finRange]

end

end QuantumAlg.Gate.ControlledRegisterSwap
