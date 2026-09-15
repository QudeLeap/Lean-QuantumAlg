/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Construction

/-!
# Exact compiled-constant phases for Draper addition

The classical addend is a compilation parameter. The layer contains one actual
one-qubit phase gate per target wire, placed in a disjoint tensor product. Its
angles match the bit-reversed output of the existing no-swap QFT: the leading
wire of an `n`-qubit target receives angle `2 pi c / 2^n`. Known rotations on
one wire combine exactly by addition of their angles
[D00, paper.tex:216-233,302,352-361].

The construction retains identity-angle gates, including when the constant is
zero. Its counts describe this literal structure. It adds no constant word,
carry storage, controlled phase, or relative-phase relaxation.
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

/-- The exact compiled angle for the leading Fourier wire of a `width`-bit word. -/
def phaseAngle (width constant : Nat) : Real :=
  2 * Real.pi * (constant : Real) / (2 : Real) ^ width

/-- The compiled angle contributes the corresponding power of the existing QFT root. -/
theorem draperPhaseAngle_exp (width constant : Nat) :
    Complex.exp ((phaseAngle width constant : Real) * Complex.I) =
      ω width ^ constant := by
  rw [ω, ← Complex.exp_nat_mul]
  congr 1
  simp only [phaseAngle]
  push_cast
  ring

private theorem phaseGate_matrix (width constant : Nat) (output input : Fin 2) :
    (phaseGate (phaseAngle width constant)).matrix output input =
      if output = input then ω width ^ (output.val * constant) else 0 := by
  fin_cases output <;> fin_cases input <;>
    simp [coe_phaseGate, phaseGateOp, draperPhaseAngle_exp]

private def prependPhase (n constant : Nat) (body : UnitaryCircuit (Qubits n))
    (hbody : body.physical_idx = List.range n) :
    UnitaryCircuit (Qubits (n + 1)) := by
  let leading := phaseGate (phaseAngle (n + 1) constant)
  let tail := UnitaryCircuit.shiftPhysicalIdx 1 body
  let layout : PhysicalLayout.DisjointMerge leading.physical_idx tail.physical_idx :=
    { left_nodup := leading.physical_idx_nodup
      right_nodup := tail.physical_idx_nodup
      disjoint := by
        rw [show leading.physical_idx = [0] from rfl,
          UnitaryCircuit.shiftPhysicalIdx_physical_idx, hbody]
        simp }
  exact UnitaryCircuit.reindex (qftPairEquiv n)
    (UnitaryCircuit.tensor leading tail layout)

private theorem prependPhase_physical_idx (n constant : Nat)
    (body : UnitaryCircuit (Qubits n)) (hbody : body.physical_idx = List.range n) :
    (prependPhase n constant body hbody).physical_idx = List.range (n + 1) := by
  unfold prependPhase
  simp only [UnitaryCircuit.reindex, UnitaryCircuit.tensor_physical_idx,
    UnitaryCircuit.shiftPhysicalIdx_physical_idx, hbody]
  change 0 :: List.map (fun index => 1 + index) (List.range n) =
    List.range (n + 1)
  simpa only [Nat.one_add] using (List.range_succ_eq_map (n := n)).symm

private theorem prependPhase_matrix_pair (n constant : Nat)
    (body : UnitaryCircuit (Qubits n)) (hbody : body.physical_idx = List.range n)
    (outputHead inputHead : Fin 2) (outputTail inputTail : Fin (2 ^ n)) :
    (prependPhase n constant body hbody).matrix
        (qftPairEquiv n (outputHead, outputTail))
        (qftPairEquiv n (inputHead, inputTail)) =
      (if outputHead = inputHead then ω (n + 1) ^ (outputHead.val * constant)
        else 0) * body.matrix outputTail inputTail := by
  unfold prependPhase
  rw [qftReindexTensor_matrix_apply_pair, UnitaryCircuit.shiftPhysicalIdx_matrix,
    phaseGate_matrix]

private def phaseLayerData (constant : Nat) :
    (n : Nat) → { circuit : UnitaryCircuit (Qubits n) //
      circuit.physical_idx = List.range n }
  | 0 => ⟨UnitaryCircuit.identity (Qubits 0) [] (by simp), rfl⟩
  | n + 1 =>
      ⟨prependPhase n constant (phaseLayerData constant n).val
          (phaseLayerData constant n).property,
        prependPhase_physical_idx n constant (phaseLayerData constant n).val
          (phaseLayerData constant n).property⟩

/-- A parallel tensor of the `n` exact one-qubit phases for a compiled constant. -/
def phaseLayer (n constant : Nat) : UnitaryCircuit (Qubits n) :=
  (phaseLayerData constant n).val

/-- The literal phase layer occupies exactly the canonical `n`-wire interface. -/
@[simp] theorem draperPhaseLayer_physical_idx (n constant : Nat) :
    (phaseLayer n constant).physical_idx = List.range n :=
  (phaseLayerData constant n).property

/-- Exact diagonal action in the bit-reversed Fourier convention already proved for QFT. -/
theorem draperPhaseLayer_matrix (n constant : Nat) (output input : Fin (2 ^ n)) :
    (phaseLayer n constant).matrix output input =
      if output = input then ω n ^ ((qftReverseBits n output).val * constant) else 0 := by
  induction n with
  | zero =>
      have hreverse : (qftReverseBits 0 output).val = 0 := by
        have hlt := (qftReverseBits 0 output).isLt
        omega
      have heq : output = input := by
        apply Fin.ext
        have houtput := output.isLt
        have hinput := input.isLt
        omega
      rw [if_pos heq, hreverse]
      simp [phaseLayer, phaseLayerData, heq]
  | succ n ih =>
      rcases (qftPairEquiv n).surjective output with ⟨⟨outputHead, outputTail⟩, rfl⟩
      rcases (qftPairEquiv n).surjective input with ⟨⟨inputHead, inputTail⟩, rfl⟩
      change (prependPhase n constant (phaseLayer n constant)
        (draperPhaseLayer_physical_idx n constant)).matrix _ _ = _
      rw [prependPhase_matrix_pair, ih, qftReverseBits_pair]
      by_cases hhead : outputHead = inputHead
      · subst inputHead
        by_cases htail : outputTail = inputTail
        · subst inputTail
          simp only [if_true]
          rw [← omega_succ_sq n, ← pow_mul, ← pow_add]
          congr 1
          ring
        · simp [htail]
      · simp [hhead]

/-- The native ledger contains one uncontrolled phase event per actual target wire. -/
theorem draperPhaseLayer_eventCost (n constant : Nat) :
    (phaseLayer n constant).eventCost =
      n • ResourcePool.singleton
        (.gate (.declared "QuantumAlg.Components.Gate" "phase")) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (prependPhase n constant (phaseLayer n constant)
        (draperPhaseLayer_physical_idx n constant)).eventCost = _
      simp only [prependPhase, UnitaryCircuit.reindex_eventCost,
        UnitaryCircuit.tensor_eventCost, UnitaryCircuit.shiftPhysicalIdx_eventCost, ih]
      change ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "phase")) +
        n • ResourcePool.singleton (.gate (.declared "QuantumAlg.Components.Gate" "phase")) = _
      rw [succ_nsmul, add_comm]

/-- The tensor schedule has one unit-depth layer when nonempty, and zero at width zero. -/
theorem draperPhaseLayer_unit_depth (n constant : Nat) :
    (phaseLayer n constant).evaluatedEventDepth (fun _ => 1) =
      if n = 0 then 0 else 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (prependPhase n constant (phaseLayer n constant)
        (draperPhaseLayer_physical_idx n constant)).evaluatedEventDepth (fun _ => 1) = _
      simp only [prependPhase, UnitaryCircuit.evaluatedEventDepth,
        UnitaryCircuit.reindex_eventDepth, UnitaryCircuit.tensor_eventDepth,
        UnitaryCircuit.shiftPhysicalIdx_eventDepth]
      change max 1 ((phaseLayer n constant).evaluatedEventDepth (fun _ => 1)) = _
      rw [ih]
      split <;> simp_all

end

end QuantumAlg.MAU.Addition.Draper
