/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Program

/-!
# Native costs of the actual one-hot preparation

Every old unary position contributes one actual Toffoli and one actual
CNOT to its next doubled range. The shared address control keeps Toffolis
sequential, while each complete CNOT cleanup layer has depth at most one.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

namespace UnaryMoveFrame

variable {count : Nat}

/-- The original native word emits one Toffoli and one CNOT for each moved position. -/
lemma program_eventTrace (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (frame.program physical oracles).eventTrace =
      List.replicate count (.gate .toffoli) ++ List.replicate count (.gate .cnot) := by
  rw [program, UnitaryCircuit.seq_eventTrace,
    CnotLayer.program_eventTrace_exact]
  have copyTrace : (frame.copyProgram physical oracles).eventTrace =
      List.replicate count (.gate .toffoli) := by
    rw [copyProgram, Word.controlledXorIntoProgram, GateSpec.programList_eventTrace]
    simp only [Word.controlledXorIntoGates, List.map_ofFn]
    change (List.ofFn fun _ : Fin count =>
      (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model oracles))) = _
    exact List.ofFn_const _ _
  rw [copyTrace]
  simp only [cleanupLayer, List.length_ofFn]

/-- The literal event pool is derived from that original Toffoli/CNOT word. -/
lemma program_eventCost (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (frame.program physical oracles).eventCost =
      ResourcePool.scale count
          (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
            (.gate .toffoli)) +
        ResourcePool.scale count
          (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
            (.gate .cnot)) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, frame.program_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_replicate, ResourcePool.ofList_replicate]

/-- Exactly one actual Toffoli per original unary position. -/
lemma program_toffoli_count (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (frame.program physical oracles).eventCost = count := by
  have different : (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model oracles)) ≠
      .gate .cnot := by
    intro equal
    have coordinates : AlgorithmGate.Coordinate.toffoli = .cnot := Resource.Event.gate.inj equal
    cases coordinates
  simp only [frame.program_eventCost, ResourcePool.count_add, ResourcePool.count_scale,
    ResourcePool.count_singleton_self, ResourcePool.count_singleton_of_ne different,
    Nat.mul_one, Nat.mul_zero, Nat.add_zero]

/-- Exactly one actual CNOT per original unary position. -/
lemma program_cnot_count (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (frame.program physical oracles).eventCost = count := by
  have different : (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model oracles)) ≠
      .gate .toffoli := by
    intro equal
    have coordinates : AlgorithmGate.Coordinate.cnot = .toffoli := Resource.Event.gate.inj equal
    cases coordinates
  simp only [frame.program_eventCost, ResourcePool.count_add, ResourcePool.count_scale,
    ResourcePool.count_singleton_of_ne different, ResourcePool.count_singleton_self,
    Nat.mul_one, Nat.mul_zero, Nat.zero_add]

private lemma gate_quantumTime (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (gate : GateSpec encoding) :
    (gate.program physical oracles).evaluatedEventDepth Resource.Event.quantumDuration = 1 := by
  cases gate <;> rfl

private lemma word_quantumTime (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (gates : List (GateSpec encoding)) :
    (GateSpec.programList physical oracles gates).evaluatedEventDepth
      Resource.Event.quantumDuration = gates.length := by
  induction gates with
  | nil => rfl
  | cons first rest ih =>
      rw [GateSpec.programList, UnitaryCircuit.evaluatedEventDepth_seq,
        gate_quantumTime, ih, List.length_cons]
      omega

/-- Only the CNOT layer is parallel; the shared-control Toffolis retain their sequential depth. -/
lemma program_quantumTime_le (frame : UnaryMoveFrame encoding count)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (frame.program physical oracles) ≤ count + 1 := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, copyProgram,
    Word.controlledXorIntoProgram, word_quantumTime, Word.controlledXorIntoGates_length,
    frame.cleanupLayer.program_quantumTime]
  split <;> omega

end UnaryMoveFrame

namespace UnaryFrame

variable {width : Nat}

/-- All original binary-to-unary stages have their exact geometric Toffoli count. -/
lemma stagesProgramAt_toffoli_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (remaining depth : Nat) (fits : depth + remaining = width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (frame.stagesProgramAt physical oracles remaining depth fits).eventCost =
        2 ^ width - 2 ^ depth := by
  induction remaining generalizing depth with
  | zero =>
      have same : depth = width := by omega
      subst depth
      simp only [stagesProgramAt, UnitaryCircuit.identity_eventCost,
        ResourcePool.count_zero, Nat.sub_self]
  | succ remaining ih =>
      rw [stagesProgramAt, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnaryMoveFrame.program_toffoli_count, ih]
      have limit := Nat.pow_le_pow_right Nat.zero_lt_two
        (show depth + 1 ≤ width by omega)
      rw [pow_succ] at limit ⊢
      omega

/-- All original binary-to-unary stages have the same exact geometric CNOT count. -/
lemma stagesProgramAt_cnot_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (remaining depth : Nat) (fits : depth + remaining = width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (frame.stagesProgramAt physical oracles remaining depth fits).eventCost =
        2 ^ width - 2 ^ depth := by
  induction remaining generalizing depth with
  | zero =>
      have same : depth = width := by omega
      subst depth
      simp only [stagesProgramAt, UnitaryCircuit.identity_eventCost,
        ResourcePool.count_zero, Nat.sub_self]
  | succ remaining ih =>
      rw [stagesProgramAt, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnaryMoveFrame.program_cnot_count, ih]
      have limit := Nat.pow_le_pow_right Nat.zero_lt_two
        (show depth + 1 ≤ width by omega)
      rw [pow_succ] at limit ⊢
      omega

/-- The actual shared-control schedule has one parallel CNOT step per binary address bit. -/
lemma stagesProgramAt_quantumTime_le (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (remaining depth : Nat) (fits : depth + remaining = width) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (frame.stagesProgramAt physical oracles remaining depth fits) ≤
        (2 ^ width - 2 ^ depth) + remaining := by
  induction remaining generalizing depth with
  | zero =>
      have same : depth = width := by omega
      subst depth
      exact Nat.zero_le _
  | succ remaining ih =>
      have current := (frame.stage depth (by omega)).program_quantumTime_le physical oracles
      have rest := ih (depth + 1) (by omega)
      have limit := Nat.pow_le_pow_right Nat.zero_lt_two
        (show depth + 1 ≤ width by omega)
      rw [pow_succ] at limit rest
      rw [stagesProgramAt, UnitaryCircuit.evaluatedEventDepth_seq]
      omega

/-- Complete actual one-hot preparation uses one Toffoli per non-root unary position. -/
lemma program_toffoli_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (frame.program physical oracles).eventCost = 2 ^ width - 1 := by
  have seedCount : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      ((GateSpec.x (frame.target ⟨0, Nat.two_pow_pos width⟩)).program physical oracles).eventCost =
        0 := by
    rw [GateSpec.program_eventCost, ResourcePool.count_singleton]
    rfl
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, seedCount,
    frame.stagesProgramAt_toffoli_count, pow_zero, Nat.zero_add]

/-- Complete actual one-hot preparation uses one CNOT per non-root unary position. -/
lemma program_cnot_count (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (frame.program physical oracles).eventCost = 2 ^ width - 1 := by
  have seedCount : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      ((GateSpec.x (frame.target ⟨0, Nat.two_pow_pos width⟩)).program physical oracles).eventCost =
        0 := by
    rw [GateSpec.program_eventCost, ResourcePool.count_singleton]
    rfl
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, seedCount,
    frame.stagesProgramAt_cnot_count, pow_zero, Nat.zero_add]

/-- The original seed and actual shared-control layers give this complete native depth bound. -/
lemma program_quantumTime_le (frame : UnaryFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (frame.program physical oracles) ≤ 2 ^ width + width := by
  have stages := frame.stagesProgramAt_quantumTime_le physical oracles width 0 (by omega)
  have seedTime : UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      ((GateSpec.x (frame.target ⟨0, Nat.two_pow_pos width⟩)).program physical oracles) = 1 := rfl
  have positive := Nat.two_pow_pos width
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, seedTime]
  simp only [pow_zero] at stages
  omega

end UnaryFrame

end

end QuantumAlg.EncodedBit.WindowLookup
