/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Endpoint
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Endpoint
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Endpoint.Execution

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
public import QuantumAlg.Primitives.MAU.Exponentiation.WordAction
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Problem

import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Requirement
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Examples
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Native arbitrary-target XOR exponentiation with internal work preparation

The incoming exponent and target may be in any normalized joint state.
The actual program prepares the missing identity-power and zero auxiliary
words, executes the literal selected-power gate list, and retains every live system.
Its independent complete state target includes every external reference.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete reversible XOR protocol has unit success probability. -/
public lemma gidneyExponentiation_problem_successLB (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (environment : model.Environment)
    (witness : (problem exponentWidth width modulus positive base).Witness) :
    ((problem exponentWidth width modulus positive base).successLB environment witness).value =
      1 := by
  rfl

/-- Independent scalar ceiling for each actual native gate coordinate,
including identity loading, copying and the complete uncomputation. -/
@[expose] public def gidneyExponentiationGateCountBound (exponentWidth width : Nat) : Nat :=
  let offset := fun n => n * (39 * Nat.clog 2 n + 1)
  let modularOffset := 6 * offset (width + 1) + 30 * offset width + 24 * width + 18
  let stage := if width ≤ 2 then 9 else 4 * modularOffset
  8 * exponentWidth * (2 * width * stage + 3 * width) + 3 * width

/-- Every native coordinate is counted on the same named public execution. -/
public lemma gidneyExponentiation_nativeGateCount_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (coordinate : AlgorithmGate.Coordinate)
    (path : (algorithm exponentWidth width modulus positive base).run.code.Path) :
    ResourcePool.count (model := model) (.gate coordinate)
      ((algorithm exponentWidth width modulus positive base).run.code.resourcePool path) ≤
        gidneyExponentiationGateCountBound exponentWidth width :=
  by
    have offset : Addition.Gidney.modularOffsetEventBound width =
        6 * ((width + 1) * (39 * Nat.clog 2 (width + 1) + 1)) +
          30 * (width * (39 * Nat.clog 2 width + 1)) + 24 * width + 18 := by
      simp only [Addition.Gidney.modularOffsetEventBound, Addition.Gidney.pivotEventBound,
        Addition.Gidney.biFlipEventBound, Addition.Gidney.comparisonEventBound,
        Addition.Gidney.constantOffsetEventBound, Nat.add_comm 1 width]
      ring
    simpa only [algorithm, gidneyExponentiationGateCountBound, Multiplication.Gidney.eventBound,
      Multiplication.Accumulate.Gidney.stageEventBound, offset, Nat.mul_assoc] using
      arithmeticNativeCode_gate_count_le exponentWidth width modulus positive base coordinate path

private lemma gateCountBound_explicit (exponentWidth width : Nat) :
    gidneyExponentiationGateCountBound exponentWidth width ≤
      24 * exponentWidth * width *
        ((3744 * width + 624) * Nat.clog 2 (width + 1) + 160 * width + 65) +
          3 * width := by
  have monotone := Nat.clog_mono_right 2 (Nat.le_succ width)
  have stage :
      (if width ≤ 2 then 9 else
        4 * (6 * ((width + 1) * (39 * Nat.clog 2 (width + 1) + 1)) +
          30 * (width * (39 * Nat.clog 2 width + 1)) + 24 * width + 18)) ≤
        (5616 * width + 936) * Nat.clog 2 (width + 1) + 240 * width + 96 := by
    split_ifs
    · omega
    · nlinarith [Nat.mul_le_mul_left (4680 * width) monotone]
  unfold gidneyExponentiationGateCountBound
  dsimp only
  nlinarith [Nat.mul_le_mul_left (16 * exponentWidth * width) stage]

private lemma cnotCountBound_explicit (exponentWidth width : Nat) :
    2 * selectedPowerCnotBound exponentWidth width + width ≤
      24 * exponentWidth * width ^ 2 * (39 * Nat.clog 2 (width + 1) + 2) + width := by
  have monotone := Nat.clog_mono_right 2 (Nat.le_succ width)
  have refined := Multiplication.Gidney.controlledCnotBound_le_logarithmic width
  unfold selectedPowerCnotBound
  calc
    _ ≤ 2 * (exponentWidth *
        (12 * width * (Addition.Gidney.constantOffsetEventBound width + width))) + width :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left exponentWidth refined)) width
    _ = 24 * exponentWidth * width ^ 2 * (39 * Nat.clog 2 width + 2) + width := by
      unfold Addition.Gidney.constantOffsetEventBound
      ring
    _ ≤ _ := Nat.add_le_add_right
      (Nat.mul_le_mul_left (24 * exponentWidth * width ^ 2)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 39 monotone) 2)) width

/-- Explicit separate native counts of the same full-state execution, for every fitted modulus. -/
public lemma gidneyExponentiation_public_counts (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (algorithm exponentWidth width modulus positive base).run.code.Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
        ((algorithm exponentWidth width modulus positive base).run.code.resourcePool path) ≤
        24 * exponentWidth * width *
          ((3744 * width + 624) * ⌈Real.logb 2 (width + 1 : Nat)⌉₊ +
            160 * width + 65) + 3 * width ∧
      ResourcePool.count (model := model) (.gate .cnot)
        ((algorithm exponentWidth width modulus positive base).run.code.resourcePool path) ≤
          24 * exponentWidth * width ^ 2 *
            (39 * ⌈Real.logb 2 (width + 1 : Nat)⌉₊ + 2) + width ∧
      ResourcePool.count (model := model) (.gate .singleQubit)
        ((algorithm exponentWidth width modulus positive base).run.code.resourcePool path) ≤ 2 := by
  refine ⟨?_, ?_,
    arithmeticNativeCode_singleQubit_count exponentWidth width modulus positive base path⟩
  · rw [show (2 : Real) = ((2 : Nat) : Real) from rfl, Real.natCeil_logb_natCast]
    exact (gidneyExponentiation_nativeGateCount_le exponentWidth width modulus positive base
      .toffoli path).trans (gateCountBound_explicit exponentWidth width)
  · rw [show (2 : Real) = ((2 : Nat) : Real) from rfl, Real.natCeil_logb_natCast]
    exact (arithmeticNativeCode_cnot_count_le exponentWidth width modulus positive base path).trans
      (cnotCountBound_explicit exponentWidth width)

/-- Both input fields and both internally prepared work words remain in the complete output. -/
public lemma gidneyExponentiation_output_listing (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (algorithm exponentWidth width modulus positive base).run.output.listing =
      (preparedContext exponentWidth width).keys := (rfl)

/-- The public problem includes its complete joint-state requirement. -/
public lemma gidneyExponentiation_stateRequirement_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    (environment : model.Environment)
    (witness : (problem exponentWidth width modulus positive base).Witness) :
    ((problem exponentWidth width modulus positive base).states environment witness).length = 1 :=
  (rfl)

/-- The resident budget counts the supplied exponent and target plus exactly two prepared words. -/
public lemma gidneyExponentiation_resident_budget (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).resources.resident =
      space (exponentWidth + 3 * width) := (rfl)

/-- The supplied exponent and target are excluded from auxiliary space; only
the two internally prepared words are charged. -/
public lemma gidneyExponentiation_auxiliary_budget (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    (problem exponentWidth width modulus positive base).resources.auxiliary =
      space (2 * width) := (rfl)

set_option maxHeartbeats 800000 in
-- The endpoint proof expands both the native execution trace and the borrowed-register
-- observation; the larger budget is confined to this theorem.
/-- Actual preparation and XOR exponentiation satisfy the complete independent native problem. -/
public lemma gidneyExponentiation_solves
    (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    Algorithm.Solves (algorithm exponentWidth width modulus positive base)
      (problem exponentWidth width modulus positive base) :=
  complete_correct exponentWidth width modulus positive base

end

end QuantumAlg.MAU.Exponentiation.Gidney
