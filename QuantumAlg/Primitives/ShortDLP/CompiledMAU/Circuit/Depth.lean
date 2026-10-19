/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Independent duration envelope of the complete short-DLP member

Preparation is one parallel layer of actual single-qubit instructions. The
two inverse-QFT words retain their disjoint-register parallelism, including
all single-qubit and CNOT instructions of the native decomposition. Every
duration bound refers to the actual AlgorithmGate coordinates.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Independent dependency envelope of the one parallel Hadamard layer. -/
def preparationDepthEnvelope (m ell : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  if ell + m + ell = 0 then .id else .atom (.gate .singleQubit)

private lemma hadamardLayer_duration (bits : Nat)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (Gate.HadamardLayer.circuit .empty bits).evaluatedEventDepth assignment =
      if bits = 0 then 0 else assignment (.gate .singleQubit) := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
      rw [Gate.HadamardLayer.circuit, UnitaryCircuit.castLayout_evaluatedEventDepth,
        UnitaryCircuit.tensor_native_evaluatedEventDepth]
      change max
        ((Gate.HadamardLayer.circuit .empty bits).evaluatedEventDepth assignment)
        (assignment (.gate .singleQubit)) = assignment (.gate .singleQubit)
      rw [ih]
      split <;> simp

/-- Preparation has exactly one native dependency layer for nonempty exponent storage. -/
lemma preparationCircuit_eventDepth_eval_eq_envelope (m ell width : Nat)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment
        (preparationCircuit (registerParameters m ell width)).eventDepth =
      DepthExpr.depthEval assignment (preparationDepthEnvelope m ell) := by
  change (Gate.HadamardLayer.circuit .empty (ell + m + ell)).evaluatedEventDepth assignment = _
  rw [hadamardLayer_duration]
  unfold preparationDepthEnvelope
  split <;> rfl

/-- Independent serial envelope of the actual native single-qubit and CNOT counts. -/
def qftDepthEnvelope (bits : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  .seq (.iterate (bits + 3 * bits.choose 2) (.atom (.gate .singleQubit)))
    (.iterate (2 * bits.choose 2 + 3 * (bits / 2)) (.atom (.gate .cnot)))

lemma qftDepthEnvelope_eval (bits : Nat)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment (qftDepthEnvelope bits) =
      ResourcePool.weightedCount assignment (qftEventEnvelope bits) := by
  simp only [qftDepthEnvelope, DepthExpr.depthEval_seq, DepthExpr.depthEval_iterate,
    DepthExpr.depthEval_atom, qftEventEnvelope, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton]

lemma shortDLP_inverseQFT_eventDepth_le_envelope (bits : Nat)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment
        (QuantumFourierTransform.Native.inverseCircuit .empty bits).eventDepth ≤
      DepthExpr.depthEval assignment (qftDepthEnvelope bits) := by
  rw [qftDepthEnvelope_eval]
  apply DepthExpr.depthEval_le_weightedCount_of_eventPool_le
  change (QuantumFourierTransform.Native.inverseCircuit .empty bits).resourcesFromEventDepth ≤ _
  exact le_of_eq ((UnitaryCircuit.resourcesFromEventDepth_eq_eventCost _).trans
    (shortDLP_inverseQFT_eventCost_eq_envelope bits))

@[simp] lemma qftDepthEnvelope_unit (bits : Nat) :
    DepthExpr.depthEval (fun _ => 1) (qftDepthEnvelope bits) = qftPrimitiveBound bits := by
  simp only [qftDepthEnvelope, DepthExpr.depthEval_seq, DepthExpr.depthEval_iterate,
    DepthExpr.depthEval_atom, Nat.mul_one, qftPrimitiveBound]
  omega

/-- The two native inverse-QFT envelopes execute on disjoint exponent words. -/
def readoutDepthEnvelope (m ell : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  .tensor (qftDepthEnvelope (ell + m)) (qftDepthEnvelope ell)

lemma readoutCircuit_eventDepth_le_envelope (m ell width : Nat)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment
        (readoutCircuit (registerParameters m ell width)).eventDepth ≤
      DepthExpr.depthEval assignment (readoutDepthEnvelope m ell) := by
  change max
    ((QuantumFourierTransform.Native.inverseCircuit .empty (ell + m)).evaluatedEventDepth
      assignment)
    (((QuantumFourierTransform.Native.inverseCircuit .empty ell).relabel
      (UnitaryCircuit.binarySuffixShift (ell + m))).evaluatedEventDepth
      assignment) ≤ _
  rw [UnitaryCircuit.relabel_evaluatedEventDepth]
  exact max_le_max (shortDLP_inverseQFT_eventDepth_le_envelope (ell + m) assignment)
    (shortDLP_inverseQFT_eventDepth_le_envelope ell assignment)

/-- Independent complete envelope preserving preparation and readout parallelism. -/
def compiledCircuitDepthEnvelope (m ell width N : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  .seq (preparationDepthEnvelope m ell)
    (.seq (compiledGroupActionDepthEnvelope m ell width N) (readoutDepthEnvelope m ell))

lemma compiledCircuit_eventDepth_le (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment (compiledCircuit m ell width N g x).eventDepth ≤
      DepthExpr.depthEval assignment (compiledCircuitDepthEnvelope m ell width N) := by
  rw [compiledCircuit, UnitaryCircuit.seq_eventDepth, UnitaryCircuit.seq_eventDepth,
    compiledCircuitDepthEnvelope]
  simp only [DepthExpr.depthEval_seq, preparationCircuit_eventDepth_eval_eq_envelope]
  exact Nat.add_le_add_left
    (Nat.add_le_add (compiledGroupActionProgram_eventDepth_le m ell width N g x assignment)
      (readoutCircuit_eventDepth_le_envelope m ell width assignment)) _

/-- Closed unit-duration value of the independent complete envelope. -/
def compiledCircuitEventUnitDepth (m ell width N : Nat) : Nat :=
  (if ell + m + ell = 0 then 0 else 1) +
    (groupActionPrimitiveBound m ell width N +
      max (qftPrimitiveBound (ell + m)) (qftPrimitiveBound ell))

/-- Modulus-independent ceiling preserving the preparation and readout parallelism. -/
def compiledCircuitEventUnitDepthWidthBound (m ell width : Nat) : Nat :=
  (if ell + m + ell = 0 then 0 else 1) +
    (groupActionPrimitiveWidthBound m ell width +
      max (qftPrimitiveBound (ell + m)) (qftPrimitiveBound ell))

lemma compiledCircuitDepthEnvelope_unit (m ell width N : Nat) :
    DepthExpr.depthEval (fun _ => 1) (compiledCircuitDepthEnvelope m ell width N) =
      compiledCircuitEventUnitDepth m ell width N := by
  simp only [compiledCircuitDepthEnvelope, DepthExpr.depthEval_seq,
    readoutDepthEnvelope, DepthExpr.depthEval_tensor,
    compiledGroupActionDepthEnvelope_unit, qftDepthEnvelope_unit]
  unfold compiledCircuitEventUnitDepth preparationDepthEnvelope
  split <;> rfl

lemma compiledCircuitEventUnitDepth_le_widthBound (m ell width N : Nat) :
    compiledCircuitEventUnitDepth m ell width N ≤
      compiledCircuitEventUnitDepthWidthBound m ell width := by
  exact Nat.add_le_add_left
    (Nat.add_le_add_right (groupActionPrimitiveBound_le_widthBound m ell width N) _) _

lemma compiledCircuitEventUnitDepth_le_polynomial (m ell width N : Nat) :
    compiledCircuitEventUnitDepth m ell width N ≤ polynomialPrimitiveBound m ell width N := by
  have preparation : (if ell + m + ell = 0 then 0 else 1) ≤ m + 2 * ell := by
    split <;> omega
  have readout : max (qftPrimitiveBound (ell + m)) (qftPrimitiveBound ell) ≤
      qftPrimitiveBound (m + ell) + qftPrimitiveBound ell := by
    rw [Nat.add_comm ell m]
    exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  unfold compiledCircuitEventUnitDepth polynomialPrimitiveBound
  omega

lemma compiledCircuit_eventUnitDepth_le (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).evaluatedEventDepth (fun _ => 1) ≤
      compiledCircuitEventUnitDepth m ell width N :=
  (compiledCircuit_eventDepth_le m ell width N g x (fun _ => 1)).trans_eq
    (compiledCircuitDepthEnvelope_unit m ell width N)

/-- Native depth is unchanged when the complete member runs inside a classical controller. -/
lemma compiledCircuit_eventUnitDepth_classical_context_le
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    DepthExpr.depthEval (fun _ => 1)
        ((compiledCircuit m ell width N g x).eventDepth operations services) ≤
      compiledCircuitEventUnitDepth m ell width N := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  exact compiledCircuit_eventUnitDepth_le m ell width N g x

/-- Tighter depth ceiling from actual arithmetic occurrences and parallel native readout. -/
def compiledCircuitActualDepthBound (m ell width : Nat) : Nat :=
  (if ell + m + ell = 0 then 0 else 1) +
    (groupActionActualEventBound m ell width +
      max (qftPrimitiveBound (ell + m)) (qftPrimitiveBound ell))

lemma compiledCircuit_actual_depth_bound (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).evaluatedEventDepth (fun _ => 1) ≤
      compiledCircuitActualDepthBound m ell width := by
  have group := compiledGroupActionProgram_actual_depth_bound m ell width N g x
  have readout := readoutCircuit_eventDepth_le_envelope m ell width (fun _ => 1)
  change DepthExpr.depthEval (fun _ => 1)
    (compiledCircuit m ell width N g x).eventDepth ≤ _
  rw [compiledCircuit, UnitaryCircuit.seq_eventDepth, UnitaryCircuit.seq_eventDepth]
  simp only [DepthExpr.depthEval_seq, preparationCircuit_eventDepth_eval_eq_envelope]
  unfold compiledCircuitActualDepthBound
  have preparation : DepthExpr.depthEval (fun _ => 1) (preparationDepthEnvelope m ell) =
      if ell + m + ell = 0 then 0 else 1 := by
    unfold preparationDepthEnvelope
    split <;> rfl
  rw [preparation]
  apply Nat.add_le_add_left
  apply Nat.add_le_add group
  simpa only [readoutDepthEnvelope, DepthExpr.depthEval_tensor, qftDepthEnvelope_unit]
    using readout

end

end QuantumAlg.ShortDLP.CompiledMAU
