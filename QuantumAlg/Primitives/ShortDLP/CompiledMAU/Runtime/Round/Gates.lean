/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Resources
import all QuantumAlg.Components.Encoded.BitGates.Resources

/-!
# Separate native gate coordinates of the reusable short-DLP round

The two arithmetic folds retain their independent coordinate caps. Hadamards
and the two inverse QFTs contribute their exact native coordinates. Measurement
and classical packing add no gates; actual bank correction and identity reload
add only single-qubit gates. The resulting width formulas bound every path of
the existing round, without conflating total events with any one gate type.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

/-- Independent cap for each native coordinate in the two arithmetic folds. -/
def arithmeticGateBound (m ell width : Nat) : Nat :=
  MAU.Exponentiation.Gidney.eventBound (ell + m) width +
    MAU.Exponentiation.Gidney.eventBound ell width

/-- Width-only native gate bounds for preparation, arithmetic and both inverse QFTs. -/
def memberGateBound (m ell width : Nat) : AlgorithmGate.Coordinate → Nat
  | .toffoli => arithmeticGateBound m ell width
  | .cnot => arithmeticGateBound m ell width +
      2 * (ell + m).choose 2 + 3 * ((ell + m) / 2) +
      2 * ell.choose 2 + 3 * (ell / 2)
  | .singleQubit => arithmeticGateBound m ell width +
      2 * (m + 2 * ell) + 3 * (ell + m).choose 2 + 3 * ell.choose 2

/-- The full physical reset and reload reserve only single-qubit gates. -/
def gateWidthBound (m ell width : Nat) : AlgorithmGate.Coordinate → Nat
  | .toffoli => memberGateBound m ell width .toffoli
  | .cnot => memberGateBound m ell width .cnot
  | .singleQubit => memberGateBound m ell width .singleQubit +
      2 * totalQubits (registerParameters m ell width)

private lemma exponentiation_gate_le (bits width N : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate) (exponentiationEventEnvelope bits width N) ≤
      MAU.Exponentiation.Gidney.eventBound bits width := by
  unfold exponentiationEventEnvelope
  split
  · have alphabet : ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate)
        EncodedBit.GateSpec.primitiveAlphabet = 1 := by
      cases coordinate <;>
        simp [EncodedBit.GateSpec.primitiveAlphabet, ResourcePool.ofList, ResourcePool.count]
    simp only [MAU.Exponentiation.Gidney.nativeBudget,
      MAU.Exponentiation.Gidney.stageNativeBudget, ResourcePool.count_nsmul,
      alphabet, Nat.mul_one, MAU.Exponentiation.Gidney.eventBound, le_refl]
  · exact Nat.zero_le _

/-- Each independent member coordinate keeps its own width cap and exact Fourier contribution. -/
lemma member_envelope_gate_le (m ell width N : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate coordinate) (compiledCircuitEventEnvelope m ell width N) ≤
      memberGateBound m ell width coordinate := by
  have first := exponentiation_gate_le (ell + m) width N coordinate
  have second := exponentiation_gate_le ell width N coordinate
  simp only [compiledCircuitEventEnvelope, preparationEventEnvelope,
    compiledGroupActionEventEnvelope, firstExponentiationEventEnvelope,
    secondExponentiationEventEnvelope, readoutEventEnvelope, qftEventEnvelope,
    ResourcePool.count_add, ResourcePool.count_singleton]
  cases coordinate <;> simp [memberGateBound, arithmeticGateBound] at ⊢
  all_goals omega

private lemma member_context_gate (m ell width N : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model) (.gate coordinate)
        (compiledCircuitEventEnvelopeInClassicalContext m ell width N BitWord.model .empty) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate coordinate) (compiledCircuitEventEnvelope m ell width N) :=
  count_context_pool BitWord.model .empty (.gate coordinate)
    (compiledCircuitEventEnvelope m ell width N)

/-- The complete round allowance obeys all three independently specified gate formulas. -/
lemma eventEnvelope_gate_le (m ell width N : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model) (.gate coordinate) (eventEnvelope m ell width N) ≤
      gateWidthBound m ell width coordinate := by
  have member := member_envelope_gate_le m ell width N coordinate
  have reload := shortDLP_reload_count_le m ell width N
  simp only [eventEnvelope, ResourcePool.count_add, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, member_context_gate, ZReset.Bank.envelope,
    ZReset.eventEnvelope]
  cases coordinate <;> simp [gateWidthBound] at ⊢
  all_goals omega

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  {shape : CShape} (parameter : CInputRef ctx shape)
  (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (resultBits m ell width)))

/-- Every actual native round path satisfies each separate gate-coordinate ceiling. -/
lemma shortDLP_runtimeRound_gate_le
    (path : (code m ell width sameWires parameter N generator target cells result).Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model) (.gate coordinate)
        ((code m ell width sameWires parameter N generator target cells result).resourcePool path) ≤
      gateWidthBound m ell width coordinate :=
  ((ResourcePool.le_iff_count.mp (shortDLP_runtimeRound_resourcePool_le
    m ell width sameWires parameter N generator target cells result path))
      (.gate coordinate)).trans (eventEnvelope_gate_le m ell width N coordinate)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
