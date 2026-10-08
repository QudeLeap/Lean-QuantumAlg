/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources

/-!
# Independent native resources of the complete new short-DLP member

The preparation budget lists its single-qubit instructions directly. Each
inverse QFT has independently specified single-qubit and CNOT coordinates,
including the native decomposition of every controlled phase and swap.
These surround the two actual selected-power folds. No implementation
resource projection defines a specification budget, and no controlled
arithmetic gate is identified with its uncontrolled base label.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Independent Hadamard coordinates of the source exponent preparation. -/
def preparationEventEnvelope (m ell : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.singleton (.gate .singleQubit) (ell + m + ell)

/-- Independent pool of all native instructions in one inverse QFT. -/
def qftEventEnvelope (bits : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (bits + 3 * bits.choose 2) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (2 * bits.choose 2 + 3 * (bits / 2))

/-- The source readout runs one inverse QFT on each exponent word. -/
def readoutEventEnvelope (m ell : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  qftEventEnvelope (ell + m) + qftEventEnvelope ell

theorem preparationCircuit_eventCost_eq_envelope (m ell width : Nat) :
    (preparationCircuit (registerParameters m ell width)).eventCost =
      preparationEventEnvelope m ell := by
  change (Gate.HadamardLayer.circuit .empty (ell + m + ell)).eventCost = _
  rw [Gate.HadamardLayer.hadamardLayer_circuit_eventCost]
  simp [preparationEventEnvelope, ResourcePool.singleton, Multiset.nsmul_singleton]

/-- The independently specified native inverse-QFT pool is exact. -/
theorem shortDLP_inverseQFT_eventCost_eq_envelope (bits : Nat) :
    (QuantumFourierTransform.Native.inverseCircuit .empty bits).eventCost =
      qftEventEnvelope bits := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event
    (QuantumFourierTransform.Native.inverseCircuit .empty bits).eventCost = _
  rw [QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count]
  simp [qftEventEnvelope, ResourcePool.singleton, Multiset.count_replicate, eq_comm]

theorem readoutCircuit_eventCost_eq_envelope (m ell width : Nat) :
    (readoutCircuit (registerParameters m ell width)).eventCost =
      readoutEventEnvelope m ell := by
  change (QuantumFourierTransform.Native.inverseCircuit .empty (ell + m)).eventCost +
    ((QuantumFourierTransform.Native.inverseCircuit .empty ell).relabel
      (UnitaryCircuit.binarySuffixShift (ell + m))).eventCost = _
  rw [UnitaryCircuit.relabel_eventCost, shortDLP_inverseQFT_eventCost_eq_envelope,
    shortDLP_inverseQFT_eventCost_eq_envelope]
  rfl

/-- Complete family budget, retaining every controlled native coordinate. -/
def compiledCircuitEventEnvelope (m ell width N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  preparationEventEnvelope m ell +
    (compiledGroupActionEventEnvelope m ell width N + readoutEventEnvelope m ell)

private def eventInClassicalContext (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) :
    Resource.Event (.quantum AlgorithmGate.model .empty) →
      Resource.Event (.quantum AlgorithmGate.model .empty operations services)
  | .classicalOperation impossible => nomatch impossible
  | .classicalQuery impossible => nomatch impossible
  | .gate coordinate => .gate coordinate
  | .oracle impossible => nomatch impossible
  | .preparation dimension => .preparation dimension
  | .measurement dimension => .measurement dimension

private theorem eventInClassicalContext_injective (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) :
    Function.Injective (eventInClassicalContext operations services) := by
  intro left right equality
  cases left <;> cases right <;> try cases ‹Empty›
  all_goals simp_all [eventInClassicalContext]

private theorem count_context_pool (operations : ClassicalOpModel)
    (services : ClassicalOracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model .empty))
    (pool : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count (eventInClassicalContext operations services event)
        (pool.map (eventInClassicalContext operations services)) =
      ResourcePool.count event pool := by
  unfold ResourcePool.count
  rw [Multiset.count_map]
  simpa [(eventInClassicalContext_injective operations services).eq_iff] using
    (Multiset.count_eq_card_filter_eq pool event).symm

/-- The same independent native budget in a selected classical context.
Only the event inclusion changes; every specified multiplicity is retained. -/
def compiledCircuitEventEnvelopeInClassicalContext (m ell width N : Nat)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    ResourcePool (.quantum AlgorithmGate.model .empty operations services) :=
  (compiledCircuitEventEnvelope m ell width N).map (eventInClassicalContext operations services)

/-- Number of native events in one source QFT construction. -/
def qftPrimitiveBound (bits : Nat) : Nat :=
  bits + 5 * bits.choose 2 + 3 * (bits / 2)

/-- Source controlled-phase occurrences before their native decomposition.
This statistic is not a count of native resource coordinates. -/
def qftRotationCount (m ell : Nat) : Nat :=
  (m + ell) * (m + ell - 1) / 2 + ell * (ell - 1) / 2

/-- Sum of the independent coordinate caps and exact preparation/readout counts. -/
def polynomialPrimitiveBound (m ell width N : Nat) : Nat :=
  groupActionPrimitiveBound m ell width N + (m + 2 * ell) +
    qftPrimitiveBound (m + ell) + qftPrimitiveBound ell

/-- Modulus-independent ceiling of the full native budget's cardinality. -/
def polynomialPrimitiveWidthBound (m ell width : Nat) : Nat :=
  groupActionPrimitiveWidthBound m ell width + (m + 2 * ell) +
    qftPrimitiveBound (m + ell) + qftPrimitiveBound ell

theorem polynomialPrimitiveBound_le_widthBound (m ell width N : Nat) :
    polynomialPrimitiveBound m ell width N ≤ polynomialPrimitiveWidthBound m ell width := by
  unfold polynomialPrimitiveBound polynomialPrimitiveWidthBound
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      (Nat.add_le_add_right (groupActionPrimitiveBound_le_widthBound m ell width N) _)
      _) _

@[simp] theorem preparationEventEnvelope_card (m ell : Nat) :
    (preparationEventEnvelope m ell).card = m + 2 * ell := by
  simp only [preparationEventEnvelope, ResourcePool.singleton,
    Multiset.card_replicate]
  omega

@[simp] theorem qftEventEnvelope_card (bits : Nat) :
    (qftEventEnvelope bits).card = qftPrimitiveBound bits := by
  simp only [qftEventEnvelope, Multiset.card_add, ResourcePool.singleton,
    Multiset.card_replicate, qftPrimitiveBound]
  omega

theorem shortDLP_inverseQFT_eventCost_card (bits : Nat) :
    (QuantumFourierTransform.Native.inverseCircuit .empty bits).eventCost.card =
      qftPrimitiveBound bits := by
  rw [shortDLP_inverseQFT_eventCost_eq_envelope, qftEventEnvelope_card]

@[simp] theorem readoutEventEnvelope_card (m ell : Nat) :
    (readoutEventEnvelope m ell).card =
      qftPrimitiveBound (m + ell) + qftPrimitiveBound ell := by
  rw [readoutEventEnvelope, Multiset.card_add, qftEventEnvelope_card, qftEventEnvelope_card,
    Nat.add_comm ell m]

@[simp] theorem compiledCircuitEventEnvelope_card (m ell width N : Nat) :
    (compiledCircuitEventEnvelope m ell width N).card =
      polynomialPrimitiveBound m ell width N := by
  simp only [compiledCircuitEventEnvelope, Multiset.card_add, preparationEventEnvelope_card,
    compiledGroupActionEventEnvelope_card, readoutEventEnvelope_card, polynomialPrimitiveBound]
  omega

/-- The actual member satisfies every independent native coordinate cap. -/
theorem compiledCircuit_eventCost_le (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).eventCost ≤
      compiledCircuitEventEnvelope m ell width N := by
  rw [compiledCircuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    preparationCircuit_eventCost_eq_envelope, readoutCircuit_eventCost_eq_envelope,
    compiledCircuitEventEnvelope]
  exact ResourcePool.add_mono le_rfl
    (ResourcePool.add_mono (compiledGroupActionProgram_eventCost_le m ell width N g x) le_rfl)

/-- The same independent coordinate caps apply inside any classical execution context. -/
theorem compiledCircuit_event_count_classical_context_le
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model .empty operations services)) :
    ResourcePool.count event
        ((compiledCircuit m ell width N g x).eventCost operations services) ≤
      match event with
      | .gate coordinate =>
          ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.gate coordinate) (compiledCircuitEventEnvelope m ell width N)
      | .oracle coordinate =>
          ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
            (.oracle coordinate) (compiledCircuitEventEnvelope m ell width N)
      | .classicalOperation _ | .classicalQuery _ | .preparation _ | .measurement _ => 0 := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      exact (ResourcePool.le_iff_count.mp (compiledCircuit_eventCost_le m ell width N g x)) _
  | oracle coordinate =>
      exact (ResourcePool.le_iff_count.mp (compiledCircuit_eventCost_le m ell width N g x)) _
  | _ => exact Nat.le_refl 0

/-- A classical controller retains the full independently stated native resource bound. -/
theorem compiledCircuit_eventCost_le_classical_context
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (compiledCircuit m ell width N g x).eventCost operations services ≤
      compiledCircuitEventEnvelopeInClassicalContext m ell width N operations services := by
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
          (compiledCircuit m ell width N g x).eventCost ≤
        ResourcePool.count
          (eventInClassicalContext operations services (.gate coordinate))
          ((compiledCircuitEventEnvelope m ell width N).map
            (eventInClassicalContext operations services))
      rw [count_context_pool]
      exact (ResourcePool.le_iff_count.mp (compiledCircuit_eventCost_le m ell width N g x)) _
  | oracle impossible => nomatch impossible
  | _ => exact Nat.zero_le _

/-- Context inclusion retains the closed cardinality of the independent native budget. -/
@[simp] theorem compiledCircuitEventEnvelopeInClassicalContext_card
    (m ell width N : Nat) (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (compiledCircuitEventEnvelopeInClassicalContext m ell width N operations services).card =
      polynomialPrimitiveBound m ell width N := by
  rw [compiledCircuitEventEnvelopeInClassicalContext, Multiset.card_map,
    compiledCircuitEventEnvelope_card]

theorem compiledCircuit_eventCount_le_polynomial (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).eventCost.card ≤
      polynomialPrimitiveBound m ell width N :=
  (Multiset.card_le_card (compiledCircuit_eventCost_le m ell width N g x)).trans_eq
    (compiledCircuitEventEnvelope_card m ell width N)

/-- Tighter total-occurrence bound of the actual complete member. -/
def compiledCircuitActualEventBound (m ell width : Nat) : Nat :=
  groupActionActualEventBound m ell width + (m + 2 * ell) +
    qftPrimitiveBound (m + ell) + qftPrimitiveBound ell

theorem compiledCircuit_actual_event_bound (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledCircuit m ell width N g x).eventCost.card ≤
      compiledCircuitActualEventBound m ell width := by
  rw [compiledCircuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    preparationCircuit_eventCost_eq_envelope, readoutCircuit_eventCost_eq_envelope]
  simp only [Multiset.card_add, preparationEventEnvelope_card, readoutEventEnvelope_card]
  have group := compiledGroupActionProgram_actual_event_bound m ell width N g x
  unfold compiledCircuitActualEventBound
  omega

end

end QuantumAlg.ShortDLP.CompiledMAU
