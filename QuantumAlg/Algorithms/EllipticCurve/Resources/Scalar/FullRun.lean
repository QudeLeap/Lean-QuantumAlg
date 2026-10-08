/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-! # Seven-coordinate event arithmetic for the full original symbolic ECC run -/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured ScalarMultiplication.MeasuredPlacement
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

/-- Unit weighting counts every literal occurrence in the same independent event pool. -/
theorem scalar_unitWeight_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun _ => 1) pool = pool.card := by
  simp [ResourcePool.weightedCount, Multiset.map_const']

private theorem initialization_singleQubit_scalar (modulus count : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit)
      (ResourcePool.ofList (Allocation.initializationTrace modulus count)) ≤
        Scalar.loadBits modulus.size := by
  rw [initialization_gate_count, load_pool]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton_self, Nat.mul_one]
  have bounded := EncodedBit.Word.BasisLoad.basisLoad_count_le
    (MeasuredUncompute.InPlacePreparation.loadConstant modulus)
  change _ ≤ MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth modulus.size at bounded
  exact bounded.trans (by
    unfold MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth
      MAU.Inversion.SharedEEA.InputPreparation.prefixWidth
      MAU.Inversion.SharedEEA.InputPreparation.suffixWidth Scalar.loadBits
    omega)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)
  (known : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ known.order) (count : Nat)

/-- The full single-qubit allowance charges one actual load and every original round. -/
theorem repeatedRun_singleQubit_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .singleQubit) (repeatedRunBudget E known nontrivial count) ≤
      Scalar.loadBits p.size + count * Scalar.roundSingle p.size (orderWidth known) := by
  rw [repeatedRunBudget_gate_count]
  exact Nat.add_le_add (initialization_singleQubit_scalar p _)
    (Nat.mul_le_mul_left count (samplingRound_singleQubit_scalar E known))

/-- All full-run CNOTs belong to the original repeated quantum rounds. -/
theorem repeatedRun_cnot_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .cnot) (repeatedRunBudget E known nontrivial count) ≤
      count * Scalar.roundCnot p.size (orderWidth known) := by
  rw [repeatedRunBudget_gate_count, initialization_gate_count, load_pool]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton,
    Resource.Event.gate.injEq, reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  exact Nat.mul_le_mul_left count (samplingRound_cnot_scalar E known)

/-- The actual full-run Toffoli allowance is the symbolic per-round arithmetic allowance. -/
theorem repeatedRun_toffoli_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .toffoli) (repeatedRunBudget E known nontrivial count) ≤
      count * Scalar.roundToffoli p.size (orderWidth known) := by
  rw [repeatedRunBudget_gate_count, initialization_gate_count, load_pool]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton,
    Resource.Event.gate.injEq, reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  exact Nat.mul_le_mul_left count (samplingRound_toffoli_scalar E known).le

/-- Every original checked classical attempt has a width-only event ceiling. -/
theorem recoveryAttempt_events_scalar :
    (attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
      (ECDLP.Canonical.Layout.curveSpec E) (recoveryModulusSpec known nontrivial)).card ≤
        Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth known) :=
  attemptEnvelope_card_le _ _ _

/-- Quantum work contributes zero classical weight; the actual final option pack contributes one. -/
theorem repeatedRun_classicalOperations_scalar :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (repeatedRunBudget E known nontrivial count) ≤
        count * Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth known) + 1 := by
  rw [repeatedRunBudget_classicalWeight]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left count
    ((classicalWeight_le_card _).trans (recoveryAttempt_events_scalar E known nontrivial))) 1

/-- The whole independent event pool reduces to parameter arithmetic at every count. -/
theorem repeatedRun_events_scalar :
    (repeatedRunBudget E known nontrivial count).card ≤
      Scalar.wholeRunEvents p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth known) count := by
  rw [repeatedRunBudget_card]
  exact Nat.add_le_add_right
    (Nat.add_le_add (initializationTrace_length_scalar p _)
      (Nat.mul_le_mul_left count (Nat.add_le_add (samplingRound_events_scalar E known)
        (recoveryAttempt_events_scalar E known nontrivial)))) 1

end

end QuantumAlg.EllipticCurve.LogicalResources
