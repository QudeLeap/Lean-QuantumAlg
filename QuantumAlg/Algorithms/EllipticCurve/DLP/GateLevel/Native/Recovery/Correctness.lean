/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Probability.Model
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Validity
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization

/-!
# Every actual original ECDLP return is the original discrete logarithm

Actual retention initializes the acceptance latch and selected word. Each
complete sample and checked recovery preserves the selected range and point
equation. The same borrowed public inputs hold on every positive execution
prefix. Actual final packing therefore returns only the original unique
secret, for arbitrary full input/reference states admitted at the original
boundary. This correctness claim requires no sampling probability premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem four_stage_support {kind : ProblemKind}
    {origin first second final result : RuntimeCtx kind}
    (setup : Circuit origin first) (allocation : Circuit first second)
    (body : Circuit second final) (packing : Circuit final result)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (predicate : Store result → Prop) :
    storeSupported ((setup.seq ((allocation.seq body).seq packing)).execute Reference initial)
        predicate ↔
      storeSupported (packing.execute Reference
        (((setup.seq allocation).seq body).execute Reference initial)) predicate := by
  simp only [Circuit.execute_seq, Circuit.execute_mapHistory, storeSupported_mapHistory]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- A present word in any positive actual recovery record is exactly the original unique secret. -/
theorem nativeECDLP_recoveryRun_supported_secret
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State (Runtime.Context.pre I) Reference H)
    (valid : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I)
    (record : Store _ × (H ×
      (recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
        count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).code.Path))
    (positive : 0 < (((recoveryRun (Runtime.Context.pre I)
      (PublicInput.nativeECDLP_input_quantumWires I) I B A count
      (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).code.execute
        Reference initial).block record).mass)
    (value : (CShape.unsignedWord (FiniteCyclicDLP.orderWidth (problem I))).Value)
    (output : record.1.read (batchResultRead
      (context (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I)
      (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))) = .optionSome value) :
    value = CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I)) (input I).secret.val := by
  let : Fact p.Prime := ⟨E.prime⟩
  let base := Runtime.Context.pre I
  have noQuantum := PublicInput.nativeECDLP_input_quantumWires I
  let width := Layout.fieldWidth E
  let scalarWidth := FiniteCyclicDLP.orderWidth (problem I)
  let terminal := context base noQuantum I
  let sampleRef := sampleInput base noQuantum I
  let baseRef := liftInput base noQuantum I (Runtime.Context.baseRef I)
  let targetRef := liftInput base noQuantum I (Runtime.Context.targetRef I)
  let curve := Layout.curveSpec E
  let modulus := recoveryModulus I
  let sampleCode := reusedSample base noQuantum I B A
  have supported := nativeECDLP_reusedSample_isLocal base noQuantum I B A
  let setup := allocate base noQuantum I
  let allocation := retainPersistent terminal width scalarWidth
  let body := sampledAttempts sampleCode supported count curve modulus sampleRef baseRef targetRef
  let packing := packBatchResult terminal width scalarWidth
  let invariant := fun store : Store (persistentCtx terminal width scalarWidth) =>
    (store.read (.storage (persistentSelected terminal width scalarWidth).toCStorageRef)).toNat <
      I.subgroupOrder ∧
    ((store.read (.storage (persistentAccepted terminal width scalarWidth).toCStorageRef)).toBool =
      true →
      (store.read (.storage (persistentSelected terminal width scalarWidth).toCStorageRef)).toNat •
        I.basePoint.toMathlib = I.targetPoint.toMathlib)
  have initialized : storeSupported ((setup.seq allocation).execute Reference initial)
      invariant := by
    apply (storeSupported_seq setup allocation initial invariant).mpr
    intro entry present
    have values := retainPersistent_latches_supported width scalarWidth
      (setup.execute Reference initial) entry present
    constructor
    · rw [values.2]
      change 0 % 2 ^ scalarWidth < I.subgroupOrder
      rw [Nat.zero_mod]
      exact I.subgroupOrder_pos
    · intro accepted
      rw [values.1] at accepted
      cases accepted
  have maintained : storeSupported (((setup.seq allocation).seq body).execute Reference initial)
      invariant := by
    exact sampledAttempts_supported_validity_on_prefix sampleCode supported count curve modulus
      sampleRef baseRef targetRef I.basePoint.toMathlib I.targetPoint.toMathlib initial
      (fun priorCode => PublicInput.nativeECDLP_persistent_supported_represents I
        priorCode initial valid) (setup.seq allocation) initialized
  have packed : storeSupported
      (packing.execute Reference (((setup.seq allocation).seq body).execute Reference initial))
      (fun store => ∀ returned, store.read (batchResultRead terminal width scalarWidth) =
        .optionSome returned → returned = CShape.wordOfNat scalarWidth (input I).secret.val) := by
    intro entry present returned same
    exact Measured.packBatchResult_supported_secret (problem I) (input I)
      (((setup.seq allocation).seq body).execute Reference initial)
      (fun earlier positive accepted =>
        ⟨(maintained earlier positive).1, (maintained earlier positive).2 accepted⟩)
      entry present returned same
  have completed := (four_stage_support setup allocation body packing initial _).mpr packed
  exact completed record positive value output

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
