/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Space
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources

/-!
# Independent native budgets for the chain and actual final selection

Every requested batch is charged through its existing actual chain envelope.
The final tail pays every optional unpack and selection copy and one pack.
Only the selected optional word remains allocated; three lexical cells add
one classical scratch peak. Quantum capacity is independent of batch count.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

open Execution
open ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- Independent events for every chronological option and the sole final paid pack. -/
def selectionEnvelope (N length : Nat) : ResourcePool .quantum :=
  Optional.Allocation.eventEnvelope .quantum (modulusBits N) length

/-- The entire actual chain precedes the independent final selection ledger. -/
def eventEnvelope (N count : Nat) : ResourcePool .quantum :=
  NativeRetryChain.eventEnvelope N count + selectionEnvelope N (count + 1)

/-- All batch dependencies precede optional unpack, direct selection and final packing. -/
def depthBound (N count : Nat) : Nat :=
  NativeRetryChain.depthBound N count + (3 * (count + 1) + 1)

/-- Only one optional factor is permanently added to the original chain context. -/
def outputSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N)

/-- The tail owns its retained output beside the three actual lexical selection cells. -/
def tailAdditionalSpace (N : Nat) : SpacePool .quantum :=
  outputSpace N + Optional.Allocation.scratchSpace .quantum (modulusBits N)

/-- Every actual chain cell and the single selected output remain live at completion. -/
def retainedSpace (N count : Nat) : SpacePool .quantum :=
  NativeRetryChain.retainedSpace N count + outputSpace N

/-- Sequential peaks retain the chain cells and charge final selection scratch only once. -/
def additionalSpace (N count : Nat) : SpacePool .quantum :=
  SpacePool.max (NativeRetryChain.additionalSpace N count)
    (NativeRetryChain.retainedSpace N count + tailAdditionalSpace N)

/-- The selected output adds precisely one presence bit and one modulus-width word. -/
theorem outputSpace_bits (N : Nat) :
    outputSpace N = SpacePool.ofShape (.bits (modulusBits N + 1)) := by
  apply SpacePool.ext
  intro axis
  cases axis <;> simp [outputSpace, LatticeBatchRecoveryOutput.OutputShape, SpacePool.ofShape]
  omega

/-- Neither the retained output nor the three lexical cells introduces a quantum system. -/
theorem tailAdditionalSpace_quantum (N : Nat) (dimension : ℕ+) :
    tailAdditionalSpace N (.quantumSystems dimension) = 0 := by
  rw [tailAdditionalSpace, outputSpace_bits]
  rfl

/-- The complete quantum peak allowance is independent of the number of later batches. -/
theorem additionalSpace_quantum (N count : Nat) (dimension : ℕ+) :
    additionalSpace N count (.quantumSystems dimension) =
      additionalSpace N 0 (.quantumSystems dimension) := by
  simp only [additionalSpace, SpacePool.max, Pi.add_apply,
    NativeRetryChain.additionalSpace_quantum, NativeRetryChain.retainedSpace_quantum]

/-- The real selected-output allocation has exactly the declared resident capacity. -/
theorem context_resident (source : RuntimeCtx .quantum) (N : Nat) :
    (context source N).residentSpace = outputSpace N + source.residentSpace :=
  RuntimeCtx.residentSpace_addRetained source (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh

/-- The real retained result has the same precise owned auxiliary capacity. -/
theorem context_auxiliary (source : RuntimeCtx .quantum) (N : Nat) :
    (context source N).auxiliarySpace = outputSpace N + source.auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addRetained source (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh

private theorem sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit pre middle) (second : Circuit middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

variable {source : RuntimeCtx .quantum} {N length : Nat}

/-- Actual retained allocation and optional selection obey the independent native ledger. -/
theorem tail_pool_le
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (tail inputs).Path) :
    (tail inputs).resourcePool path ≤ selectionEnvelope N length :=
  Optional.Allocation.into_pool_le _ _ path.2

/-- Every actual tail path contains at most three events per source and one final pack. -/
theorem tail_eventCount_le
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (tail inputs).Path) :
    ((tail inputs).eventTrace path).length ≤ 3 * length + 1 := by
  have bounded := Multiset.card_le_card (tail_pool_le inputs path)
  exact bounded.trans_eq (Optional.Allocation.eventEnvelope_card .quantum (modulusBits N) length)

/-- The actual serial tail obeys the same unpack/copy/pack duration formula. -/
theorem tail_depth_le
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (tail inputs).Path) :
    (tail inputs).depth (fun _ => 1) path ≤ 3 * length + 1 :=
  (Nat.zero_add _).le.trans (Optional.Allocation.into_depth_le _ _ path.2)

/-- Every tail resident peak includes the original source, selected output and lexical scratch. -/
theorem tail_resident_le
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (tail inputs).Path) :
    (tail inputs).peakResidentSpace path ≤ source.residentSpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max (source.residentSpace axis) (max ((context source N).residentSpace axis) 0) ≤ _
    rw [context_resident]
    change max _ (max (outputSpace N axis + source.residentSpace axis) 0) ≤
      source.residentSpace axis + (outputSpace N axis +
        Optional.Allocation.scratchSpace .quantum (modulusBits N) axis)
    omega
  · have bounded := Optional.Allocation.into_resident_le
      (fun index => liftInput source N (inputs index)) (resultRef source N) path.2
    rw [context_resident] at bounded
    exact bounded.trans_eq (by unfold tailAdditionalSpace; ac_rfl)

/-- The same actual tail charges retained ownership and lexical auxiliary capacity once. -/
theorem tail_auxiliary_le
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (tail inputs).Path) :
    (tail inputs).peakAuxiliarySpace path ≤ source.auxiliarySpace + tailAdditionalSpace N := by
  unfold tail at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · intro axis
    change max (source.auxiliarySpace axis) (max ((context source N).auxiliarySpace axis) 0) ≤ _
    rw [context_auxiliary]
    change max _ (max (outputSpace N axis + source.auxiliarySpace axis) 0) ≤
      source.auxiliarySpace axis + (outputSpace N axis +
        Optional.Allocation.scratchSpace .quantum (modulusBits N) axis)
    omega
  · have bounded := Optional.Allocation.into_auxiliary_le
      (fun index => liftInput source N (inputs index)) (resultRef source N) path.2
    rw [context_auxiliary] at bounded
    exact bounded.trans_eq (by unfold tailAdditionalSpace; ac_rfl)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Every actual full path pays for the same chain and every final selection instruction. -/
theorem code_pool_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).resourcePool path ≤ eventEnvelope N count :=
  (sequence_pool (NativeRetryChain.code base noQuantum input count)
    (tail (NativeRetryChain.resultRefs base noQuantum N count)) path).le.trans
      (add_le_add (NativeRetryChain.code_pool_le base noQuantum input count path.1)
        (tail_pool_le _ path.2))

/-- The independent combined ledger bounds the event count of that same complete path. -/
theorem code_eventCount_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    ((code base noQuantum input count).eventTrace path).length ≤ (eventEnvelope N count).card :=
  Multiset.card_le_card (code_pool_le base noQuantum input count path)

/-- The full actual dependency chain includes selection after every requested batch. -/
theorem code_depth_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).depth (fun _ => 1) path ≤ depthBound N count :=
  Nat.add_le_add (NativeRetryChain.code_depth_le base noQuantum input count path.1)
    (tail_depth_le _ path.2)

/-- The final complete context contains exactly all chain cells and the retained selected word. -/
theorem code_context_resident (N count : Nat) :
    (context (NativeRetryChain.context base noQuantum N count) N).residentSpace =
      base.residentSpace + retainedSpace N count := by
  rw [context_resident, NativeRetryChain.context_resident]
  unfold retainedSpace
  ac_rfl

/-- The complete final auxiliary capacity has exactly the same retained additions. -/
theorem code_context_auxiliary (N count : Nat) :
    (context (NativeRetryChain.context base noQuantum N count) N).auxiliarySpace =
      base.auxiliarySpace + retainedSpace N count := by
  rw [context_auxiliary, NativeRetryChain.context_auxiliary]
  unfold retainedSpace
  ac_rfl

/-- The peak combines the actual chain peak and one final selection peak by a maximum. -/
theorem code_resident_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N count := by
  refine (Circuit.peakResidentSpace_seq (NativeRetryChain.code base noQuantum input count)
    (tail (NativeRetryChain.resultRefs base noQuantum N count)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeRetryChain.code_resident_le base noQuantum input count path.1).trans
      (add_le_add (le_refl _) (SpacePool.le_max_left _ _))
  · have bounded := tail_resident_le (NativeRetryChain.resultRefs base noQuantum N count) path.2
    rw [NativeRetryChain.context_resident, add_assoc] at bounded
    exact bounded.trans (add_le_add (le_refl _) (SpacePool.le_max_right _ _))

/-- Retained cells accumulate, while quantum and classical temporary capacity are peak bounds. -/
theorem code_auxiliary_le (input : Input N) (count : Nat)
    (path : (code base noQuantum input count).Path) :
    (code base noQuantum input count).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N count := by
  refine (Circuit.peakAuxiliarySpace_seq (NativeRetryChain.code base noQuantum input count)
    (tail (NativeRetryChain.resultRefs base noQuantum N count)) path).le.trans ?_
  apply SpacePool.max_le
  · exact (NativeRetryChain.code_auxiliary_le base noQuantum input count path.1).trans
      (add_le_add (le_refl _) (SpacePool.le_max_left _ _))
  · have bounded := tail_auxiliary_le (NativeRetryChain.resultRefs base noQuantum N count) path.2
    rw [NativeRetryChain.context_auxiliary, add_assoc] at bounded
    exact bounded.trans (add_le_add (le_refl _) (SpacePool.le_max_right _ _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
