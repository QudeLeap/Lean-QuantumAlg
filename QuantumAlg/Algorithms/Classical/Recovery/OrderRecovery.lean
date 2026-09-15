/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Classical.Endpoint
public import QuantumAlg.Util.Classical.Modular.Basic
public import QuantumAlg.Util.Classical.OrderRecovery
public import QuantumAlg.Components.Classical.OrderRecovery.Native.Encoding
public import QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Classical.Endpoint
import all QuantumAlg.Util.Classical.OrderRecovery
import all QuantumAlg.Core.Algorithm.RelationalLaws
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Encoding
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Retained
import all QuantumAlg.Components.Classical.OrderRecovery.Native.ClassicalCounts

/-!
# Native recovery of the first accepted continued-fraction denominator

The stored canonical unit base and arbitrary phase bits enter the actual finite
continued-fraction scan. Its first accepted denominator is retained as an
optional word. The source explains continued-fraction recovery in
[Sho95, source.tex:1624-1635]; the deterministic finite scan and native budgets
below are implementation refinements, without a least-order claim for every sample.
-/

namespace QuantumAlg.ClassicalEndpoints.Recovery.OrderRecovery

open ClassicalRoutines.OrderRecovery.Native

/-- Read the original borrowed base and raw phase bits as one structural pair. -/
public def inputRef (modulusWidth phaseBits : Nat) :
    CInputRef (Standard.pre (inputShape modulusWidth phaseBits))
      (inputShape modulusWidth phaseBits) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty ⟨0⟩
    (inputShape modulusWidth phaseBits) (by decide))

/-- Every supported local store contains a canonical unit; the phase bits are unrestricted. -/
@[expose] public def valid {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (state : ExecutionState
      (Execution.Store (Standard.pre (inputShape modulusWidth phaseBits)))
      (Standard.pre (inputShape modulusWidth phaseBits)).register) : Prop :=
  ∀ store, 0 < (state.block store).mass →
    match (store.read (inputRef modulusWidth phaseBits)).first with
    | .canonicalResidue base => base.val < spec.modulus ∧ Nat.Coprime base.val spec.modulus

/-- The actual option equals the original source result, including none and first acceptance. -/
@[expose] public def accepts {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (store : Execution.Store (Standard.pre (inputShape modulusWidth phaseBits)))
    (output : CShape.Value (outputShape phaseBits)) : Prop :=
  ∃ source : ClassicalAlgorithms.OrderRecovery.Input
      (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits),
    store.read (inputRef modulusWidth phaseBits) =
      .product (.canonicalResidue source.base) (.bits source.terminalBits) ∧
    output = match ClassicalAlgorithms.OrderRecovery.recoverUnitOrder ⟨spec⟩ source with
      | none => .optionNone
      | some word => .optionSome (.unsignedWord word)

/-- Independent finite continued-fraction recovery specification.

**Input.**
- Static modulus data $2 \le N \le 2^m$, one borrowed canonical residue $a<N$
  coprime to $N$, and arbitrary $t$ phase bits, including $t=0$.
- Validity constrains only supported local input stores and permits arbitrary
  mixtures and correlations with every external reference.
**Output.**
- The first accepted continued-fraction denominator, represented by an optional
  $(t+1)$-bit word, or an absent result when the finite scan accepts none. The complete
  output retains both the original input pair and this actual result cell.
**Resource budget.**
- At most $4(t+1)+4+2(t+1)(2m+18+6(t+1))$ literal classical operations.
- The independent width-indexed native envelope includes the padded phase
  decoder, denominator setup, at most $2(t+1)$ candidate visits with modular
  exponentiation, actual selected branches, and final option packing.
- Let $E=9(t+1)+2m+4+\max(t+1,8m+2)$. Resident classical storage is at most
  $m+t+(t+2)+E$ bits; auxiliary storage is at most $(t+2)+E$ bits.
  The retained optional result contributes $t+2$ bits. There are no quantum
  systems or quantum depth.
**Success.**
- Exact equality with the original finite recovery function holds with probability one. This does
  not assert least-order recovery or a nonempty result for every phase sample.
  Every borrowed input is restored jointly with every external reference.
**Source.**
- [Sho95, source.tex:1624-1635] describes continued-fraction order recovery.
  The finite first-acceptance semantics and concrete native allowances are
  project-derived refinements of that postprocessing step.
-/
@[expose] public def problem {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) :
    Problem .classical (Standard.pre (inputShape modulusWidth phaseBits))
      (Standard.post (inputShape modulusWidth phaseBits) (outputShape phaseBits))
      (outputShape phaseBits) where
  valid := valid (phaseBits := phaseBits) spec
  accepts := accepts (phaseBits := phaseBits) spec
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := eventEnvelope .classical modulusWidth phaseBits
      resident := fun .classicalBits => modulusWidth + phaseBits + (phaseBits + 2) +
        (9 * (phaseBits + 1) + 2 * modulusWidth + 4 +
          max (phaseBits + 1) (8 * modulusWidth + 2))
      auxiliary := fun .classicalBits => phaseBits + 2 +
        (9 * (phaseBits + 1) + 2 * modulusWidth + 4 +
          max (phaseBits + 1) (8 * modulusWidth + 2)) }
  depth := .classical

/-- Retain one option cell, execute actual native recovery, and seal the complete output. -/
public def algorithm {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) :
    Algorithm .classical (Standard.pre (inputShape modulusWidth phaseBits))
      (Standard.post (inputShape modulusWidth phaseBits) (outputShape phaseBits))
      (outputShape phaseBits) where
  run := Standard.run (retainedCircuit ⟨spec⟩ (inputRef modulusWidth phaseBits)
    Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)))

/-- The complete output contains every final live input and result key. -/
public theorem orderRecoveryEndpoint_output_listing {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) :
    (algorithm (phaseBits := phaseBits) spec).run.output.listing =
      (Standard.post (inputShape modulusWidth phaseBits) (outputShape phaseBits)).keys := by
  exact Output.all_listing _ _

/-- The real native recovery obeys the closed classical-operation allowance on every path. -/
public theorem orderRecoveryEndpoint_classical_operations_le {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (path : (algorithm (phaseBits := phaseBits) spec).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm (phaseBits := phaseBits) spec).run.code.resourcePool path) ≤
      4 * (phaseBits + 1) + 4 +
        2 * (phaseBits + 1) * (2 * modulusWidth + 18 + 6 * (phaseBits + 1)) := by
  have bounded := nativeRecovery_retained_pool_le ⟨spec⟩ (inputRef modulusWidth phaseBits)
    Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)) path
  have counted : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm (phaseBits := phaseBits) spec).run.code.resourcePool path) ≤
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (eventEnvelope .classical modulusWidth phaseBits) := by
    obtain ⟨rest, same⟩ := Multiset.le_iff_exists_add.mp bounded
    rw [same, ResourcePool.weightedCount_add]
    exact Nat.le_add_right _ _
  exact counted.trans_eq (eventEnvelope_classicalCount .classical modulusWidth phaseBits)

private def code {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) :=
  (algorithm (phaseBits := phaseBits) spec).run.code

private noncomputable def finalStore {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (store : Execution.Store (Standard.pre (inputShape modulusWidth phaseBits))) :
    Execution.Store
      (Standard.post (inputShape modulusWidth phaseBits) (outputShape phaseBits)) :=
  (retainedStep ⟨spec⟩ (inputRef modulusWidth phaseBits) Standard.resultKey
    (Standard.resultFresh (inputShape modulusWidth phaseBits)) store).1

private theorem finalStore_accepts {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (store : Execution.Store (Standard.pre (inputShape modulusWidth phaseBits)))
    (sourceGood : match (store.read (inputRef modulusWidth phaseBits)).first with
      | .canonicalResidue base => base.val < spec.modulus ∧ Nat.Coprime base.val spec.modulus) :
    accepts (phaseBits := phaseBits) spec store
      ((finalStore (phaseBits := phaseBits) spec store).read
      (Standard.resultRef (inputShape modulusWidth phaseBits) (outputShape phaseBits))) := by
  cases stored : store.read (inputRef modulusWidth phaseBits) with
  | product base bits =>
    cases base with
    | canonicalResidue base =>
      cases bits with
      | bits bits =>
        have good : base.val < spec.modulus ∧ Nat.Coprime base.val spec.modulus := by
          simpa only [stored, CShape.Value.first] using sourceGood
        let source : ClassicalAlgorithms.OrderRecovery.Input
            (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits) :=
          ⟨base, good.1, good.2, bits⟩
        refine ⟨source, stored, ?_⟩
        have result := nativeRecovery_retained_result ⟨spec⟩ source
          (inputRef modulusWidth phaseBits) Standard.resultKey
          (Standard.resultFresh (inputShape modulusWidth phaseBits)) store stored
        change (finalStore (phaseBits := phaseBits) spec store).read
          (Standard.resultRef (inputShape modulusWidth phaseBits) (outputShape phaseBits)) =
            encodeOutput (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder ⟨spec⟩ source)
            at result
        rw [result]
        cases ClassicalAlgorithms.OrderRecovery.recoverUnitOrder ⟨spec⟩ source <;> rfl

private theorem actual_resident {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (path : (code (phaseBits := phaseBits) spec).Path) :
    (code (phaseBits := phaseBits) spec).peakResidentSpace path ≤
      (problem (phaseBits := phaseBits) spec).resources.resident := by
  refine (nativeRecovery_retained_resident_le ⟨spec⟩ (inputRef modulusWidth phaseBits)
    Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)) path).trans ?_
  intro axis
  cases axis
  simp [problem, Standard.pre, SpacePool.ofShape, extraClassicalBits]
  omega

private theorem actual_auxiliary {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (path : (code (phaseBits := phaseBits) spec).Path) :
    (code (phaseBits := phaseBits) spec).peakAuxiliarySpace path ≤
      (problem (phaseBits := phaseBits) spec).resources.auxiliary := by
  refine (nativeRecovery_retained_auxiliary_le ⟨spec⟩ (inputRef modulusWidth phaseBits)
    Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)) path).trans ?_
  intro axis
  cases axis
  simp [problem, Standard.pre, SpacePool.ofShape, extraClassicalBits]
  omega

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def finalRecord {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (store : Execution.Store (Standard.pre (inputShape modulusWidth phaseBits))) :
    (algorithm (phaseBits := phaseBits) spec).run.Record :=
  (finalStore (phaseBits := phaseBits) spec store,
    (store, (retainedStep ⟨spec⟩ (inputRef modulusWidth phaseBits) Standard.resultKey
      (Standard.resultFresh (inputShape modulusWidth phaseBits)) store).2))

private theorem execution_eq_map {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) (Reference : Register)
    (state : ExecutionState
      (Execution.Store (Standard.pre (inputShape modulusWidth phaseBits)))
      (Register.prod (Standard.pre (inputShape modulusWidth phaseBits)).register Reference)) :
    (algorithm (phaseBits := phaseBits) spec).run.execute Reference state =
      state.mapClassical (finalRecord (phaseBits := phaseBits) spec) := by
  change (retainedCircuit ⟨spec⟩ (inputRef modulusWidth phaseBits) Standard.resultKey
    (Standard.resultFresh (inputShape modulusWidth phaseBits))).execute Reference
      (state.mapClassical (fun store => (store, store))) = _
  rw [nativeRecovery_retained_execute]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  rfl

private theorem relational_distribution {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) {Reference : Register}
    (input : Execution.Input (Standard.pre (inputShape modulusWidth phaseBits)) Reference) :
    (algorithm (phaseBits := phaseBits) spec).relationalDistribution input =
      (input.state.toPMF input.normalized).map (fun store => (store,
        (finalStore (phaseBits := phaseBits) spec store).read
          (Standard.resultRef (inputShape modulusWidth phaseBits) (outputShape phaseBits)))) := by
  apply AlgorithmRun.relationalDistribution_eq_map_of_block_mass
    (algorithm (phaseBits := phaseBits) spec).run input (finalRecord (phaseBits := phaseBits) spec)
  intro record
  exact congrArg (fun state => (state.block record).mass)
    (execution_eq_map (phaseBits := phaseBits) spec Reference input.state)

private theorem success_probability {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) {Reference : Register}
    (input : Execution.Input (Standard.pre (inputShape modulusWidth phaseBits)) Reference)
    (inputValid : valid (phaseBits := phaseBits) spec input.localState) :
    (1 : ENNReal) ≤
      ((algorithm (phaseBits := phaseBits) spec).relationalDistribution input).toOuterMeasure
      {pair | accepts (phaseBits := phaseBits) spec pair.1 pair.2} := by
  rw [relational_distribution]
  apply le_of_eq
  symm
  apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
  intro pair supported
  obtain ⟨store, inputSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have localSupported : 0 < (input.localState.block store).mass := by
    rw [Execution.Input.localState_block_mass]
    exact (ExecutionState.mem_support_toPMF_iff input.state input.normalized store).mp
      inputSupported
  exact finalStore_accepts (phaseBits := phaseBits) spec store (inputValid store localSupported)

/-- The named native algorithm meets the independent source contract for every raw sample. -/
public theorem main {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth) :
    (algorithm (phaseBits := phaseBits) spec).Solves (problem (phaseBits := phaseBits) spec) := by
  constructor
  · intro Reference input inputValid
    exact success_probability (phaseBits := phaseBits) spec input inputValid
  · intro _Reference _input _valid _requirement impossible
    cases impossible
  · intro Reference input _valid
    exact nativeRecovery_retained_borrowedRestored ⟨spec⟩ (inputRef modulusWidth phaseBits)
      Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)) Reference
      (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact nativeRecovery_retained_pool_le ⟨spec⟩ (inputRef modulusWidth phaseBits)
      Standard.resultKey (Standard.resultFresh (inputShape modulusWidth phaseBits)) path
  · intro _Reference _input _valid path _supported
    exact actual_resident (phaseBits := phaseBits) spec path
  · intro _Reference _input _valid path _supported
    exact actual_auxiliary (phaseBits := phaseBits) spec path
  · intro _Reference _input _valid _path _supported
    trivial

end

end QuantumAlg.ClassicalEndpoints.Recovery.OrderRecovery
