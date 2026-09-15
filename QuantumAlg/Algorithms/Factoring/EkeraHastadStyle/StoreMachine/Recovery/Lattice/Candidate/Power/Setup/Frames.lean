/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup

/-!
# Actual shared modular-setup caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Distinct original mutable names give actual structural separation of their cells. -/
theorem mutable_avoids (refs : Refs ctx N) (separation : Separation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (saved written : MutableCell)
    (sourceKey : source.key = mutableKey refs saved) (different : saved ≠ written) :
    mutableKey refs written ∉ (writeInput source).storageKeys := by
  change mutableKey refs written ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  intro equal
  exact different (separation.mutableKeyInjective equal.symm)

/-- Actual modulus loading preserves every other original structural input. -/
theorem modulusInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.modulus.key ∉ other.storageKeys) :
    (modulusStep refs store).1.read other = store.read other :=
  ClassicalRoutines.ConstantWord.constantWord_fold_read_other refs.modulus _ other avoids store

/-- Actual target-exponent loading preserves every other original structural input. -/
theorem exponentInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.targetExponent.key ∉ other.storageKeys) :
    (exponentStep refs store).1.read other = store.read other :=
  ClassicalRoutines.ConstantWord.constantWord_fold_read_other
    refs.targetExponent _ other avoids store

/-- The actual three preparation stages retain all reads outside their original destinations. -/
theorem prepareInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (generator : refs.generator.key ∉ other.storageKeys)
    (modulus : refs.modulus.key ∉ other.storageKeys)
    (exponent : refs.targetExponent.key ∉ other.storageKeys) :
    (prepareStep refs store).1.read other = store.read other := by
  exact (exponentInto_callerFrame refs _ other exponent).trans
    ((modulusInto_callerFrame refs _ other modulus).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (packOp refs) other generator))

/-- Actual target powering preserves all original inputs outside its visible result cell. -/
theorem powerInto_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.targetPower.key ∉ other.storageKeys) :
    (powerStep input refs store).1.read other = store.read other :=
  ClassicalRoutines.Modular.NativePower.nativePower_into_read_other (modulusSpec input)
    (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower store other avoids

/-- The full actual setup preserves every caller read outside the four original shared outputs. -/
theorem setupInto_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    CallerFrame refs store (setupStep input refs store).1 := by
  intro shape other avoids
  exact (powerInto_callerFrame input refs _ other (avoids .targetPower)).trans
    (prepareInto_callerFrame refs store other (avoids .generator) (avoids .modulus)
      (avoids .targetExponent))

/-- The retained sampler parameter is preserved by every actual shared-setup stage. -/
theorem setupInto_parameter_frame (input : Input N) (refs : Refs ctx N)
    (separation : Separation refs) (store : Store ctx) :
    (setupStep input refs store).1.read refs.parameter = store.read refs.parameter :=
  setupInto_callerFrame input refs store refs.parameter separation.parameterAvoidsMutable

/-- The actual stored parameter's first projection always is the original base input. -/
theorem parameterBaseInput_read (refs : Refs ctx N) (store : Store ctx) :
    store.read (parameterBaseInput refs) = (store.read refs.parameter).first := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
