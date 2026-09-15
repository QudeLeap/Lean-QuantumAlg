/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Layout

/-!
# Actual shared modular setup from the retained sampler parameter
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual nominal packing of the original raw parameter base. -/
def packOp (refs : Refs ctx N) :
    ClassicalOp (.unsignedWord (modulusBits N)) (.canonicalResidue (modulusBits N)) ctx ctx :=
  .packCanonicalResidue (modulusBits N) ctx (parameterBaseInput refs) refs.generator

/-- Width-many literal native shifts materialize the original public modulus. -/
def modulusInto (refs : Refs ctx N) : Circuit ctx ctx :=
  ClassicalRoutines.ConstantWord.circuit refs.modulus N

/-- The original public target exponent is materialized by actual width-many native shifts. -/
def exponentInto (refs : Refs ctx N) : Circuit ctx ctx :=
  ClassicalRoutines.ConstantWord.circuit refs.targetExponent (RSA.targetExponent N)

/-- Actual shared modulus initialization and its complete store and instruction path. -/
def modulusStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (modulusInto refs).Path :=
  ClassicalRoutines.ConstantWord.foldStep refs.modulus
    (List.ofFn (ClassicalRoutines.ConstantWord.constantBits (modulusBits N + 1) N)) store

/-- Actual target exponent initialization and its complete store and instruction path. -/
def exponentStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (exponentInto refs).Path :=
  ClassicalRoutines.ConstantWord.foldStep refs.targetExponent
    (List.ofFn (ClassicalRoutines.ConstantWord.constantBits (modulusBits N) (RSA.targetExponent N)))
    store

/-- Actual base packing precedes original modulus and exponent materialization. -/
def prepareInto (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (.classical (packOp refs)) (.seq (modulusInto refs) (exponentInto refs))

/-- The actual three chronological shared-input updates and paths. -/
def prepareStep (refs : Refs ctx N) (store : Store ctx) : Store ctx × (prepareInto refs).Path :=
  let loaded := modulusStep refs (store.applyOp (packOp refs))
  let exponent := exponentStep refs loaded.1
  (exponent.1, ((), (loaded.2, exponent.2)))

/-- Actual shared target powering reads the real initialized generator and target exponent. -/
def powerInto (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  ClassicalRoutines.Modular.NativePower.into (modulusSpec input)
    (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower

/-- Complete actual target-power result and selected exponent-bit paths. -/
def powerStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (powerInto input refs).Path :=
  ClassicalRoutines.Modular.NativePower.intoStep (modulusSpec input)
    (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower store

/-- Initialize original shared inputs and execute actual target powering before candidate
scanning. -/
def setupInto (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (prepareInto refs) (powerInto input refs)

/-- Complete actual shared setup state and all four chronological component paths. -/
def setupStep (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (setupInto input refs).Path :=
  let prepared := prepareStep refs store
  let powered := powerStep input refs prepared.1
  (powered.1, (prepared.2, powered.2))

/-- Actual base packing and constant materialization retain all incoming histories and
references. -/
theorem prepareInto_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (prepareInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((prepareStep refs entry.1).1, (entry.2, (prepareStep refs entry.1).2))) := by
  have constants := Circuit.execute_seq_mapClassical (modulusInto refs) (exponentInto refs)
    (modulusStep refs) (exponentStep refs)
    (ClassicalRoutines.ConstantWord.constantWord_fold_execute refs.modulus _)
    (ClassicalRoutines.ConstantWord.constantWord_fold_execute refs.targetExponent _)
  refine (Circuit.execute_seq_mapClassical (.classical (packOp refs))
    (.seq (modulusInto refs) (exponentInto refs))
    (fun store => (store.applyOp (packOp refs), ()))
    (fun store =>
      let loaded := modulusStep refs store
      let exponent := exponentStep refs loaded.1
      (exponent.1, (loaded.2, exponent.2)))
    (fun Reference History _ state => by
      refine (Circuit.execute_classical_mapClassical (packOp refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun Reference History _ state => by
      refine (constants Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual full interpreter connects the retained base, initialized constants and target
power. -/
theorem setupInto_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (setupInto input refs).execute Reference state = state.mapClassical (fun entry =>
      ((setupStep input refs entry.1).1, (entry.2, (setupStep input refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (prepareInto refs) (powerInto input refs)
    (prepareStep refs) (powerStep input refs) (prepareInto_execute refs)
    (ClassicalRoutines.Modular.NativePower.nativePower_into_execute (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
