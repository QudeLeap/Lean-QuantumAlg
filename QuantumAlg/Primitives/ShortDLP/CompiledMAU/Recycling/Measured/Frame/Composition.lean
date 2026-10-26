/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
import all QuantumAlg.Core.Execution.Reference.Kernel
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing

/-!
# Chronological complete-parent kernels on the same actual measured bank

Every component reads the actual preceding unnormalized posterior. Its
proved parent-Store/reference kernel is composed in that same native circuit
order, and actual reset/reload establishes the successor seed
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ParentSequenceCtx := context base noQuantum m ell width

/-- Real chronological members compose their proved complete-parent/reference kernels. -/
lemma measuredForRange_parent_referenceFiberSum (count : Nat)
    (body : Fin count → Circuit model (ParentSequenceCtx base noQuantum m ell width)
      (ParentSequenceCtx base noQuantum m ell width))
    (environment : model.Environment)
    (seed : (ParentSequenceCtx base noQuantum m ell width).register.Index)
    (kernels : Fin count → (Store base → ℂ) → Store base → ℂ)
    (seededAfter : ∀ index {Reference : Register} {History : Type} [Fintype History]
      (state : State (ParentSequenceCtx base noQuantum m ell width) Reference
        (model.HiddenState × History)),
      BasisSeeded.Holds seed ((body index).execute environment Reference state))
    (equations : ∀ index {Reference : Register} {History : Type} [Fintype History]
      (state : State (ParentSequenceCtx base noQuantum m ell width) Reference
        (model.HiddenState × History)),
      BasisSeeded.Holds seed state → ∀ (weight : Store base → ℂ)
        (left right : Reference.Index),
      ExecutionState.referenceFiberSum ((body index).execute environment Reference state)
          (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) left right =
        ExecutionState.referenceFiberSum state
          (fun entry _ => kernels index weight (parentStore base noQuantum m ell width entry.1))
          left right)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ParentSequenceCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state)
    (weight : Store base → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Circuit.forRange count body).execute environment Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => Circuit.forRangeReferenceKernel count kernels weight
          (parentStore base noQuantum m ell width entry.1)) left right := by
  induction count generalizing History with
  | zero =>
      rw [Circuit.forRange, Circuit.execute_id_mapClassical (model := model)]
      exact ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) left right
  | succ count ih =>
      refine (Circuit.referenceFiberSum_execute_seq (body 0)
        (Circuit.forRange count (fun index => body index.succ)) environment state
        (fun stored => weight (parentStore base noQuantum m ell width stored)) left right).trans ?_
      refine (ih (fun index => body index.succ) (fun index => kernels index.succ)
        (fun index => seededAfter index.succ) (fun index => equations index.succ)
        ((body 0).execute environment Reference state) (seededAfter 0 state)).trans ?_
      exact equations 0 state seeded
        (Circuit.forRangeReferenceKernel count (fun index => kernels index.succ) weight) left right

/-- Actual repeated reset/reload preserves its internal seed, including empty tails. -/
lemma measuredForRange_seeded (count : Nat)
    (body : Fin count → Circuit model (ParentSequenceCtx base noQuantum m ell width)
      (ParentSequenceCtx base noQuantum m ell width))
    (environment : model.Environment)
    (seed : (ParentSequenceCtx base noQuantum m ell width).register.Index)
    (seededAfter : ∀ index {Reference : Register} {History : Type} [Fintype History]
      (state : State (ParentSequenceCtx base noQuantum m ell width) Reference
        (model.HiddenState × History)),
      BasisSeeded.Holds seed ((body index).execute environment Reference state))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ParentSequenceCtx base noQuantum m ell width) Reference
      (model.HiddenState × History)) (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed
      ((Circuit.forRange count body).execute environment Reference state) := by
  induction count generalizing History with
  | zero =>
      rw [Circuit.forRange, Circuit.execute_id_mapClassical (model := model)]
      exact BasisSeeded.mapStore seed state seeded id
        (fun entry => (entry.2.1, (entry.2.2, ())))
  | succ count ih =>
      exact BasisSeeded.seq (environment := environment) (body 0)
        (Circuit.forRange count (fun index => body index.succ)) seed state
        (ih (fun index => body index.succ) (fun index => seededAfter index.succ)
          ((body 0).execute environment Reference state) (seededAfter 0 state))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
