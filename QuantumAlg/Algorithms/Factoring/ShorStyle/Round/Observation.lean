/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Selection.Fibers
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Actual complete-store observations of a Shor quantum round

The measured and packed store determines every result weight. Real reset and
reload preserve the entire reference operator of that store. On the seed
established by actual preparation, the selected gate program supplies its
own squared amplitudes. Thus the complete round transports a final-store
weight to the original store through its actual Born fibers, without any
supplied probability distribution or assumption about the external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Actual reset and reload keep every weighted packed-store reference fiber. -/
theorem round_referenceFiberSum (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code N sameWires parameter cells result).execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((selected N sameWires parameter).execute Reference state)
        (fun entry basis => weight (packedBasisStore N sameWires cells result entry.1 basis))
        leftRef rightRef := by
  let seed := (NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)
  let output := (code N sameWires parameter cells result).execute Reference state
  let evolved := (selected N sameWires parameter).execute Reference state
  refine (BasisSeeded.referenceFiberSum_seed seed output
    (round_seeded N sameWires parameter cells result state) weight leftRef rightRef).trans ?_
  calc
    _ = ∑ original : Store ctx, weight original *
        ExecutionState.referenceFiberSum evolved
          (fun entry basis =>
            if packedBasisStore N sameWires cells result entry.1 basis = original then 1 else 0)
          leftRef rightRef := by
      apply Finset.sum_congr rfl
      intro original _
      apply congrArg (fun coefficient : ℂ => weight original * coefficient)
      have actual := round_store_reference_entry N sameWires parameter cells result state
        original seed seed leftRef rightRef
      have atSeed : NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) seed = 1 :=
        (NormalizedVector.ket_apply _ _).trans (if_pos rfl)
      exact actual.trans (by rw [atSeed, one_mul, star_one, mul_one])
    _ = _ := ExecutionState.referenceFiberSum_observation_fibers evolved
      (fun entry basis => packedBasisStore N sameWires cells result entry.1 basis)
      weight leftRef rightRef

/-- The prepared bank transports the real final-store weight through its selected amplitudes. -/
theorem round_referenceFiberSum_seeded
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code N sameWires parameter cells result).execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ basis : ctx.register.Index,
          weight (packedBasisStore N sameWires cells result entry.1 basis) *
            (((‖(NativeQuantum.program (entry.1.read parameter)).applyNormalized
              (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
                (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires basis)‖ ^ 2 :
                  ℝ) : ℂ))) leftRef rightRef := by
  let seed := (NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)
  let incomingWeight := fun original : Store ctx => ∑ basis : ctx.register.Index,
    weight (packedBasisStore N sameWires cells result original basis) *
      (((‖(NativeQuantum.program (original.read parameter)).applyNormalized
        (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
          (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires basis)‖ ^ 2 :
            ℝ) : ℂ))
  refine (round_referenceFiberSum N sameWires parameter cells result state weight
    leftRef rightRef).trans ((selected_reference_fiber N sameWires parameter state seeded
      (fun original basis => weight (packedBasisStore N sameWires cells result original basis))
      leftRef rightRef).trans ?_)
  refine Eq.trans ?_ (BasisSeeded.referenceFiberSum_seed seed state seeded
    incomingWeight leftRef rightRef).symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  dsimp only [incomingWeight]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro basis _
  ring

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
