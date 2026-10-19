/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.ResetReload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Selected

/-!
# Complete actual short-DLP round on every final store-reference block

The actual circuit's selected member, Z writes, packing, scoped reset and
reload compose to the exact formula below. Every final classical store has
the original local seed and the reference operator of its actual measured
fiber. No input normalization, zero-state promise, pure-state promise or
independence assumption is used in this complete round equation.

The conditional reference fiber is evaluated on the actual selected-member
state, so input quantum/classical/reference correlations are preserved in
the measurement result. The separate source-amplitude theorem identifies
these fibers with the original Born probabilities on the established seed.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma seq_store_marginal {ctx : RuntimeCtx .quantum}
    (first second : Circuit model ctx ctx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (original : Store ctx) :
    (ExecutionState.filterClassical ((Circuit.seq first second).execute environment Reference state)
      (fun entry => entry.1 = original)).quantumMarginal =
      (ExecutionState.filterClassical
        (second.execute environment Reference (first.execute environment Reference state))
        (fun entry => entry.1 = original)).quantumMarginal := by
  let predicate := fun store : Store ctx => store = original
  let nested := second.execute environment Reference (first.execute environment Reference state)
  let reassociate := fun history : model.HiddenState × ((History × first.Path) × second.Path) =>
    (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))
  have executed := congrArg
    (fun output : State ctx Reference
      (model.HiddenState × (History × (Circuit.seq first second).Path)) =>
      (output.filterClassical (fun entry => predicate entry.1)).quantumMarginal)
    (Circuit.execute_seq (environment := environment) first second state)
  have filtered := congrArg ExecutionState.quantumMarginal
    (ZReset.filter_mapHistory (ctx := ctx) (Reference := Reference)
      (History := model.HiddenState × ((History × first.Path) × second.Path))
      (Later := model.HiddenState × (History × (first.Path × second.Path)))
      nested reassociate predicate)
  exact executed.trans (filtered.trans
    (State.mapHistory_quantumMarginal
      (nested.filterClassical (fun entry => predicate entry.1)) reassociate))

private lemma filtered_store_reference {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : ctx.register.Index,
        ((state.mapClassical (fun entry => entry.1)).block original).matrix
          (basis, left) (basis, right) := by
  apply Finset.sum_congr rfl
  intro basis _
  change (∑ entry : Store ctx × History,
    (if entry.1 = original then state.block entry
      else DensityOperator.zero (Register.prod ctx.register Reference)).matrix)
        (basis, left) (basis, right) = _
  simp only [ExecutionState.mapClassical, Matrix.sum_apply, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix, Matrix.ite_apply, Matrix.zero_apply]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Every final store retains its actual measured reference fiber and the exact reloaded seed. -/
lemma shortDLP_runtimeRound_store_reference_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((code m ell width sameWires parameter N generator target cells result).execute environment
        Reference state) (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) left *
        ExecutionState.referenceFiberSum
          ((selected m ell width sameWires parameter N generator target).execute
            environment Reference state)
          (fun entry basis =>
            if packedBasisStore m ell width sameWires cells result entry.1 basis = original
            then 1 else 0) leftRef rightRef *
        star (NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) right) := by
  let member := selected m ell width sameWires parameter N generator target
  let measurement : Circuit model ctx ctx :=
    Circuit.measurementSequence (readouts m ell width sameWires cells)
  let pack := BitWord.instruction (execution := model) (packing m ell width cells result)
  let finish := resetReload m ell width sameWires N
  let evolved := member.execute environment Reference state
  let measured := measurement.execute environment Reference evolved
  let packed := pack.execute environment Reference measured
  have first := seq_store_marginal (environment := environment)
    member (.seq measurement (.seq pack finish)) state original
  have second := seq_store_marginal (environment := environment)
    measurement (.seq pack finish) evolved original
  have third := seq_store_marginal (environment := environment) pack finish measured original
  have composed := first.trans (second.trans third)
  refine (congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) composed).trans ?_
  refine (shortDLP_runtimeResetReload_store_entry m ell width sameWires N
    packed original left right leftRef rightRef).trans ?_
  apply congrArg (fun coefficient : ℂ =>
    NormalizedVector.ket (R := ctx.register)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) left * coefficient *
      star (NormalizedVector.ket (R := ctx.register)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) right))
  have grouped := seq_store_marginal (environment := environment)
    (Circuit.measurementSequence (readouts m ell width sameWires cells))
    (BitWord.instruction (packing m ell width cells result)) evolved original
  have entries := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      ∑ basis : ctx.register.Index, density.matrix (basis, leftRef) (basis, rightRef)) grouped
  exact entries.symm.trans
    ((filtered_store_reference
      ((measuredPacking m ell width sameWires cells result).execute environment Reference evolved)
      original leftRef rightRef).trans
      (shortDLP_runtimePacked_joint_reference_entry m ell width sameWires cells result
        evolved id original leftRef rightRef))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
