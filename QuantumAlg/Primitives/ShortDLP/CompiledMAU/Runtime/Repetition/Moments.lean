/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.WeightedOutcome
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results.Laws
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Weighted reference observations of the actual repeated circuit

The induction follows the actual retained result, measured/reset/reloaded
round and recursive tail. Each round uses the parameter still read from the
same store. Its conditional reference kernel composes with the existing
independent vector PMF, preserving arbitrary earlier data and every reference
matrix coordinate. There is no assumption that earlier outcomes were
independent and no replacement execution process.

The seed and storage-separation premises describe the internal ready bank;
actual first preparation and the fresh measurement/result layout establish
them. The empty repetition is included.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma liftInput_product (m ell width : Nat) {ctx : RuntimeCtx .quantum}
    {left right : CShape} (first : CInputRef ctx left) (second : CInputRef ctx right)
    (count : Nat) :
    RuntimeResults.liftInput m ell width (.product first second) count =
      .product (RuntimeResults.liftInput m ell width first count)
        (RuntimeResults.liftInput m ell width second count) := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact induction
        (first.underRetained ctx.canonicalFreshKey
          (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)
        (second.underRetained ctx.canonicalFreshKey
          (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)

private lemma weighted_empty {Sample : Type} [Fintype Sample]
    (distribution : PMF Sample) (weight : List.Vector Sample 0 → ℂ) :
    (∑ samples : List.Vector Sample 0,
      ((PMF.independentReplicateVector distribution 0 samples).toReal : ℂ) * weight samples) =
      weight List.Vector.nil := by
  have collapse : (∑ samples : List.Vector Sample 0,
      ((PMF.independentReplicateVector distribution 0 samples).toReal : ℂ) * weight samples) =
      ((PMF.independentReplicateVector distribution 0 List.Vector.nil).toReal : ℂ) *
        weight List.Vector.nil := by
    apply Finset.sum_eq_single List.Vector.nil
    · intro other _ different
      exact False.elim (different (Subsingleton.elim _ _))
    · intro missing
      exact False.elim (missing (Finset.mem_univ _))
  exact collapse.trans (by
    simp only [PMF.independentReplicateVector, PMF.pure_apply_self,
      ENNReal.toReal_one, Complex.ofReal_one, one_mul])

/-- Finite joint weights of real repeated results follow the original independent vector PMF. -/
lemma shortDLP_runtimeRepetition_weighted_reference
    {parameterShape : CShape} (m ell width N : Nat)
    (generator target : parameterShape.Value → (ZMod N)ˣ) :
    ∀ (count : Nat) {previousShape : CShape} (ctx : RuntimeCtx .quantum)
      (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
      (parameter : CInputRef ctx parameterShape) (previous : CInputRef ctx previousShape)
      (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
      (_distinct : Function.Injective (fun index => (cells index).key))
      (_separate : ∀ index, (cells index).key ∉
        (CInputRef.product parameter previous).storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (RuntimeRound.model.HiddenState × History)),
      RuntimeRound.HasSeedBlocks m ell width sameWires N state →
      ∀ (weight : parameterShape.Value → previousShape.Value →
          (Fin count → (CShape.bits (RuntimeRound.resultBits m ell width)).Value) → ℂ)
        (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum
          ((code m ell width N generator target ctx sameWires parameter cells count).execute
            environment
            Reference state)
          (fun entry _ => weight
            (entry.1.read (RuntimeResults.liftInput m ell width parameter count))
            (entry.1.read (RuntimeResults.liftInput m ell width previous count))
            (entry.1.read (RuntimeResults.input m ell width ctx count)).get)
          leftRef rightRef =
        ExecutionState.referenceFiberSum state
          (fun entry _ => ∑ samples :
              List.Vector (Fin (RuntimeRound.resultBits m ell width) → Bool) count,
            ((PMF.independentReplicateVector
              ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
                (CompiledMAU.evolvedState m ell width N
                  (generator (entry.1.read parameter)) (target (entry.1.read parameter))))
              count samples).toReal : ℂ) *
                weight (entry.1.read parameter) (entry.1.read previous)
                  (fun index => .bits (samples.get index))) leftRef rightRef := by
  intro count
  induction count with
  | zero =>
      intro previousShape ctx sameWires parameter previous cells _distinct _separate
        Reference History _ state _seeded weight leftRef rightRef
      let initialWeight := fun store : Store ctx =>
        weight (store.read parameter) (store.read previous)
          (store.read (RuntimeResults.input m ell width ctx 0)).get
      have identityLaw :
          ExecutionState.referenceFiberSum
            ((Circuit.id (allowAllocation := true) (model := RuntimeRound.model) ctx).execute
              environment
              Reference state)
              (fun entry _ => initialWeight entry.1) leftRef rightRef =
            ExecutionState.referenceFiberSum state
              (fun entry _ => initialWeight entry.1) leftRef rightRef := by
        have executed := congrArg
          (fun output : State ctx Reference (RuntimeRound.model.HiddenState × (History × Unit)) =>
            ExecutionState.referenceFiberSum output
              (fun entry _ => initialWeight entry.1) leftRef rightRef)
          (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
            (model := RuntimeRound.model) Reference state)
        exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
          (fun entry _ => initialWeight entry.1) leftRef rightRef)
      refine identityLaw.trans ?_
      apply congrArg
        (fun observe : (Store ctx × (RuntimeRound.model.HiddenState × History)) →
            ctx.register.Index → ℂ =>
          ExecutionState.referenceFiberSum state observe leftRef rightRef)
      funext entry basis
      refine Eq.trans ?_ (weighted_empty _ _).symm
      apply congrArg (weight (entry.1.read parameter) (entry.1.read previous))
      funext index
      exact Fin.elim0 index
  | succ count induction =>
      intro previousShape ctx sameWires parameter previous cells distinct separate
        Reference History _ state seeded weight leftRef rightRef
      let bits := CShape.bits (RuntimeRound.resultBits m ell width)
      let next := RuntimeResults.next m ell width ctx
      let nextWires :=
        (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
      let nextParameter :=
        parameter.underRetained ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh
      let nextPrevious :=
        previous.underRetained ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh
      let nextCells := fun index =>
        (cells index).underRetained ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh
      let head := RuntimeResults.head m ell width ctx
      let previousWithHead := CInputRef.product nextPrevious (.storage head.toCStorageRef)
      let retain := Circuit.retain (model := RuntimeRound.model) ctx ctx.canonicalFreshKey bits
        ctx.canonicalFreshKey_fresh
      let round := RuntimeRound.code m ell width nextWires nextParameter N generator target
        nextCells head
      let tail := code m ell width N generator target next nextWires nextParameter nextCells count
      let retained := retain.execute environment Reference state
      let rounded := round.execute environment Reference retained
      let source := fun value : parameterShape.Value =>
        (ShortDLP.measurement (registerParameters m ell width)).outcomePMF
          (CompiledMAU.evolvedState m ell width N (generator value) (target value))
      let finalWeight := fun store : Store (RuntimeResults.context m ell width ctx (count + 1)) =>
        weight (store.read (RuntimeResults.liftInput m ell width parameter (count + 1)))
          (store.read (RuntimeResults.liftInput m ell width previous (count + 1)))
          (store.read (RuntimeResults.input m ell width ctx (count + 1))).get
      let tailWeight := fun parameterValue : parameterShape.Value =>
        fun earlier : (CShape.product previousShape bits).Value =>
          fun outcomes : Fin count → bits.Value =>
            weight parameterValue earlier.first (Fin.cons earlier.second outcomes)
      have nextSeparate : ∀ index, (nextCells index).key ∉
          (CInputRef.product nextParameter nextPrevious).storageKeys := by
        intro index
        exact (CInputRef.storageKeys_underRetained (.product parameter previous)
          ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh).symm ▸ separate index
      have headSeparate : head.key ∉
          (CInputRef.product nextParameter nextPrevious).storageKeys :=
        CInputRef.fresh_not_mem_storageKeys_underRetained (.product parameter previous)
          ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh
      have tailSeparate : ∀ index, (nextCells index).key ∉
          (CInputRef.product nextParameter previousWithHead).storageKeys := by
        intro index present
        change (cells index).key ∈ nextParameter.storageKeys ++
          (nextPrevious.storageKeys ++ [ctx.canonicalFreshKey]) at present
        rcases List.mem_append.mp present with parameterKey | rest
        · exact nextSeparate index (List.mem_append_left _ parameterKey)
        · rcases List.mem_append.mp rest with previousKey | freshKey
          · exact nextSeparate index (List.mem_append_right _ previousKey)
          · have live := CInputRef.storageKeys_subset_context
              (.storage (cells index).toCStorageRef) (List.mem_singleton.mpr rfl)
            exact ctx.canonicalFreshKey_fresh ((List.mem_singleton.mp freshKey) ▸ live)
      have retainedSeed := RuntimeRound.shortDLP_runtimeSeedBlocks_retain
        (environment := environment) m ell width sameWires N
        ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh state seeded
      have roundSeed := RuntimeRound.shortDLP_runtimeRound_seedBlocks
        (environment := environment) m ell width nextWires
        nextParameter N generator target nextCells head retained
      have tailLaw := induction next nextWires nextParameter previousWithHead nextCells distinct
        tailSeparate rounded roundSeed tailWeight leftRef rightRef
      have finalRead (store : Store (RuntimeResults.context m ell width ctx (count + 1))) :
          finalWeight store = tailWeight
            (store.read (RuntimeResults.liftInput m ell width nextParameter count))
            (store.read (RuntimeResults.liftInput m ell width previousWithHead count))
            (store.read (RuntimeResults.input m ell width next count)).get := by
        let tailStore : Store (RuntimeResults.context m ell width next count) := store
        have headRead := congrArg
          (fun input : CInputRef (RuntimeResults.context m ell width next count) bits =>
            tailStore.read input)
          (RuntimeResults.shortDLP_runtimeResults_lift_storage m ell width head count)
        have pairRead := congrArg
          (fun input : CInputRef (RuntimeResults.context m ell width next count)
              (.product previousShape bits) => tailStore.read input)
          (liftInput_product m ell width nextPrevious (.storage head.toCStorageRef) count)
        have pairValue := pairRead.trans (congrArg
          (fun value : bits.Value => CShape.Value.product
            (tailStore.read (RuntimeResults.liftInput m ell width nextPrevious count)) value)
          headRead)
        have expanded := congrArg
          (fun outcomes => weight
            (tailStore.read (RuntimeResults.liftInput m ell width nextParameter count))
            (tailStore.read (RuntimeResults.liftInput m ell width nextPrevious count)) outcomes)
          (congrArg CShape.Value.get
            (RuntimeResults.shortDLP_runtimeResults_read_succ m ell width ctx count store))
        exact expanded.trans (congrArg
          (fun earlier : (CShape.product previousShape bits).Value =>
            tailWeight
              (tailStore.read (RuntimeResults.liftInput m ell width nextParameter count))
              earlier (tailStore.read (RuntimeResults.input m ell width next count)).get)
          pairValue.symm)
      have sequences := (Circuit.referenceFiberSum_execute_seq (environment := environment)
        retain (.seq round tail) state
        finalWeight leftRef rightRef).trans
        (Circuit.referenceFiberSum_execute_seq (environment := environment)
          round tail retained finalWeight leftRef rightRef)
      refine sequences.trans (Eq.trans (b := ExecutionState.referenceFiberSum
        (tail.execute environment Reference rounded)
        (fun entry _ => tailWeight
          (entry.1.read (RuntimeResults.liftInput m ell width nextParameter count))
          (entry.1.read (RuntimeResults.liftInput m ell width previousWithHead count))
          (entry.1.read (RuntimeResults.input m ell width next count)).get)
        leftRef rightRef) ?_ ?_)
      · exact congrArg
          (fun observe : (Store (RuntimeResults.context m ell width ctx (count + 1)) ×
              (RuntimeRound.model.HiddenState ×
                (((History × retain.Path) × round.Path) × tail.Path))) →
              (RuntimeResults.context m ell width ctx (count + 1)).register.Index → ℂ =>
            ExecutionState.referenceFiberSum (tail.execute environment Reference rounded)
              observe leftRef rightRef)
          (funext fun entry => funext fun _ => finalRead entry.1)
      · refine tailLaw.trans ?_
        let roundWeight := fun earlier : (CShape.product parameterShape previousShape).Value =>
          fun outcome : bits.Value =>
            ∑ samples : List.Vector (Fin (RuntimeRound.resultBits m ell width) → Bool) count,
              ((PMF.independentReplicateVector (source earlier.first) count samples).toReal : ℂ) *
                weight earlier.first earlier.second
                  (Fin.cons outcome (fun index => .bits (samples.get index)))
        have roundLaw := RuntimeRound.shortDLP_runtimeRound_weighted_outcome_reference
          (environment := environment)
            m ell width nextWires nextParameter nextPrevious N generator target nextCells head
          distinct nextSeparate headSeparate retained retainedSeed roundWeight leftRef rightRef
        refine roundLaw.trans ?_
        let earlierWeight := fun earlier : (CShape.product parameterShape previousShape).Value =>
          ∑ samples : List.Vector (Fin (RuntimeRound.resultBits m ell width) → Bool) (count + 1),
            ((PMF.independentReplicateVector
              (source earlier.first) (count + 1) samples).toReal : ℂ) *
              weight earlier.first earlier.second (fun index => .bits (samples.get index))
        have retainedLaw := Circuit.referenceFiberSum_execute_retain_input (environment :=
          environment)
          (gates := AlgorithmGate.model) (oracles := .empty)
          (operations := BitWord.model) (classicalOracles := .empty)
          (.product parameter previous) ctx.canonicalFreshKey bits ctx.canonicalFreshKey_fresh
          state earlierWeight leftRef rightRef
        refine Eq.trans ?_ retainedLaw
        apply congrArg
          (fun observe : (Store next × (RuntimeRound.model.HiddenState × (History × Unit))) →
            next.register.Index → ℂ =>
            ExecutionState.referenceFiberSum retained observe leftRef rightRef)
        funext entry basis
        have weights := PMF.independentReplicateVector_weighted_cons
          (source (entry.1.read nextParameter)) count
          (fun samples => weight (entry.1.read nextParameter) (entry.1.read nextPrevious)
            (fun index => .bits (samples.get index)))
        refine Eq.trans ?_ weights.symm
        apply Finset.sum_congr rfl
        intro first _
        apply congrArg
          (fun value : ℂ => ((source (entry.1.read nextParameter) first).toReal : ℂ) * value)
        apply Finset.sum_congr rfl
        intro samples _
        apply congrArg (fun value : ℂ =>
          ((PMF.independentReplicateVector
            (source (entry.1.read nextParameter)) count samples).toReal : ℂ) * value)
        apply congrArg (weight (entry.1.read nextParameter) (entry.1.read nextPrevious))
        funext index
        exact Fin.cases rfl (fun _ => rfl) index

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition
