/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Layout

/-!
# Actual second-pair reduction prefix

The actual refreshed Gram words feed the two arithmetic expressions, then
rounded division and the actual third-row reduction. Each chronological stage
consumes its predecessor's store and carries its own actual branch path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual second-direction quotient followed by the third-row reduction. -/
def divisionReductionInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (RoundedDiv.body refs.division32)
    (LatticeArithmetic.pointReduce (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct)

/-- Actual division path and the six dependent row-update instructions. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (divisionReductionInto refs).Path :=
  let divided := RoundedDiv.bodyStep refs.division32 store
  (LatticeArithmetic.pointStore (writeInput refs.division32.output)
    refs.basis.second refs.basis.third refs.reduceProduct divided.1,
      (divided.2, (((), ()), (((), ()), ((), ())))))

/-- Refresh the second third-row dot product before deriving both actual division inputs. -/
def refresh32InputsInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.basis.third refs.basis.second (refreshG32Refs refs))
    (LatticeSecondReductionInputs.secondReductionInputsInto (reductionInputs refs)
      refs.reductionInputs)

/-- Actual refreshed `g32` feeds both original Gram expressions. -/
def refresh32InputsStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refresh32InputsInto refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
    (refreshG32Refs refs) store
  (LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
    refs.reductionInputs refreshed,
      (((), (((), ()), ((), ()))), (((), ((), ())), ((), ((), ())))))

/-- Refresh both original dot products and derive the actual division inputs. -/
def refreshInputsInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.basis.second refs.basis.first (refreshG21Refs refs))
    (refresh32InputsInto refs)

/-- Actual chronological stores of both dot refreshes and the six arithmetic writes. -/
def refreshInputsStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshInputsInto refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first
    (refreshG21Refs refs) store
  let inputs := refresh32InputsStep refs refreshed
  (inputs.1, (((), (((), ()), ((), ()))), inputs.2))

/-- Execute the original second-direction reduction from the actual original store. -/
def secondPairPrefixInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (refreshInputsInto refs) (divisionReductionInto refs)

/-- Actual final store and complete recorded path of the five prefix stages. -/
def secondPairPrefixStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondPairPrefixInto refs).Path :=
  let inputs := refreshInputsStep refs store
  let reduced := divisionReductionStep refs inputs.1
  (reduced.1, (inputs.2, reduced.2))

/-- Full actual division and row reduction preserve histories and quantum-reference blocks. -/
theorem divisionReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (divisionReductionInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((divisionReductionStep refs entry.1).1,
        (entry.2, (divisionReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (RoundedDiv.body refs.division32)
    (LatticeArithmetic.pointReduce (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct)
    (RoundedDiv.bodyStep refs.division32)
    (fun store => (LatticeArithmetic.pointStore (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct store,
        (((), ()), (((), ()), ((), ())))))
    (RoundedDiv.body_execute refs.division32) (by
      intro Reference History _ state
      refine (LatticeArithmetic.pointReduce_execute _ _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Full actual refreshed `g32` and arithmetic execution compose without a parallel store model. -/
theorem refresh32InputsInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (refresh32InputsInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((refresh32InputsStep refs entry.1).1, (entry.2, (refresh32InputsStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto refs.basis.third refs.basis.second (refreshG32Refs refs))
    (LatticeSecondReductionInputs.secondReductionInputsInto (reductionInputs refs)
      refs.reductionInputs)
    (fun store => (LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
      (refreshG32Refs refs) store, ((), (((), ()), ((), ())))))
    (fun store => (LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
      refs.reductionInputs store, (((), ((), ())), ((), ((), ())))))
    (by
      intro Reference History _ state
      refine (LatticeDotRefresh.refreshInto_execute _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (by
      intro Reference History _ state
      refine (LatticeSecondReductionInputs.secondReductionInputsInto_execute _ _
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual preparation of the original numerator and denominator retains full state. -/
theorem refreshInputsInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (refreshInputsInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((refreshInputsStep refs entry.1).1, (entry.2, (refreshInputsStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto refs.basis.second refs.basis.first (refreshG21Refs refs))
    (refresh32InputsInto refs)
    (fun store => (LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first
      (refreshG21Refs refs) store, ((), (((), ()), ((), ())))))
    (refresh32InputsStep refs) (by
      intro Reference History _ state
      refine (LatticeDotRefresh.refreshInto_execute _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (refresh32InputsInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual quotient and row updates consume the actual refreshed Gram-derived inputs. -/
theorem secondPairPrefixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPairPrefixInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondPairPrefixStep refs entry.1).1,
        (entry.2, (secondPairPrefixStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (refreshInputsInto refs) (divisionReductionInto refs)
    (refreshInputsStep refs) (divisionReductionStep refs)
    (refreshInputsInto_execute refs) (divisionReductionInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
