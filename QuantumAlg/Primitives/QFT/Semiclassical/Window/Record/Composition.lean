/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Lift

/-!
# Two actual recycled windows around a measured middle circuit

The middle premise is its full actual interpreter block equation, with its
true Store writes, measured Path and retained hidden/history/reference fibers.
Its allocation index is unrestricted, so actual lexical table construction and
release may remain present. The next Fourier feedback reads the middle's real
output Store. No unitary replacement, point-correctness premise or source row
is substituted for the middle circuit's execution.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits firstActive secondActive : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}
  {MiddleOutcome : Type} [Fintype MiddleOutcome]

/-- A component law about every block of the same actual middle interpreter. -/
def MiddleEquation
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (operator : (Reference : Register) → Store ctx → MiddleOutcome →
      HilbertOperator (ctx.register.prod Reference))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) result,
    ((middle.execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : MiddleOutcome,
        if Execution.Instrument.retainedRecord record original outcome = result then
          operator Reference original.1 outcome * (state.block original).matrix *
            (operator Reference original.1 outcome).conjTranspose else 0

def windowThenMiddle (ports : Ports ctx totalBits firstActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation) :=
  (liftedInverse (allowAllocation := allowAllocation) ports).seq middle

def windowThenMiddleRecord (ports : Ports ctx totalBits firstActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (store : Store ctx) (outcome : Bits firstActive × MiddleOutcome) :
    Store ctx × (windowThenMiddle ports middle).Path :=
  Execution.Instrument.sequenceRetainedRecord (liftedInverse ports) middle
    (inverseStoreRecord ports) record store outcome.1 outcome.2

def windowThenMiddleOperator (ports : Ports ctx totalBits firstActive)
    (operator : (Reference : Register) → Store ctx → MiddleOutcome →
      HilbertOperator (ctx.register.prod Reference))
    (Reference : Register) (store : Store ctx) (outcome : Bits firstActive × MiddleOutcome) :
    HilbertOperator (ctx.register.prod Reference) :=
  operator Reference
      (inverseStoreRecord (operations := operations) (services := services)
        ports store outcome.1).1 outcome.2 *
    sourceWindowKraus ports Reference store outcome.1

/-- The measured middle receives the first window's exact actual next Store. -/
lemma windowThenMiddle_record_matrix (ports : Ports ctx totalBits firstActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (operator : (Reference : Register) → Store ctx → MiddleOutcome →
      HilbertOperator (ctx.register.prod Reference))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (actualMiddle : MiddleEquation middle record operator environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (windowThenMiddle ports middle).Path))) :
    (((windowThenMiddle ports middle).execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Bits firstActive × MiddleOutcome,
          if Execution.Instrument.retainedRecord
              (windowThenMiddleRecord ports middle record) original outcome = result then
            windowThenMiddleOperator (operations := operations) (services := services)
              ports operator Reference original.1 outcome *
              (state.block original).matrix *
                (windowThenMiddleOperator (operations := operations) (services := services)
                  ports operator Reference original.1 outcome).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (liftedInverse (allowAllocation := allowAllocation) ports) middle
    (inverseStoreRecord (operations := operations) (services := services) ports) record
    (fun reference store outcome => sourceWindowKraus ports reference store outcome)
    operator environment
    (fun reference {_} _ input selected => by
      refine (window_liftedInverse_source_record_matrix ports environment reference
        input selected).trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      exact conditional_values _ _ _ _)
    actualMiddle Reference state result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro firstOutcome _
  apply Finset.sum_congr rfl
  intro middleOutcome _
  simp only [Execution.Instrument.retainedRecord, windowThenMiddleRecord,
    windowThenMiddleOperator]
  split_ifs <;> rfl

def betweenWindows (first : Ports ctx totalBits firstActive)
    (second : Ports ctx totalBits secondActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation) :=
  (windowThenMiddle first middle).seq (liftedInverse second)

def betweenWindowsRecord (first : Ports ctx totalBits firstActive)
    (second : Ports ctx totalBits secondActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (store : Store ctx) (outcome : (Bits firstActive × MiddleOutcome) × Bits secondActive) :
    Store ctx × (betweenWindows first second middle).Path :=
  Execution.Instrument.sequenceRetainedRecord
    (windowThenMiddle first middle) (liftedInverse second)
    (windowThenMiddleRecord first middle record) (inverseStoreRecord second)
    store outcome.1 outcome.2

/-- The second native Fourier row reads the real middle output, including every Store write. -/
def betweenWindowsOperator (first : Ports ctx totalBits firstActive)
    (second : Ports ctx totalBits secondActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (operator : (Reference : Register) → Store ctx → MiddleOutcome →
      HilbertOperator (ctx.register.prod Reference))
    (Reference : Register) (store : Store ctx)
    (outcome : (Bits firstActive × MiddleOutcome) × Bits secondActive) :
    HilbertOperator (ctx.register.prod Reference) :=
  sourceWindowKraus second Reference
      (windowThenMiddleRecord first middle record store outcome.1).1 outcome.2 *
    windowThenMiddleOperator (operations := operations) (services := services)
      first operator Reference store outcome.1

/-- Exact full actual two-window instrument, with a measured middle and both real record sets. -/
lemma betweenWindows_record_matrix (first : Ports ctx totalBits firstActive)
    (second : Ports ctx totalBits secondActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (record : Store ctx → MiddleOutcome → Store ctx × middle.Path)
    (operator : (Reference : Register) → Store ctx → MiddleOutcome →
      HilbertOperator (ctx.register.prod Reference))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (actualMiddle : MiddleEquation middle record operator environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (betweenWindows first second middle).Path))) :
    (((betweenWindows first second middle).execute environment Reference state).block
      result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ firstOutcome : Bits firstActive, ∑ middleOutcome : MiddleOutcome,
          ∑ secondOutcome : Bits secondActive,
            if Execution.Instrument.retainedRecord
                (betweenWindowsRecord first second middle record) original
                  ((firstOutcome, middleOutcome), secondOutcome) = result then
              betweenWindowsOperator first second middle record operator Reference original.1
                  ((firstOutcome, middleOutcome), secondOutcome) * (state.block original).matrix *
                (betweenWindowsOperator first second middle record operator Reference original.1
                  ((firstOutcome, middleOutcome), secondOutcome)).conjTranspose
            else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (windowThenMiddle first middle) (liftedInverse second)
    (windowThenMiddleRecord first middle record)
    (inverseStoreRecord (operations := operations) (services := services) second)
    (windowThenMiddleOperator (operations := operations) (services := services) first operator)
    (fun reference store outcome => sourceWindowKraus second reference store outcome)
    environment
    (windowThenMiddle_record_matrix first middle record operator environment actualMiddle)
    (fun reference {_} _ input selected => by
      refine (window_liftedInverse_source_record_matrix second environment reference
        input selected).trans ?_
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro outcome _
      exact conditional_values _ _ _ _)
    Reference state result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro firstOutcome _
  apply Finset.sum_congr rfl
  intro middleOutcome _
  apply Finset.sum_congr rfl
  intro secondOutcome _
  simp only [Execution.Instrument.retainedRecord, betweenWindowsRecord,
    betweenWindowsOperator]
  split_ifs <;> rfl

/-- Both real Fourier words and every paid middle operation remain in quantum time. -/
lemma betweenWindows_quantumTime (first : Ports ctx totalBits firstActive)
    (second : Ports ctx totalBits secondActive)
    (middle : Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx ctx allowAllocation)
    (firstPath : (inverseCode (operations := operations) (services := services) first).Path)
    (middlePath : middle.Path)
    (secondPath : (inverseCode (operations := operations) (services := services) second).Path) :
    (betweenWindows first second middle).quantumTime ((firstPath, middlePath), secondPath) =
      (inverseCode (operations := operations) (services := services) first).quantumTime firstPath +
        middle.quantumTime middlePath +
          (inverseCode (operations := operations) (services := services) second).quantumTime
            secondPath := by
  have prefixTime :
      ((liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) first).seq middle).quantumTime
          (firstPath, middlePath) =
        (inverseCode (operations := operations) (services := services) first).quantumTime
          firstPath + middle.quantumTime middlePath :=
    (Circuit.quantumTime_seq
      (model := .quantum AlgorithmGate.model .empty operations services)
      (liftedInverse (allowAllocation := allowAllocation) first) middle
      firstPath middlePath).trans
        (congrArg (fun duration => duration + middle.quantumTime middlePath)
          (window_liftedInverse_quantumTime (operations := operations) (services := services)
            (allowAllocation := allowAllocation) first firstPath))
  exact (Circuit.quantumTime_seq
    (model := .quantum AlgorithmGate.model .empty operations services)
    ((liftedInverse (allowAllocation := allowAllocation) first).seq middle)
    (liftedInverse second) (firstPath, middlePath) secondPath).trans
      (congrArg₂ Nat.add prefixTime
        (window_liftedInverse_quantumTime (operations := operations) (services := services)
          (allowAllocation := allowAllocation) second secondPath))

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
