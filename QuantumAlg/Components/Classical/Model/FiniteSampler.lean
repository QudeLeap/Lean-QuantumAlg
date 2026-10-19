/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module


public import QuantumAlg.Core.Execution.Random.Selection
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Finite weighted sampling followed by a selected quantum word

This component is the compiled mechanism used by qDRIFT-style randomized
programs: one finite nonuniform distribution is a native classical operation,
its result is written to an actual cell, and that cell selects a quantum word
over the already-granted gate and oracle models. Each occurrence samples the
same stateless law independently. Stateful or externally supplied sampling is
represented instead by a granted `ClassicalOracleModel`.

The theorem below exposes the complete probability-weighted quantum/reference
mixture of the actual circuit. It does not assert a Hamiltonian-simulation
error bound or implement the rest of qDRIFT.
-/

namespace QuantumAlg.FiniteSampler

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A single native coordinate for one declared categorical sampler. -/
public inductive Coordinate where
  | sample
  deriving DecidableEq

/-- One fixed finite probability law as a classical native-operation model. -/
@[expose, implicit_reducible]
public def model (cardinality : ℕ+)
    (distribution : PMF (CShape.Value (.finite cardinality))) : ClassicalOpModel where
  Token := Unit
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  inputShape _ := .finite cardinality
  outputShape _ := .finite cardinality
  evaluate _ _ := distribution
  coordinate _ := .sample

variable {cardinality : ℕ+}
  (distribution : PMF (CShape.Value (.finite cardinality)))
  {gates : GateModel} {oracles : OracleModel} {services : ClassicalOracleModel}
  {environment :
    (ExecutionModel.quantum gates oracles (model cardinality distribution) services).Environment}
  {ctx : RuntimeCtx .quantum}

/-- Place the declared sampler at one real result cell. Its previous value is
the typed operand but does not affect the fixed law. -/
public def application (output : CWriteRef ctx (.finite cardinality)) :
    (model cardinality distribution).Application ctx where
  token := ()
  input := .storage output.toCStorageRef
  output := output

/-- Every occurrence uses the same law, independently of prior visible values. -/
public lemma application_distribution (output : CWriteRef ctx (.finite cardinality))
    (input : CShape.Value (.finite cardinality)) :
    (model cardinality distribution).evaluate
      (application distribution output).token input = distribution := rfl

/-- Two stateless occurrences assign the product of their declared weights;
this is the independence premise used when the circuit nodes are sequenced. -/
public lemma repeated_weight
    (firstInput secondInput firstOutcome secondOutcome :
      CShape.Value (.finite cardinality)) :
    ((model cardinality distribution).evaluate () firstInput firstOutcome).toReal *
        ((model cardinality distribution).evaluate () secondInput secondOutcome).toReal =
      (distribution firstOutcome).toReal * (distribution secondOutcome).toReal := rfl

/-- Sample one label and execute its granted quantum word. -/
@[expose, implicit_reducible]
public def code (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout) :
    Circuit (.quantum gates oracles (model cardinality distribution) services) ctx ctx :=
  sampleUnitary (services := services) (application distribution output) words

/-- The actual result is the full weighted mixture of all selected words,
including zero-probability labels and arbitrary external references. -/
public lemma code_quantumMarginal_matrix
    (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ((code (services := services) distribution output words).execute environment
      Reference state).quantumMarginal.matrix =
      ∑ entry : Store ctx × (services.HiddenState × History),
        ∑ outcome : CShape.Value (.finite cardinality),
          (distribution outcome).toReal •
            (let operator := UnitaryOperator.prodTensor ((words outcome).matrix environment.quantum)
              (1 : UnitaryOperator Reference)
             (operator : HilbertOperator (ctx.register.prod Reference)) *
               (state.block entry).matrix *
                 (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose) := by
  rw [code, sampleUnitary_quantumMarginal_matrix]
  apply Finset.sum_congr rfl
  intro entry _
  rw [application_distribution]
  apply Finset.sum_congr
  · ext outcome
    simp only [Finset.mem_univ]
  · intro outcome _
    rfl

/-- Every occurrence charges its sampling event before the selected word. -/
public lemma code_eventTrace (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (sample selected : CShape.Value (.finite cardinality)) :
    (code (services := services) distribution output words).eventTrace
      (sample, ⟨selected, ()⟩) =
      [.classicalOperation .sample] ++
        (words selected).eventTrace (model cardinality distribution) services :=
  sampleUnitary_eventTrace (application distribution output) words sample selected

/-- Two actual sampler occurrences use one result cell while retaining both
draws and the paths of both selected quantum words. -/
public abbrev twice (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout) :
    Circuit (.quantum gates oracles (model cardinality distribution) services) ctx ctx :=
  (code (services := services) distribution output words).seq
    (code (services := services) distribution output words)

/-- Both actual occurrences charge their own sampling event, in order, before
their respective selected quantum words. -/
public lemma twice_eventTrace (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    (firstSample firstSelected secondSample secondSelected :
      CShape.Value (.finite cardinality)) :
    (twice (services := services) distribution output words).eventTrace
        ((firstSample, ⟨firstSelected, ()⟩),
          (secondSample, ⟨secondSelected, ()⟩)) =
      ([.classicalOperation .sample] ++
        (words firstSelected).eventTrace (model cardinality distribution) services) ++
      ([.classicalOperation .sample] ++
        (words secondSelected).eventTrace (model cardinality distribution) services) := by
  change (code (services := services) distribution output words).eventTrace
      (firstSample, ⟨firstSelected, ()⟩) ++
    (code (services := services) distribution output words).eventTrace
      (secondSample, ⟨secondSelected, ()⟩) = _
  rw [code_eventTrace, code_eventTrace]

open scoped Classical in
/-- The second actual draw applies the same nonuniform law to every complete
block produced by the first selected quantum word. Thus the law is sampled
again on the executed program, including arbitrary reference correlations. -/
public lemma twice_execute (output : CWriteRef ctx (.finite cardinality))
    (words : CShape.Value (.finite cardinality) →
      UnitaryCircuit gates oracles ctx.quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (((code (services := services) distribution output words).seq
      (code (services := services) distribution output words)).execute
        environment Reference state) =
      let first := (code (services := services) distribution output words).execute environment
        Reference state
      (((kernelChoice first (fun entry =>
          (model cardinality distribution).evaluate
            (application distribution output).token
            (entry.1.read (application distribution output).input))).applyUnitary fun entry =>
          UnitaryOperator.prodTensor ((words entry.2).matrix environment.quantum)
            (1 : UnitaryOperator Reference)).mapClassical fun entry =>
          let nextPath : (code (services := services) distribution output words).Path :=
            (entry.2, ⟨entry.2, ()⟩)
          (entry.1.1.write (application distribution output).output entry.2,
            (entry.1.2.1, (entry.1.2.2.1,
              (entry.1.2.2.2, nextPath))))) := by
  rw [Circuit.execute_seq]
  unfold code
  rw [sampleUnitary_execute]
  simp only [State.mapHistory]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance)]
  rfl

end

end QuantumAlg.FiniteSampler
