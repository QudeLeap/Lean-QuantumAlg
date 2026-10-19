/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Control
import all QuantumAlg.Core.Execution.Circuit.Reference
import all QuantumAlg.Core.Execution.Circuit.Allocation
import all QuantumAlg.Core.Execution.Composition.ClassicalTag.Parallel

/-!
# Complete classical spectator tags for fixed-context circuit execution

Every diagonal slice of an arbitrary external tag evolves exactly as the
corresponding classical history record. This is proved from the actual
instruction syntax, including nested physical embeddings and disjoint
parallel composition. The complete store, persistent service state, original
reference and actual execution path are retained. No conditional admission,
product-state premise or normalization of an individual slice is needed.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

private lemma execute_decodeReferenceTag_of_fixed
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation) (environment : model.Environment)
    (fixed : allowAllocation = false)
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State pre (Tag.prod Reference) (model.HiddenState × H)) :
    code.execute environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag (code.execute environment (Tag.prod Reference) state) := by
  induction code generalizing Reference Tag H with
  | id => exact id_decodeReferenceTag environment state
  | classical application => exact classical_decodeReferenceTag environment application state
  | classicalQuery application =>
      exact classicalQuery_decodeReferenceTag environment application state
  | unitary program => exact unitary_decodeReferenceTag environment program state
  | measureZ wire output => exact measureZ_decodeReferenceTag environment wire output state
  | retain | prepareZero | workspace => cases fixed
  | seq first second firstIH secondIH =>
      cases fixed
      cases first.fixed_endpoints
      cases second.fixed_endpoints
      exact sequence_tagNatural
        (fun Reference {_} _ original => interpret first environment Reference original)
        (fun Reference {_} _ original => interpret second environment Reference original)
        (fun {_ _ _} _ original => firstIH environment rfl original)
        (fun {_ _ _} _ original => secondIH environment rfl original)
        (fun Reference {_ _} _ _ original update =>
          second.execute_mapHistory environment Reference original update) state
  | branch input body bodyIH =>
      exact branch_decodeReferenceTag environment input body
        (fun value {_ _ _} _ original => bodyIH value environment fixed original) state
  | iterate count body bodyIH =>
      exact iterate_decodeReferenceTag environment body
        (fun {_ _ _} _ original => bodyIH environment fixed original) count state
  | embed placement body bodyIH =>
      exact embedPreserving_tagNatural placement
        (fun Reference {_} _ original => interpret body environment Reference original)
        (fun {_ _ _} _ original => bodyIH environment rfl original)
        (fun Reference {_ _} _ _ original update =>
          body.execute_mapHistory environment Reference original update)
        (fun {_ _} basis {_} _ original =>
          body.execute_referenceReindex environment basis original) state
  | parallelClassical join separate first second firstIH secondIH =>
      exact parallelPreserving_tagNatural join separate
        (fun Reference {_} _ original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference original)
        (fun Reference {_} _ original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference original)
        (fun {_ _ _} _ original => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ rfl original)
        (fun {_ _ _} _ original => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ rfl original)
        (fun Reference {_ _} _ _ original update =>
          first.execute_mapHistory
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
            Reference original update)
        (fun Reference {_ _} _ _ original update =>
          second.execute_mapHistory
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
            Reference original update)
        (fun {_ _} basis {_} _ original => first.execute_referenceReindex
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ basis original)
        (fun {_ _} basis {_} _ original => second.execute_referenceReindex
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ basis original)
        state
  | parallelQuantum join separate first second firstIH secondIH =>
      exact parallelPreserving_tagNatural join separate
        (fun Reference {_} _ original => interpret first
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ Reference original)
        (fun Reference {_} _ original => interpret second
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ Reference original)
        (fun {_ _ _} _ original => firstIH
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ rfl original)
        (fun {_ _ _} _ original => secondIH
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ rfl original)
        (fun Reference {_ _} _ _ original update =>
          first.execute_mapHistory
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩
            Reference original update)
        (fun Reference {_ _} _ _ original update =>
          second.execute_mapHistory
          ⟨environment.quantum, join.interpretationRight environment.classical⟩
            Reference original update)
        (fun {_ _} basis {_} _ original => first.execute_referenceReindex
          ⟨environment.quantum, join.interpretationLeft environment.classical⟩ basis original)
        (fun {_ _} basis {_} _ original => second.execute_referenceReindex
          ⟨environment.quantum, join.interpretationRight environment.classical⟩ basis original)
        state

/-- Every fixed-context circuit preserves the complete diagonal slices of any external tag. -/
lemma execute_decodeReferenceTag
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post false) (environment : model.Environment)
    {Reference Tag : Register} {H : Type} [Fintype H]
    (state : State pre (Tag.prod Reference) (model.HiddenState × H)) :
    code.execute environment Reference (State.decodeOracleTag state) =
      State.decodeExecutionTag (code.execute environment (Tag.prod Reference) state) :=
  execute_decodeReferenceTag_of_fixed code environment rfl state

end

end QuantumAlg.Circuit
