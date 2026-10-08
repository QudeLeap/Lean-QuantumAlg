/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Frame

/-!
# Actual caller reads after scoped residue preparation

Every internal write is separated from existing caller references by the
eleven real fresh keys. After releasing those scopes, every original read
outside the supplied parameter output has its exact original value. This
includes the retained packed random sample used by the subsequent sampler.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution
open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual modulus load and complete scan leave every original caller read unchanged. -/
theorem samplerScan_read_original (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (store : Store (Layout.context ctx (modulusBits N))) :
    (Scan.step (model := model) N sample store).1.read (Layout.underRead other (modulusBits N)) =
      store.read (Layout.underRead other (modulusBits N)) := by
  have separate : ∀ key ∈ Proposal.slotKeys (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)),
      key ∉ (Layout.underRead other (modulusBits N)).storageKeys := by
    intro key present
    change key ∈ [(Layout.candidateCell ctx (modulusBits N)).key,
      (Layout.extendedCell ctx (modulusBits N)).key,
      (Layout.positiveCell ctx (modulusBits N)).key,
      (Layout.belowModulusCell ctx (modulusBits N)).key,
      (Layout.eligibleCell ctx (modulusBits N)).key,
      (Layout.availableCell ctx (modulusBits N)).key,
      (Layout.takeCell ctx (modulusBits N)).key,
      (Layout.acceptedCell ctx (modulusBits N)).key,
      (Layout.selectedCell ctx (modulusBits N)).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Layout.samplerLayout_original_free other 8
    · exact Layout.samplerLayout_original_free other 7
    · exact Layout.samplerLayout_original_free other 6
    · exact Layout.samplerLayout_original_free other 5
    · exact Layout.samplerLayout_original_free other 4
    · exact Layout.samplerLayout_original_free other 1
    · exact Layout.samplerLayout_original_free other 0
    · exact Layout.samplerLayout_original_free other 3
    · exact Layout.samplerLayout_original_free other 2
  exact (Proposal.proposalFold_read_other (model := model)
    (Layout.underRead sample (modulusBits N))
    (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
    (List.ofFn (fun proposal : Fin residueProposalCount => proposal))
    (Layout.underRead other (modulusBits N)) separate (Scan.loaderStep (model := model)
      N store).1).trans
      (ConstantWord.constantWord_fold_read_other (model := model)
    (Layout.modulusCell ctx (modulusBits N))
        (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N))
        (Layout.underRead other (modulusBits N)) (Layout.samplerLayout_original_free other 10)
        store)

/-- Every original read outside the actual parameter output survives the complete inner program. -/
theorem samplerInner_read_other (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (outputFree : output.key ∉ other.storageKeys)
    (store : Store (Layout.context ctx (modulusBits N))) :
    (innerStep (model := model)
      N sample output store).1.read (Layout.underRead other (modulusBits N)) =
      store.read (Layout.underRead other (modulusBits N)) := by
  have outputFree' : (Layout.underWrite output (modulusBits N)).key ∉
      (Layout.underRead other (modulusBits N)).storageKeys := by
    rw [Layout.samplerLayout_underRead_keys]
    exact outputFree
  exact (Decision.decision_read_other (model := model)
    (Layout.shared ctx (modulusBits N))
    (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
    (Layout.underWrite output (modulusBits N)) (Layout.underRead other (modulusBits N))
    (Layout.samplerLayout_original_free other 8) (Layout.samplerLayout_original_free other 2)
    (Layout.samplerLayout_original_free other 4) (Layout.samplerLayout_original_free other 7)
    (Layout.samplerLayout_original_free other 6) (Layout.samplerLayout_original_free other 9)
    outputFree' (Scan.step (model := model) N sample store).1).trans
      (samplerScan_read_original (model := model) N sample other store)

/-- Actual scope release preserves every complete original read outside the parameter cell. -/
theorem samplerProgram_read_other (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (outputFree : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step (model := model) N sample output store).1.read other = store.read other := by
  exact (Layout.samplerLayout_pop_read other (modulusBits N)
    (innerStep (model := model) N sample output (Layout.pushStore (modulusBits N) store)).1).trans
      ((samplerInner_read_other (model := model) N sample output other outputFree
        (Layout.pushStore (modulusBits N) store)).trans
        (Layout.samplerLayout_push_read other (modulusBits N) store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
