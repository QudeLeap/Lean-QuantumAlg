/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence

/-!
# Actual sequential sampling beside the original seven persistent cells

The existing native placement keeps the original seven keys, roles and
shapes. Its sequence law preserves the complete state and original paired
path, rather than asserting equality of the two different circuit trees.
The existing restart and selected-seed contracts belong to the same placed
child in the companion restart module.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

variable {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}

/-- The original seven-cell caller retains the complete ordered native sequence. -/
def candidateCheck_sampleUnderPersistent_seqOperationalEquiv
    (first second : Circuit model ctx ctx false) (width scalarWidth : Nat) :
    Circuit.OperationalEquiv
      (sampleUnderPersistent (first.seq second) width scalarWidth)
      ((sampleUnderPersistent first width scalarWidth).seq
        (sampleUnderPersistent second width scalarWidth)) :=
  Circuit.embed_seqOperationalEquiv (persistentEmbedding ctx width scalarWidth) first second

/-- Every caller Store, service, reference and old history agrees on the same paired path. -/
lemma candidateCheck_sampleUnderPersistent_execute_seq
    (first second : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) :
    (sampleUnderPersistent (first.seq second) width scalarWidth).execute environment Reference
      state =
      ((sampleUnderPersistent first width scalarWidth).seq
        (sampleUnderPersistent second width scalarWidth)).execute environment Reference state :=
  Circuit.execute_embed_seq (persistentEmbedding ctx width scalarWidth) first second
    environment Reference state

/-- Exact resident accounting includes all seven original shapes throughout the sequence. -/
lemma candidateCheck_sampleUnderPersistent_seq_resident
    (first second : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (path : (first.seq second).Path) :
    (sampleUnderPersistent (first.seq second) width scalarWidth).peakResidentSpace path =
      persistentCellSpace model.kind width scalarWidth + ctx.residentSpace :=
  (candidateCheck_sampleUnderPersistent_resident (first.seq second) width scalarWidth path).trans
    (persistentCtx_residentSpace ctx width scalarWidth)

/-- The same seven retained roles remain in the exact auxiliary-space charge. -/
lemma candidateCheck_sampleUnderPersistent_seq_auxiliary
    (first second : Circuit model ctx ctx false) (width scalarWidth : Nat)
    (path : (first.seq second).Path) :
    (sampleUnderPersistent (first.seq second) width scalarWidth).peakAuxiliarySpace path =
      persistentCellSpace model.kind width scalarWidth + ctx.auxiliarySpace :=
  (candidateCheck_sampleUnderPersistent_auxiliary (first.seq second) width scalarWidth path).trans
    (persistentCtx_auxiliarySpace ctx width scalarWidth)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
