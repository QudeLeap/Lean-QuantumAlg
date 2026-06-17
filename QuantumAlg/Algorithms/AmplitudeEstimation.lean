/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.QPE
public import QuantumAlg.Primitives.AmplitudeAmplification

/-!
# Amplitude estimation (exact, dyadic eigenphase)

Amplitude estimation reads the unknown good-state amplitude of an amplitude-
amplification instance by running quantum phase estimation on the amplification
operator [Lin22]. In the good/bad-plane model
(`QuantumAlg.Primitives.AmplitudeAmplification`) one amplification iterate is a
rotation by `2θ`, where the initial good-state probability is `sin² θ`
[dW19, qcnotes.tex:2954]. As a planar rotation by `2θ`, the amplification
operator has eigenphases `±θ/π` (eigenvalues `e^{±2iθ}`); phase estimation reads
that eigenphase, and the amplitude is recovered as `sin²(π · eigenphase)`.

This module formalizes the **exact** regime, where the eigenphase is the dyadic
rational `θ/π = j / 2^t` for some `j : Fin (2^t)`, i.e. `θ = π · j / 2^t`. Two
proved facts compose, with phase estimation entering only through its decoupled
interface (`QuantumAlg.qpe_correct`):

- phase estimation reads out `|j⟩` from the eigenphase superposition; and
- the estimate `sin²(π · j / 2^t)` computed from the outcome `j` equals the true
  good-state probability `sin² θ` of the amplitude-amplification instance,
  reusing `QuantumAlg.amplitudeAmplificationState_good_probability`.

The construction of the reflection operators whose product realizes the planar
rotation, and the non-exact regime (where `θ/π` is not dyadic and continued-
fraction / confidence-interval recovery is needed), are out of scope here.

## Main results

- `QuantumAlg.amplitude_estimation_exact` — exact amplitude estimation: phase
  estimation of the dyadic eigenphase `θ/π = j/2^t` reads out `|j⟩`, and
  `sin²(π · j/2^t)` recovers the good-state probability `sin² θ`.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- **Exact amplitude estimation.** Let an amplitude-amplification instance have
initial angle `θ` whose corresponding eigenphase `θ/π` is the dyadic rational
`j / 2^t` (equivalently `θ = π · j / 2^t`). Then:

1. exact quantum phase estimation reads out `|j⟩` from the eigenphase
   superposition (`QuantumAlg.qpe_correct`); and
2. the amplitude estimate `sin²(π · j / 2^t)` formed from the outcome `j` equals
   the true good-state probability `sin² θ` of the instance, via
   `QuantumAlg.amplitudeAmplificationState_good_probability`.

This is the decoupled correctness statement: phase estimation enters only
through its proved interface, and the eigenphase/angle relation is taken as the
hypothesis `hθ` [Lin22]. -/
theorem amplitude_estimation_exact (t : ℕ) (j : Fin (2 ^ t)) (θ : ℝ)
    (hθ : θ = Real.pi * (j.val : ℝ) / (2 : ℝ) ^ t) :
    Gate.apply (invQFT t) (phaseState t ((j.val : ℝ) / (2 : ℝ) ^ t)) = ket j
      ∧ PureState.probOutcome (amplitudeAmplificationState θ 0) (1 : Fin (2 ^ 1))
          = Real.sin (Real.pi * (j.val : ℝ) / (2 : ℝ) ^ t) ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact qpe_correct t j _ rfl
  · rw [amplitudeAmplificationState_good_probability]
    have hang : amplitudeAmplificationAngle θ 0 = θ := by
      unfold amplitudeAmplificationAngle; push_cast; ring
    rw [hang, hθ]

end

end QuantumAlg
