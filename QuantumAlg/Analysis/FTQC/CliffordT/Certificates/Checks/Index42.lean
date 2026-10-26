/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word42Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word42State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step0 :
    word42Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word42State1 := by decide +kernel

private def word42Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word42State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step1 :
    word42Chunk1.foldl (fun acc a => a.applyPacked acc)
      word42State1 = word42State2 := by decide +kernel

private def word42Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word42State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step2 :
    word42Chunk2.foldl (fun acc a => a.applyPacked acc)
      word42State2 = word42State3 := by decide +kernel

private def word42Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word42State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step3 :
    word42Chunk3.foldl (fun acc a => a.applyPacked acc)
      word42State3 = word42State4 := by decide +kernel

private def word42Chunk4 : List Letter := [.h, .s, .h, .s, .s, .h, .s, .s]
private def word42State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step4 :
    word42Chunk4.foldl (fun acc a => a.applyPacked acc)
      word42State4 = word42State5 := by decide +kernel

private def word42Chunk5 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word42State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word42Step5 :
    word42Chunk5.foldl (fun acc a => a.applyPacked acc)
      word42State5 = word42State6 := by decide +kernel

private def word42Chunk6 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word42State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word42Step6 :
    word42Chunk6.foldl (fun acc a => a.applyPacked acc)
      word42State6 = word42State7 := by decide +kernel

private def word42Chunk7 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word42State8 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word42Step7 :
    word42Chunk7.foldl (fun acc a => a.applyPacked acc)
      word42State7 = word42State8 := by decide +kernel

private def word42Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word42Step8 :
    word42Chunk8.foldl (fun acc a => a.applyPacked acc)
      word42State8 = word42State9 := by decide +kernel

private def word42Chunk9 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word42State10 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((21 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word42Step9 :
    word42Chunk9.foldl (fun acc a => a.applyPacked acc)
      word42State9 = word42State10 := by decide +kernel

private def word42Chunk10 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word42State11 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 6),
        ((27 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 6),
        ((-27 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word42Step10 :
    word42Chunk10.foldl (fun acc a => a.applyPacked acc)
      word42State10 = word42State11 := by decide +kernel

private def word42Chunk11 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word42State12 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 6),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-35 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((35 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((65 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word42Step11 :
    word42Chunk11.foldl (fun acc a => a.applyPacked acc)
      word42State11 = word42State12 := by decide +kernel

private def word42Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word42State13 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((57 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 7),
        ((47 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-57 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word42Step12 :
    word42Chunk12.foldl (fun acc a => a.applyPacked acc)
      word42State12 = word42State13 := by decide +kernel

private def word42Chunk13 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word42State14 : PackedMat2 :=
    ⟨⟨⟨((95 : Dyadic) * half ^ 8),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((151 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((113 : Dyadic) * half ^ 8),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((69 : Dyadic) * half ^ 8),
        ((51 : Dyadic) * half ^ 8)⟩,
       ⟨((-67 : Dyadic) * half ^ 8),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((73 : Dyadic) * half ^ 8),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((-79 : Dyadic) * half ^ 8),
        ((123 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word42Step13 :
    word42Chunk13.foldl (fun acc a => a.applyPacked acc)
      word42State13 = word42State14 := by decide +kernel

private def word42Chunk14 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word42State15 : PackedMat2 :=
    ⟨⟨⟨((325 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 8)⟩,
       ⟨((-63 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((89 : Dyadic) * half ^ 9),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-37 : Dyadic) * half ^ 9),
        ((257 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-89 : Dyadic) * half ^ 9),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-37 : Dyadic) * half ^ 9),
        ((257 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((325 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 8)⟩,
       ⟨((63 : Dyadic) * half ^ 9),
        ((-51 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word42Step14 :
    word42Chunk14.foldl (fun acc a => a.applyPacked acc)
      word42State14 = word42State15 := by decide +kernel

private def word42Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word42State16 : PackedMat2 :=
    ⟨⟨⟨((105 : Dyadic) * half ^ 8),
        ((75 : Dyadic) * half ^ 8)⟩,
       ⟨((109 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 7),
        ((-299 : Dyadic) * half ^ 10)⟩,
       ⟨((157 : Dyadic) * half ^ 8),
        ((-183 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-157 : Dyadic) * half ^ 8),
        ((183 : Dyadic) * half ^ 10)⟩,
       ⟨((-7 : Dyadic) * half ^ 7),
        ((299 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((109 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 9)⟩,
       ⟨((105 : Dyadic) * half ^ 8),
        ((75 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word42Step15 :
    word42Chunk15.foldl (fun acc a => a.applyPacked acc)
      word42State15 = word42State16 := by decide +kernel

private def word42Chunk16 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word42State17 : PackedMat2 :=
    ⟨⟨⟨((59 : Dyadic) * half ^ 10),
        ((-567 : Dyadic) * half ^ 11)⟩,
       ⟨((161 : Dyadic) * half ^ 9),
        ((879 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-237 : Dyadic) * half ^ 10),
        ((515 : Dyadic) * half ^ 11)⟩,
       ⟨((-195 : Dyadic) * half ^ 9),
        ((327 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((421 : Dyadic) * half ^ 10),
        ((-627 : Dyadic) * half ^ 11)⟩,
       ⟨((47 : Dyadic) * half ^ 9),
        ((153 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 8),
        ((-381 : Dyadic) * half ^ 11)⟩,
       ⟨((723 : Dyadic) * half ^ 10),
        ((263 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word42Step16 :
    word42Chunk16.foldl (fun acc a => a.applyPacked acc)
      word42State16 = word42State17 := by decide +kernel

private def word42Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word42State18 : PackedMat2 :=
    ⟨⟨⟨((-1341 : Dyadic) * half ^ 11),
        ((-15 : Dyadic) * half ^ 10)⟩,
       ⟨((283 : Dyadic) * half ^ 11),
        ((-87 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((331 : Dyadic) * half ^ 10),
        ((-61 : Dyadic) * half ^ 11)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((55 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-159 : Dyadic) * half ^ 11),
        ((-779 : Dyadic) * half ^ 11)⟩,
       ⟨((281 : Dyadic) * half ^ 11),
        ((117 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-363 : Dyadic) * half ^ 10),
        ((-529 : Dyadic) * half ^ 11)⟩,
       ⟨((333 : Dyadic) * half ^ 10),
        ((-203 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word42Step17 :
    word42Chunk17.foldl (fun acc a => a.applyPacked acc)
      word42State17 = word42State18 := by decide +kernel

private def word42Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word42State19 : PackedMat2 :=
    ⟨⟨⟨((-1239 : Dyadic) * half ^ 12),
        ((-865 : Dyadic) * half ^ 12)⟩,
       ⟨((-3395 : Dyadic) * half ^ 12),
        ((157 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-735 : Dyadic) * half ^ 12),
        ((-127 : Dyadic) * half ^ 11)⟩,
       ⟨((-239 : Dyadic) * half ^ 12),
        ((805 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-735 : Dyadic) * half ^ 12),
        ((-127 : Dyadic) * half ^ 11)⟩,
       ⟨((239 : Dyadic) * half ^ 12),
        ((-805 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1239 : Dyadic) * half ^ 12),
        ((865 : Dyadic) * half ^ 12)⟩,
       ⟨((-3395 : Dyadic) * half ^ 12),
        ((157 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word42Step18 :
    word42Chunk18.foldl (fun acc a => a.applyPacked acc)
      word42State18 = word42State19 := by decide +kernel

private def word42Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word42State20 : PackedMat2 :=
    ⟨⟨⟨((277 : Dyadic) * half ^ 10),
        ((-255 : Dyadic) * half ^ 10)⟩,
       ⟨((-835 : Dyadic) * half ^ 12),
        ((-1127 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((141 : Dyadic) * half ^ 12),
        ((777 : Dyadic) * half ^ 13)⟩,
       ⟨((1027 : Dyadic) * half ^ 12),
        ((-1571 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-587 : Dyadic) * half ^ 11),
        ((443 : Dyadic) * half ^ 12)⟩,
       ⟨((-397 : Dyadic) * half ^ 12),
        ((73 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((617 : Dyadic) * half ^ 11),
        ((1943 : Dyadic) * half ^ 13)⟩,
       ⟨((1637 : Dyadic) * half ^ 11),
        ((-273 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word42Step19 :
    word42Chunk19.foldl (fun acc a => a.applyPacked acc)
      word42State19 = word42State20 := by decide +kernel

private def word42Chunk20 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word42State21 : PackedMat2 :=
    ⟨⟨⟨((-467 : Dyadic) * half ^ 12),
        ((1573 : Dyadic) * half ^ 14)⟩,
       ⟨((-2135 : Dyadic) * half ^ 13),
        ((-7605 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4557 : Dyadic) * half ^ 13),
        ((3789 : Dyadic) * half ^ 14)⟩,
       ⟨((307 : Dyadic) * half ^ 11),
        ((2035 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-91 : Dyadic) * half ^ 8),
        ((3329 : Dyadic) * half ^ 14)⟩,
       ⟨((-877 : Dyadic) * half ^ 13),
        ((5785 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-377 : Dyadic) * half ^ 10),
        ((-3069 : Dyadic) * half ^ 14)⟩,
       ⟨((4589 : Dyadic) * half ^ 13),
        ((1201 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word42Step20 :
    word42Chunk20.foldl (fun acc a => a.applyPacked acc)
      word42State20 = word42State21 := by decide +kernel

private def word42Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word42State22 : PackedMat2 :=
    ⟨⟨⟨((-659 : Dyadic) * half ^ 13),
        ((13731 : Dyadic) * half ^ 15)⟩,
       ⟨((-201 : Dyadic) * half ^ 14),
        ((-13239 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-8281 : Dyadic) * half ^ 14),
        ((-2085 : Dyadic) * half ^ 15)⟩,
       ⟨((1863 : Dyadic) * half ^ 13),
        ((-491 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1863 : Dyadic) * half ^ 13),
        ((-491 : Dyadic) * half ^ 15)⟩,
       ⟨((-8281 : Dyadic) * half ^ 14),
        ((-2085 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((201 : Dyadic) * half ^ 14),
        ((13239 : Dyadic) * half ^ 15)⟩,
       ⟨((659 : Dyadic) * half ^ 13),
        ((-13731 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word42Step21 :
    word42Chunk21.foldl (fun acc a => a.applyPacked acc)
      word42State21 = word42State22 := by decide +kernel

private def word42Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State23 : PackedMat2 :=
    ⟨⟨⟨((9365 : Dyadic) * half ^ 14),
        ((-525 : Dyadic) * half ^ 14)⟩,
       ⟨((-143 : Dyadic) * half ^ 9),
        ((11683 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3959 : Dyadic) * half ^ 15),
        ((119 : Dyadic) * half ^ 11)⟩,
       ⟨((-11977 : Dyadic) * half ^ 15),
        ((-2485 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2009 : Dyadic) * half ^ 13),
        ((4009 : Dyadic) * half ^ 15)⟩,
       ⟨((-2961 : Dyadic) * half ^ 13),
        ((-249 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((10633 : Dyadic) * half ^ 15),
        ((4789 : Dyadic) * half ^ 15)⟩,
       ⟨((-12733 : Dyadic) * half ^ 15),
        ((13941 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word42Step22 :
    word42Chunk22.foldl (fun acc a => a.applyPacked acc)
      word42State22 = word42State23 := by decide +kernel

private def word42Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word42State24 : PackedMat2 :=
    ⟨⟨⟨((11011 : Dyadic) * half ^ 16),
        ((8951 : Dyadic) * half ^ 16)⟩,
       ⟨((54073 : Dyadic) * half ^ 16),
        ((-131 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2945 : Dyadic) * half ^ 16),
        ((14949 : Dyadic) * half ^ 16)⟩,
       ⟨((-25073 : Dyadic) * half ^ 16),
        ((805 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2945 : Dyadic) * half ^ 16),
        ((14949 : Dyadic) * half ^ 16)⟩,
       ⟨((25073 : Dyadic) * half ^ 16),
        ((-805 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-11011 : Dyadic) * half ^ 16),
        ((-8951 : Dyadic) * half ^ 16)⟩,
       ⟨((54073 : Dyadic) * half ^ 16),
        ((-131 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word42Step23 :
    word42Chunk23.foldl (fun acc a => a.applyPacked acc)
      word42State23 = word42State24 := by decide +kernel

private def word42Chunk24 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word42State25 : PackedMat2 :=
    ⟨⟨⟨((-7857 : Dyadic) * half ^ 15),
        ((13403 : Dyadic) * half ^ 16)⟩,
       ⟨((15399 : Dyadic) * half ^ 16),
        ((15915 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((24849 : Dyadic) * half ^ 16),
        ((8281 : Dyadic) * half ^ 17)⟩,
       ⟨((-47715 : Dyadic) * half ^ 16),
        ((5757 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-631 : Dyadic) * half ^ 15),
        ((-18141 : Dyadic) * half ^ 15)⟩,
       ⟨((7019 : Dyadic) * half ^ 16),
        ((-11433 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-157 : Dyadic) * half ^ 12),
        ((-31113 : Dyadic) * half ^ 17)⟩,
       ⟨((-14659 : Dyadic) * half ^ 15),
        ((315 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word42Step24 :
    word42Chunk24.foldl (fun acc a => a.applyPacked acc)
      word42State24 = word42State25 := by decide +kernel

private def word42Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word42State26 : PackedMat2 :=
    ⟨⟨⟨((-59007 : Dyadic) * half ^ 17),
        ((-43305 : Dyadic) * half ^ 18)⟩,
       ⟨((49723 : Dyadic) * half ^ 17),
        ((-54213 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-15203 : Dyadic) * half ^ 17),
        ((6817 : Dyadic) * half ^ 14)⟩,
       ⟨((-2555 : Dyadic) * half ^ 13),
        ((-10999 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((38267 : Dyadic) * half ^ 16),
        ((25677 : Dyadic) * half ^ 18)⟩,
       ⟨((-16269 : Dyadic) * half ^ 16),
        ((56083 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-2727 : Dyadic) * half ^ 16),
        ((54365 : Dyadic) * half ^ 17)⟩,
       ⟨((-48759 : Dyadic) * half ^ 17),
        ((-2321 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word42Step25 :
    word42Chunk25.foldl (fun acc a => a.applyPacked acc)
      word42State25 = word42State26 := by decide +kernel

private def word42Chunk26 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word42State27 : PackedMat2 :=
    ⟨⟨⟨((-77825 : Dyadic) * half ^ 18),
        ((-172873 : Dyadic) * half ^ 19)⟩,
       ⟨((-38525 : Dyadic) * half ^ 16),
        ((12145 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((90945 : Dyadic) * half ^ 18),
        ((-29715 : Dyadic) * half ^ 19)⟩,
       ⟨((-54461 : Dyadic) * half ^ 17),
        ((81525 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((25905 : Dyadic) * half ^ 18),
        ((-17977 : Dyadic) * half ^ 19)⟩,
       ⟨((-13905 : Dyadic) * half ^ 16),
        ((199867 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((20091 : Dyadic) * half ^ 16),
        ((231925 : Dyadic) * half ^ 19)⟩,
       ⟨((92509 : Dyadic) * half ^ 18),
        ((-76275 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word42Step26 :
    word42Chunk26.foldl (fun acc a => a.applyPacked acc)
      word42State26 = word42State27 := by decide +kernel

private def word42Chunk27 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word42State28 : PackedMat2 :=
    ⟨⟨⟨((1783 : Dyadic) * half ^ 17),
        ((-46443 : Dyadic) * half ^ 18)⟩,
       ⟨((-30325 : Dyadic) * half ^ 17),
        ((-140603 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((159571 : Dyadic) * half ^ 19),
        ((166145 : Dyadic) * half ^ 19)⟩,
       ⟨((264979 : Dyadic) * half ^ 19),
        ((-161917 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-159571 : Dyadic) * half ^ 19),
        ((-166145 : Dyadic) * half ^ 19)⟩,
       ⟨((264979 : Dyadic) * half ^ 19),
        ((-161917 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((1783 : Dyadic) * half ^ 17),
        ((-46443 : Dyadic) * half ^ 18)⟩,
       ⟨((30325 : Dyadic) * half ^ 17),
        ((140603 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word42Step27 :
    word42Chunk27.foldl (fun acc a => a.applyPacked acc)
      word42State27 = word42State28 := by decide +kernel

private def word42Chunk28 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word42State29 : PackedMat2 :=
    ⟨⟨⟨((95099 : Dyadic) * half ^ 20),
        ((39235 : Dyadic) * half ^ 17)⟩,
       ⟨((-539053 : Dyadic) * half ^ 20),
        ((-52269 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((60179 : Dyadic) * half ^ 20),
        ((207187 : Dyadic) * half ^ 19)⟩,
       ⟨((-285563 : Dyadic) * half ^ 20),
        ((290521 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((123853 : Dyadic) * half ^ 20),
        ((172871 : Dyadic) * half ^ 20)⟩,
       ⟨((-704895 : Dyadic) * half ^ 20),
        ((28173 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-366149 : Dyadic) * half ^ 20),
        ((-79269 : Dyadic) * half ^ 18)⟩,
       ⟨((261611 : Dyadic) * half ^ 20),
        ((-221977 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word42Step28 :
    word42Chunk28.foldl (fun acc a => a.applyPacked acc)
      word42State28 = word42State29 := by decide +kernel

private def word42Chunk29 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word42State30 : PackedMat2 :=
    ⟨⟨⟨((78791 : Dyadic) * half ^ 21),
        ((230529 : Dyadic) * half ^ 19)⟩,
       ⟨((-43267 : Dyadic) * half ^ 21),
        ((-740039 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-648705 : Dyadic) * half ^ 21),
        ((215499 : Dyadic) * half ^ 21)⟩,
       ⟨((1038301 : Dyadic) * half ^ 21),
        ((16913 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-181673 : Dyadic) * half ^ 21),
        ((843503 : Dyadic) * half ^ 21)⟩,
       ⟨((249325 : Dyadic) * half ^ 21),
        ((97399 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1662155 : Dyadic) * half ^ 21),
        ((61029 : Dyadic) * half ^ 21)⟩,
       ⟨((-182077 : Dyadic) * half ^ 21),
        ((-8881 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word42Step29 :
    word42Chunk29.foldl (fun acc a => a.applyPacked acc)
      word42State29 = word42State30 := by decide +kernel

private def word42Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word42State31 : PackedMat2 :=
    ⟨⟨⟨((666233 : Dyadic) * half ^ 20),
        ((-43611 : Dyadic) * half ^ 21)⟩,
       ⟨((-172285 : Dyadic) * half ^ 21),
        ((236927 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-10291 : Dyadic) * half ^ 18),
        ((-352789 : Dyadic) * half ^ 22)⟩,
       ⟨((-189559 : Dyadic) * half ^ 19),
        ((-545645 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((24107 : Dyadic) * half ^ 19),
        ((168977 : Dyadic) * half ^ 20)⟩,
       ⟨((449217 : Dyadic) * half ^ 21),
        ((210141 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((991319 : Dyadic) * half ^ 21),
        ((-1504751 : Dyadic) * half ^ 22)⟩,
       ⟨((904097 : Dyadic) * half ^ 21),
        ((1160181 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word42Step30 :
    word42Chunk30.foldl (fun acc a => a.applyPacked acc)
      word42State30 = word42State31 := by decide +kernel

private def word42Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State32 : PackedMat2 :=
    ⟨⟨⟨((-64221 : Dyadic) * half ^ 17),
        ((372465 : Dyadic) * half ^ 23)⟩,
       ⟨((2858065 : Dyadic) * half ^ 22),
        ((18107 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1928311 : Dyadic) * half ^ 22),
        ((69591 : Dyadic) * half ^ 23)⟩,
       ⟨((282697 : Dyadic) * half ^ 20),
        ((512473 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((282697 : Dyadic) * half ^ 20),
        ((512473 : Dyadic) * half ^ 23)⟩,
       ⟨((1928311 : Dyadic) * half ^ 22),
        ((69591 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2858065 : Dyadic) * half ^ 22),
        ((-18107 : Dyadic) * half ^ 23)⟩,
       ⟨((64221 : Dyadic) * half ^ 17),
        ((-372465 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word42Step31 :
    word42Chunk31.foldl (fun acc a => a.applyPacked acc)
      word42State31 = word42State32 := by decide +kernel

private def word42Chunk32 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State33 : PackedMat2 :=
    ⟨⟨⟨((252487 : Dyadic) * half ^ 22),
        ((-1197809 : Dyadic) * half ^ 22)⟩,
       ⟨((-697385 : Dyadic) * half ^ 21),
        ((613471 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-6138605 : Dyadic) * half ^ 23),
        ((24669 : Dyadic) * half ^ 21)⟩,
       ⟨((3143627 : Dyadic) * half ^ 23),
        ((280469 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-152569 : Dyadic) * half ^ 20),
        ((1497489 : Dyadic) * half ^ 23)⟩,
       ⟨((31975 : Dyadic) * half ^ 18),
        ((1160279 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1782147 : Dyadic) * half ^ 23),
        ((-1142283 : Dyadic) * half ^ 23)⟩,
       ⟨((-3009089 : Dyadic) * half ^ 23),
        ((1647257 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word42Step32 :
    word42Chunk32.foldl (fun acc a => a.applyPacked acc)
      word42State32 = word42State33 := by decide +kernel

private def word42Chunk33 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word42State34 : PackedMat2 :=
    ⟨⟨⟨((4136909 : Dyadic) * half ^ 24),
        ((-207173 : Dyadic) * half ^ 24)⟩,
       ⟨((4875543 : Dyadic) * half ^ 24),
        ((-2031641 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2441301 : Dyadic) * half ^ 24),
        ((-9656099 : Dyadic) * half ^ 24)⟩,
       ⟨((-1105313 : Dyadic) * half ^ 24),
        ((82151 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-2441301 : Dyadic) * half ^ 24),
        ((-9656099 : Dyadic) * half ^ 24)⟩,
       ⟨((1105313 : Dyadic) * half ^ 24),
        ((-82151 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-4136909 : Dyadic) * half ^ 24),
        ((207173 : Dyadic) * half ^ 24)⟩,
       ⟨((4875543 : Dyadic) * half ^ 24),
        ((-2031641 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word42Step33 :
    word42Chunk33.foldl (fun acc a => a.applyPacked acc)
      word42State33 = word42State34 := by decide +kernel

private def word42Chunk34 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word42State35 : PackedMat2 :=
    ⟨⟨⟨((-641947 : Dyadic) * half ^ 23),
        ((9009217 : Dyadic) * half ^ 24)⟩,
       ⟨((2025515 : Dyadic) * half ^ 24),
        ((-636153 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2113173 : Dyadic) * half ^ 24),
        ((-14265411 : Dyadic) * half ^ 25)⟩,
       ⟨((1931387 : Dyadic) * half ^ 24),
        ((-2295991 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2992355 : Dyadic) * half ^ 23),
        ((252785 : Dyadic) * half ^ 21)⟩,
       ⟨((-8280701 : Dyadic) * half ^ 24),
        ((-90893 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((4822685 : Dyadic) * half ^ 23),
        ((-3309409 : Dyadic) * half ^ 25)⟩,
       ⟨((-1046633 : Dyadic) * half ^ 21),
        ((-741621 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word42Step34 :
    word42Chunk34.foldl (fun acc a => a.applyPacked acc)
      word42State34 = word42State35 := by decide +kernel

private def word42Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word42State36 : PackedMat2 :=
    ⟨⟨⟨((4526523 : Dyadic) * half ^ 23),
        ((12969929 : Dyadic) * half ^ 26)⟩,
       ⟨((-624813 : Dyadic) * half ^ 25),
        ((19773473 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-4370173 : Dyadic) * half ^ 23),
        ((16088079 : Dyadic) * half ^ 26)⟩,
       ⟨((-6434679 : Dyadic) * half ^ 25),
        ((-9130331 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((6434679 : Dyadic) * half ^ 25),
        ((9130331 : Dyadic) * half ^ 26)⟩,
       ⟨((4370173 : Dyadic) * half ^ 23),
        ((-16088079 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-624813 : Dyadic) * half ^ 25),
        ((19773473 : Dyadic) * half ^ 26)⟩,
       ⟨((4526523 : Dyadic) * half ^ 23),
        ((12969929 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word42Step35 :
    word42Chunk35.foldl (fun acc a => a.applyPacked acc)
      word42State35 = word42State36 := by decide +kernel

private def word42Chunk36 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word42State37 : PackedMat2 :=
    ⟨⟨⟨((-2752855 : Dyadic) * half ^ 25),
        ((54771303 : Dyadic) * half ^ 27)⟩,
       ⟨((17404859 : Dyadic) * half ^ 26),
        ((52990961 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((5737969 : Dyadic) * half ^ 26),
        ((1644499 : Dyadic) * half ^ 27)⟩,
       ⟨((8067881 : Dyadic) * half ^ 24),
        ((-19527475 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((8067881 : Dyadic) * half ^ 24),
        ((-19527475 : Dyadic) * half ^ 27)⟩,
       ⟨((5737969 : Dyadic) * half ^ 26),
        ((1644499 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-17404859 : Dyadic) * half ^ 26),
        ((-52990961 : Dyadic) * half ^ 27)⟩,
       ⟨((2752855 : Dyadic) * half ^ 25),
        ((-54771303 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word42Step36 :
    word42Chunk36.foldl (fun acc a => a.applyPacked acc)
      word42State36 = word42State37 := by decide +kernel

private def word42Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word42State38 : PackedMat2 :=
    ⟨⟨⟨((26780457 : Dyadic) * half ^ 27),
        ((-18734413 : Dyadic) * half ^ 27)⟩,
       ⟨((38543763 : Dyadic) * half ^ 27),
        ((63795257 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-14868427 : Dyadic) * half ^ 26),
        ((2023211 : Dyadic) * half ^ 26)⟩,
       ⟨((-33835319 : Dyadic) * half ^ 26),
        ((27144199 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-31190621 : Dyadic) * half ^ 27),
        ((24351873 : Dyadic) * half ^ 26)⟩,
       ⟨((23097777 : Dyadic) * half ^ 27),
        ((-4741723 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((11265211 : Dyadic) * half ^ 25),
        ((16331055 : Dyadic) * half ^ 26)⟩,
       ⟨((-41264835 : Dyadic) * half ^ 26),
        ((-5881653 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word42Step37 :
    word42Chunk37.foldl (fun acc a => a.applyPacked acc)
      word42State37 = word42State38 := by decide +kernel

private def word42Chunk38 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State39 : PackedMat2 :=
    ⟨⟨⟨((-179044511 : Dyadic) * half ^ 28),
        ((-2238751 : Dyadic) * half ^ 28)⟩,
       ⟨((56395315 : Dyadic) * half ^ 28),
        ((-17208613 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((119370559 : Dyadic) * half ^ 28),
        ((20438381 : Dyadic) * half ^ 28)⟩,
       ⟨((-13405265 : Dyadic) * half ^ 28),
        ((-9710397 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((119370559 : Dyadic) * half ^ 28),
        ((20438381 : Dyadic) * half ^ 28)⟩,
       ⟨((13405265 : Dyadic) * half ^ 28),
        ((9710397 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((179044511 : Dyadic) * half ^ 28),
        ((2238751 : Dyadic) * half ^ 28)⟩,
       ⟨((56395315 : Dyadic) * half ^ 28),
        ((-17208613 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word42Step38 :
    word42Chunk38.foldl (fun acc a => a.applyPacked acc)
      word42State38 = word42State39 := by decide +kernel

private def word42Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word42State40 : PackedMat2 :=
    ⟨⟨⟨((9312185 : Dyadic) * half ^ 27),
        ((-43822147 : Dyadic) * half ^ 29)⟩,
       ⟨((-64867155 : Dyadic) * half ^ 27),
        ((1173917 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-6156837 : Dyadic) * half ^ 28),
        ((19673353 : Dyadic) * half ^ 25)⟩,
       ⟨((-26767249 : Dyadic) * half ^ 27),
        ((-27145741 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-184532565 : Dyadic) * half ^ 28),
        ((-47377661 : Dyadic) * half ^ 29)⟩,
       ⟨((130241083 : Dyadic) * half ^ 28),
        ((-59691335 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-1406127 : Dyadic) * half ^ 24),
        ((18544835 : Dyadic) * half ^ 26)⟩,
       ⟨((21324115 : Dyadic) * half ^ 28),
        ((27777485 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word42Step39 :
    word42Chunk39.foldl (fun acc a => a.applyPacked acc)
      word42State39 = word42State40 := by decide +kernel

private def word42Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word42State41 : PackedMat2 :=
    ⟨⟨⟨((11508625 : Dyadic) * half ^ 26),
        ((-278698825 : Dyadic) * half ^ 30)⟩,
       ⟨((-33736211 : Dyadic) * half ^ 29),
        ((-357582249 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((96733129 : Dyadic) * half ^ 27),
        ((-1844339 : Dyadic) * half ^ 30)⟩,
       ⟨((69285991 : Dyadic) * half ^ 29),
        ((206530735 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-51171599 : Dyadic) * half ^ 28),
        ((-456218507 : Dyadic) * half ^ 30)⟩,
       ⟨((104187537 : Dyadic) * half ^ 29),
        ((-317646525 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-318140537 : Dyadic) * half ^ 29),
        ((58332789 : Dyadic) * half ^ 30)⟩,
       ⟨((2465107 : Dyadic) * half ^ 25),
        ((125805211 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word42Step40 :
    word42Chunk40.foldl (fun acc a => a.applyPacked acc)
      word42State40 = word42State41 := by decide +kernel

private def word42Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word42State42 : PackedMat2 :=
    ⟨⟨⟨((-17827427 : Dyadic) * half ^ 27),
        ((249484689 : Dyadic) * half ^ 29)⟩,
       ⟨((-184850393 : Dyadic) * half ^ 29),
        ((-14262361 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((247010207 : Dyadic) * half ^ 30),
        ((127250377 : Dyadic) * half ^ 29)⟩,
       ⟨((554021539 : Dyadic) * half ^ 30),
        ((170663 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((247010207 : Dyadic) * half ^ 30),
        ((127250377 : Dyadic) * half ^ 29)⟩,
       ⟨((-554021539 : Dyadic) * half ^ 30),
        ((-170663 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((17827427 : Dyadic) * half ^ 27),
        ((-249484689 : Dyadic) * half ^ 29)⟩,
       ⟨((-184850393 : Dyadic) * half ^ 29),
        ((-14262361 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word42Step41 :
    word42Chunk41.foldl (fun acc a => a.applyPacked acc)
      word42State41 = word42State42 := by decide +kernel

private def word42Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word42State43 : PackedMat2 :=
    ⟨⟨⟨((59529659 : Dyadic) * half ^ 30),
        ((1075744647 : Dyadic) * half ^ 31)⟩,
       ⟨((114245571 : Dyadic) * half ^ 30),
        ((-444211499 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-702162423 : Dyadic) * half ^ 31),
        ((-76175845 : Dyadic) * half ^ 31)⟩,
       ⟨((-375647781 : Dyadic) * half ^ 31),
        ((-57052235 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((8326755 : Dyadic) * half ^ 27),
        ((269452551 : Dyadic) * half ^ 30)⟩,
       ⟨((9561805 : Dyadic) * half ^ 30),
        ((163257321 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((187321649 : Dyadic) * half ^ 31),
        ((86887615 : Dyadic) * half ^ 30)⟩,
       ⟨((1964167645 : Dyadic) * half ^ 31),
        ((-6839489 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word42Step42 :
    word42Chunk42.foldl (fun acc a => a.applyPacked acc)
      word42State42 = word42State43 := by decide +kernel

private def word42Chunk43 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word42State44 : PackedMat2 :=
    ⟨⟨⟨((-55338255 : Dyadic) * half ^ 32),
        ((1599037773 : Dyadic) * half ^ 32)⟩,
       ⟨((-1635740795 : Dyadic) * half ^ 32),
        ((4923765 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-647064371 : Dyadic) * half ^ 32),
        ((-365901971 : Dyadic) * half ^ 31)⟩,
       ⟨((-3022854239 : Dyadic) * half ^ 32),
        ((84745153 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-647064371 : Dyadic) * half ^ 32),
        ((-365901971 : Dyadic) * half ^ 31)⟩,
       ⟨((3022854239 : Dyadic) * half ^ 32),
        ((-84745153 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((55338255 : Dyadic) * half ^ 32),
        ((-1599037773 : Dyadic) * half ^ 32)⟩,
       ⟨((-1635740795 : Dyadic) * half ^ 32),
        ((4923765 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word42Step43 :
    word42Chunk43.foldl (fun acc a => a.applyPacked acc)
      word42State43 = word42State44 := by decide +kernel

private def word42Chunk44 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State45 : PackedMat2 :=
    ⟨⟨⟨((641068053 : Dyadic) * half ^ 31),
        ((-1619420685 : Dyadic) * half ^ 33)⟩,
       ⟨((785134349 : Dyadic) * half ^ 30),
        ((589972855 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1454353885 : Dyadic) * half ^ 32),
        ((117957975 : Dyadic) * half ^ 32)⟩,
       ⟨((23247571 : Dyadic) * half ^ 31),
        ((-80397755 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-1404322055 : Dyadic) * half ^ 32),
        ((-1407858743 : Dyadic) * half ^ 33)⟩,
       ⟨((-1168406105 : Dyadic) * half ^ 32),
        ((1500849027 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-552348385 : Dyadic) * half ^ 31),
        ((-929200645 : Dyadic) * half ^ 32)⟩,
       ⟨((514723915 : Dyadic) * half ^ 32),
        ((-2211336751 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word42Step44 :
    word42Chunk44.foldl (fun acc a => a.applyPacked acc)
      word42State44 = word42State45 := by decide +kernel

private def word42Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word42State46 : PackedMat2 :=
    ⟨⟨⟨((-301179775 : Dyadic) * half ^ 31),
        ((712430935 : Dyadic) * half ^ 34)⟩,
       ⟨((4123048217 : Dyadic) * half ^ 33),
        ((-578905283 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-275271277 : Dyadic) * half ^ 33),
        ((8732166639 : Dyadic) * half ^ 34)⟩,
       ⟨((-504084899 : Dyadic) * half ^ 32),
        ((-5603072243 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-782273599 : Dyadic) * half ^ 32),
        ((1283441075 : Dyadic) * half ^ 34)⟩,
       ⟨((-7167619441 : Dyadic) * half ^ 33),
        ((-732898521 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((33381413 : Dyadic) * half ^ 32),
        ((2918329117 : Dyadic) * half ^ 34)⟩,
       ⟨((645668109 : Dyadic) * half ^ 33),
        ((-5327767317 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word42Step45 :
    word42Chunk45.foldl (fun acc a => a.applyPacked acc)
      word42State45 = word42State46 := by decide +kernel

private def word42Chunk46 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word42State47 : PackedMat2 :=
    ⟨⟨⟨((-1997389731 : Dyadic) * half ^ 34),
        ((-1774182451 : Dyadic) * half ^ 32)⟩,
       ⟨((-6269174289 : Dyadic) * half ^ 34),
        ((-348351727 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((905792677 : Dyadic) * half ^ 31),
        ((-420941235 : Dyadic) * half ^ 33)⟩,
       ⟨((-912801249 : Dyadic) * half ^ 33),
        ((6815351545 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5973469075 : Dyadic) * half ^ 34),
        ((2710369459 : Dyadic) * half ^ 34)⟩,
       ⟨((-7657234015 : Dyadic) * half ^ 34),
        ((4535971957 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3896716629 : Dyadic) * half ^ 33),
        ((2066641005 : Dyadic) * half ^ 33)⟩,
       ⟨((3200013175 : Dyadic) * half ^ 33),
        ((-2135892279 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word42Step46 :
    word42Chunk46.foldl (fun acc a => a.applyPacked acc)
      word42State46 = word42State47 := by decide +kernel

private def word42Chunk47 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word42State48 : PackedMat2 :=
    ⟨⟨⟨((-155441951 : Dyadic) * half ^ 34),
        ((3447696083 : Dyadic) * half ^ 35)⟩,
       ⟨((-6665982927 : Dyadic) * half ^ 34),
        ((-133588125 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-6932230637 : Dyadic) * half ^ 35),
        ((15466811517 : Dyadic) * half ^ 35)⟩,
       ⟨((5556452173 : Dyadic) * half ^ 35),
        ((14360865215 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-7456919183 : Dyadic) * half ^ 33),
        ((42993077 : Dyadic) * half ^ 31)⟩,
       ⟨((-552973151 : Dyadic) * half ^ 34),
        ((6244341405 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((1310286083 : Dyadic) * half ^ 35),
        ((-3410712439 : Dyadic) * half ^ 34)⟩,
       ⟨((5585106083 : Dyadic) * half ^ 35),
        ((406908811 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word42Step47 :
    word42Chunk47.foldl (fun acc a => a.applyPacked acc)
      word42State47 = word42State48 := by decide +kernel

private def word42Chunk48 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word42State49 : PackedMat2 :=
    ⟨⟨⟨((44159044767 : Dyadic) * half ^ 36),
        ((-1924208027 : Dyadic) * half ^ 36)⟩,
       ⟨((-18122009537 : Dyadic) * half ^ 36),
        ((-5722298149 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((16028707839 : Dyadic) * half ^ 36),
        ((1809870487 : Dyadic) * half ^ 34)⟩,
       ⟨((-8066830849 : Dyadic) * half ^ 36),
        ((29561477161 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-22321995213 : Dyadic) * half ^ 36),
        ((47061599 : Dyadic) * half ^ 28)⟩,
       ⟨((-36800959109 : Dyadic) * half ^ 36),
        ((-3980938495 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-9520388271 : Dyadic) * half ^ 36),
        ((-1946282947 : Dyadic) * half ^ 32)⟩,
       ⟨((-13368804325 : Dyadic) * half ^ 36),
        ((13018517615 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word42Step48 :
    word42Chunk48.foldl (fun acc a => a.applyPacked acc)
      word42State48 = word42State49 := by decide +kernel

private def word42Chunk49 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word42State50 : PackedMat2 :=
    ⟨⟨⟨((-4224908055 : Dyadic) * half ^ 36),
        ((3736963579 : Dyadic) * half ^ 35)⟩,
       ⟨((8220885535 : Dyadic) * half ^ 35),
        ((7649711969 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-12101470435 : Dyadic) * half ^ 35),
        ((-36197786063 : Dyadic) * half ^ 37)⟩,
       ⟨((26263885641 : Dyadic) * half ^ 35),
        ((-20265264745 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((26263885641 : Dyadic) * half ^ 35),
        ((-20265264745 : Dyadic) * half ^ 37)⟩,
       ⟨((-12101470435 : Dyadic) * half ^ 35),
        ((-36197786063 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-8220885535 : Dyadic) * half ^ 35),
        ((-7649711969 : Dyadic) * half ^ 36)⟩,
       ⟨((4224908055 : Dyadic) * half ^ 36),
        ((-3736963579 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word42Step49 :
    word42Chunk49.foldl (fun acc a => a.applyPacked acc)
      word42State49 = word42State50 := by decide +kernel

private def word42Chunk50 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word42State51 : PackedMat2 :=
    ⟨⟨⟨((13431342491 : Dyadic) * half ^ 34),
        ((10585804841 : Dyadic) * half ^ 38)⟩,
       ⟨((-591472829 : Dyadic) * half ^ 35),
        ((-15950663429 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((624233013 : Dyadic) * half ^ 34),
        ((-50229706745 : Dyadic) * half ^ 37)⟩,
       ⟨((10733227623 : Dyadic) * half ^ 37),
        ((-15687486181 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-18854734383 : Dyadic) * half ^ 37),
        ((-5739363519 : Dyadic) * half ^ 38)⟩,
       ⟨((81604679107 : Dyadic) * half ^ 37),
        ((-15727091727 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-13268234135 : Dyadic) * half ^ 37),
        ((-27454157811 : Dyadic) * half ^ 36)⟩,
       ⟨((-1341214647 : Dyadic) * half ^ 36),
        ((26271212153 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word42Step50 :
    word42Chunk50.foldl (fun acc a => a.applyPacked acc)
      word42State50 = word42State51 := by decide +kernel

private def word42Chunk51 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word42State52 : PackedMat2 :=
    ⟨⟨⟨((-27667837215 : Dyadic) * half ^ 36),
        ((109442126313 : Dyadic) * half ^ 39)⟩,
       ⟨((188738881057 : Dyadic) * half ^ 38),
        ((115894225155 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-47850060245 : Dyadic) * half ^ 38),
        ((47653363451 : Dyadic) * half ^ 39)⟩,
       ⟨((-5626654495 : Dyadic) * half ^ 34),
        ((83102471573 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-5626654495 : Dyadic) * half ^ 34),
        ((83102471573 : Dyadic) * half ^ 39)⟩,
       ⟨((-47850060245 : Dyadic) * half ^ 38),
        ((47653363451 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-188738881057 : Dyadic) * half ^ 38),
        ((-115894225155 : Dyadic) * half ^ 39)⟩,
       ⟨((27667837215 : Dyadic) * half ^ 36),
        ((-109442126313 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word42Step51 :
    word42Chunk51.foldl (fun acc a => a.applyPacked acc)
      word42State51 = word42State52 := by decide +kernel

private def word42Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word42State53 : PackedMat2 :=
    ⟨⟨⟨((-240867381861 : Dyadic) * half ^ 39),
        ((60798881415 : Dyadic) * half ^ 39)⟩,
       ⟨((113210913777 : Dyadic) * half ^ 39),
        ((-4455935777 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-111231150883 : Dyadic) * half ^ 39),
        ((186519777063 : Dyadic) * half ^ 39)⟩,
       ⟨((-299715956459 : Dyadic) * half ^ 39),
        ((-18126598239 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-331532562975 : Dyadic) * half ^ 39),
        ((-23560600697 : Dyadic) * half ^ 37)⟩,
       ⟨((41506991151 : Dyadic) * half ^ 39),
        ((-205473553671 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((132093853847 : Dyadic) * half ^ 39),
        ((-177039147819 : Dyadic) * half ^ 39)⟩,
       ⟨((10496091017 : Dyadic) * half ^ 39),
        ((31914117021 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word42Step52 :
    word42Chunk52.foldl (fun acc a => a.applyPacked acc)
      word42State52 = word42State53 := by decide +kernel

private def word42Chunk53 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word42State54 : PackedMat2 :=
    ⟨⟨⟨((-305112047977 : Dyadic) * half ^ 40),
        ((-121233825319 : Dyadic) * half ^ 40)⟩,
       ⟨((40089831685 : Dyadic) * half ^ 40),
        ((-353789215621 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((68603733461 : Dyadic) * half ^ 40),
        ((-132109410453 : Dyadic) * half ^ 40)⟩,
       ⟨((-2970710095 : Dyadic) * half ^ 40),
        ((-37028038213 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((68603733461 : Dyadic) * half ^ 40),
        ((-132109410453 : Dyadic) * half ^ 40)⟩,
       ⟨((2970710095 : Dyadic) * half ^ 40),
        ((37028038213 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((305112047977 : Dyadic) * half ^ 40),
        ((121233825319 : Dyadic) * half ^ 40)⟩,
       ⟨((40089831685 : Dyadic) * half ^ 40),
        ((-353789215621 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word42Step53 :
    word42Chunk53.foldl (fun acc a => a.applyPacked acc)
      word42State53 = word42State54 := by decide +kernel

private def word42Chunk54 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word42State55 : PackedMat2 :=
    ⟨⟨⟨((-588492423159 : Dyadic) * half ^ 40),
        ((305721344925 : Dyadic) * half ^ 41)⟩,
       ⟨((-391381544377 : Dyadic) * half ^ 40),
        ((-788320727183 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-124368475717 : Dyadic) * half ^ 40),
        ((189099421331 : Dyadic) * half ^ 39)⟩,
       ⟨((22171395559 : Dyadic) * half ^ 37),
        ((-48693739941 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((22171395559 : Dyadic) * half ^ 37),
        ((-48693739941 : Dyadic) * half ^ 39)⟩,
       ⟨((-124368475717 : Dyadic) * half ^ 40),
        ((189099421331 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((391381544377 : Dyadic) * half ^ 40),
        ((788320727183 : Dyadic) * half ^ 41)⟩,
       ⟨((588492423159 : Dyadic) * half ^ 40),
        ((-305721344925 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word42Step54 :
    word42Chunk54.foldl (fun acc a => a.applyPacked acc)
      word42State54 = word42State55 := by decide +kernel

private def word42Chunk55 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word42State56 : PackedMat2 :=
    ⟨⟨⟨((903853183185 : Dyadic) * half ^ 40),
        ((338491192231 : Dyadic) * half ^ 42)⟩,
       ⟨((37175752633 : Dyadic) * half ^ 41),
        ((-187571535617 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((331941662459 : Dyadic) * half ^ 40),
        ((116511601787 : Dyadic) * half ^ 42)⟩,
       ⟨((-567949313463 : Dyadic) * half ^ 41),
        ((1201286212625 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-329449453603 : Dyadic) * half ^ 40),
        ((-95934011455 : Dyadic) * half ^ 42)⟩,
       ⟨((542387305419 : Dyadic) * half ^ 41),
        ((-1231832638381 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((75459828307 : Dyadic) * half ^ 41),
        ((1844882119003 : Dyadic) * half ^ 42)⟩,
       ⟨((65757840981 : Dyadic) * half ^ 39),
        ((1770530613737 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word42Step55 :
    word42Chunk55.foldl (fun acc a => a.applyPacked acc)
      word42State55 = word42State56 := by decide +kernel

private def word42Chunk56 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word42State57 : PackedMat2 :=
    ⟨⟨⟨((-2245734079997 : Dyadic) * half ^ 42),
        ((187887419417 : Dyadic) * half ^ 40)⟩,
       ⟨((1278041128581 : Dyadic) * half ^ 42),
        ((893057764869 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((146173131187 : Dyadic) * half ^ 39),
        ((31565752025 : Dyadic) * half ^ 40)⟩,
       ⟨((926777896477 : Dyadic) * half ^ 41),
        ((-400634531883 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-274371523783 : Dyadic) * half ^ 42),
        ((1511470421225 : Dyadic) * half ^ 42)⟩,
       ⟨((526897539983 : Dyadic) * half ^ 42),
        ((-342085371729 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1268832603703 : Dyadic) * half ^ 41),
        ((120961618927 : Dyadic) * half ^ 40)⟩,
       ⟨((517282926035 : Dyadic) * half ^ 41),
        ((1761887604289 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word42Step56 :
    word42Chunk56.foldl (fun acc a => a.applyPacked acc)
      word42State56 = word42State57 := by decide +kernel

private def word42Chunk57 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word42State58 : PackedMat2 :=
    ⟨⟨⟨((2078614019709 : Dyadic) * half ^ 43),
        ((-2216242070809 : Dyadic) * half ^ 42)⟩,
       ⟨((2495882028975 : Dyadic) * half ^ 43),
        ((2155853814349 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-2879070905335 : Dyadic) * half ^ 43),
        ((-216095948359 : Dyadic) * half ^ 43)⟩,
       ⟨((2613850065727 : Dyadic) * half ^ 43),
        ((614134561693 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1444365071745 : Dyadic) * half ^ 43),
        ((2746460485531 : Dyadic) * half ^ 43)⟩,
       ⟨((1012173175027 : Dyadic) * half ^ 43),
        ((-33152604951 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-6588337955967 : Dyadic) * half ^ 43),
        ((-208634004633 : Dyadic) * half ^ 43)⟩,
       ⟨((2276630327269 : Dyadic) * half ^ 43),
        ((-1143624012171 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word42Step57 :
    word42Chunk57.foldl (fun acc a => a.applyPacked acc)
      word42State57 = word42State58 := by decide +kernel

private def word42Chunk58 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word42State59 : PackedMat2 :=
    ⟨⟨⟨((-4958242620233 : Dyadic) * half ^ 43),
        ((2669220690891 : Dyadic) * half ^ 44)⟩,
       ⟨((3701247411717 : Dyadic) * half ^ 43),
        ((-2069212532447 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-2408594979603 : Dyadic) * half ^ 42),
        ((-2157987016677 : Dyadic) * half ^ 43)⟩,
       ⟨((927048834353 : Dyadic) * half ^ 43),
        ((55253046513 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-927048834353 : Dyadic) * half ^ 43),
        ((-55253046513 : Dyadic) * half ^ 43)⟩,
       ⟨((2408594979603 : Dyadic) * half ^ 42),
        ((2157987016677 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((3701247411717 : Dyadic) * half ^ 43),
        ((-2069212532447 : Dyadic) * half ^ 44)⟩,
       ⟨((-4958242620233 : Dyadic) * half ^ 43),
        ((2669220690891 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word42Step58 :
    word42Chunk58.foldl (fun acc a => a.applyPacked acc)
      word42State58 = word42State59 := by decide +kernel

private def word42Chunk59 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word42State60 : PackedMat2 :=
    ⟨⟨⟨((-104977886473 : Dyadic) * half ^ 44),
        ((-7736766614993 : Dyadic) * half ^ 45)⟩,
       ⟨((-5922322555943 : Dyadic) * half ^ 43),
        ((5755741480971 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-34938555779 : Dyadic) * half ^ 36),
        ((-7675673478991 : Dyadic) * half ^ 45)⟩,
       ⟨((251558754053 : Dyadic) * half ^ 44),
        ((-5131097055539 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-6403385267265 : Dyadic) * half ^ 44),
        ((-8692711525371 : Dyadic) * half ^ 45)⟩,
       ⟨((-636144105863 : Dyadic) * half ^ 43),
        ((-9195829033477 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((990512567011 : Dyadic) * half ^ 44),
        ((11949622998359 : Dyadic) * half ^ 45)⟩,
       ⟨((3373127023991 : Dyadic) * half ^ 43),
        ((-11739667225413 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word42Step59 :
    word42Chunk59.foldl (fun acc a => a.applyPacked acc)
      word42State59 = word42State60 := by decide +kernel

private def word42Chunk60 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word42State61 : PackedMat2 :=
    ⟨⟨⟨((5255631882079 : Dyadic) * half ^ 44),
        ((1363507135727 : Dyadic) * half ^ 45)⟩,
       ⟨((432690737889 : Dyadic) * half ^ 41),
        ((-2778778475661 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-8917744800055 : Dyadic) * half ^ 45),
        ((-6176766625417 : Dyadic) * half ^ 44)⟩,
       ⟨((-20821621382945 : Dyadic) * half ^ 45),
        ((8920139169 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((8917744800055 : Dyadic) * half ^ 45),
        ((6176766625417 : Dyadic) * half ^ 44)⟩,
       ⟨((-20821621382945 : Dyadic) * half ^ 45),
        ((8920139169 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((5255631882079 : Dyadic) * half ^ 44),
        ((1363507135727 : Dyadic) * half ^ 45)⟩,
       ⟨((-432690737889 : Dyadic) * half ^ 41),
        ((2778778475661 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word42Step60 :
    word42Chunk60.foldl (fun acc a => a.applyPacked acc)
      word42State60 = word42State61 := by decide +kernel

private def word42Chunk61 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word42State62 : PackedMat2 :=
    ⟨⟨⟨((9681394346087 : Dyadic) * half ^ 46),
        ((5593774454439 : Dyadic) * half ^ 46)⟩,
       ⟨((-16233372432553 : Dyadic) * half ^ 46),
        ((3163047866031 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((27580898343273 : Dyadic) * half ^ 46),
        ((8908010946991 : Dyadic) * half ^ 45)⟩,
       ⟨((11585505726237 : Dyadic) * half ^ 46),
        ((-38223929754789 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((56039951648771 : Dyadic) * half ^ 46),
        ((3998848154259 : Dyadic) * half ^ 45)⟩,
       ⟨((20407907860807 : Dyadic) * half ^ 46),
        ((-19583202034755 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((732321277623 : Dyadic) * half ^ 46),
        ((-1619672923665 : Dyadic) * half ^ 43)⟩,
       ⟨((11919870186501 : Dyadic) * half ^ 46),
        ((-3275989043233 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word42Step61 :
    word42Chunk61.foldl (fun acc a => a.applyPacked acc)
      word42State61 = word42State62 := by decide +kernel

private def word42Chunk62 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word42State63 : PackedMat2 :=
    ⟨⟨⟨((64200439631285 : Dyadic) * half ^ 47),
        ((6764983270597 : Dyadic) * half ^ 44)⟩,
       ⟨((-56348338589855 : Dyadic) * half ^ 47),
        ((39844292325411 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((41494449786199 : Dyadic) * half ^ 47),
        ((-14670503412713 : Dyadic) * half ^ 46)⟩,
       ⟨((-4097261435883 : Dyadic) * half ^ 47),
        ((2897201345607 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((-41494449786199 : Dyadic) * half ^ 47),
        ((14670503412713 : Dyadic) * half ^ 46)⟩,
       ⟨((-4097261435883 : Dyadic) * half ^ 47),
        ((2897201345607 : Dyadic) * half ^ 47)⟩⟩,
     ⟨⟨((64200439631285 : Dyadic) * half ^ 47),
        ((6764983270597 : Dyadic) * half ^ 44)⟩,
       ⟨((56348338589855 : Dyadic) * half ^ 47),
        ((-39844292325411 : Dyadic) * half ^ 47)⟩⟩⟩
private lemma word42Step62 :
    word42Chunk62.foldl (fun acc a => a.applyPacked acc)
      word42State62 = word42State63 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word42_check : check word42 42 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word42 = word42State63.toMatrix := by
    unfold evalRingPacked
    change ((
      word42Chunk0 ++ word42Chunk1 ++ word42Chunk2 ++ word42Chunk3 ++
      word42Chunk4 ++ word42Chunk5 ++ word42Chunk6 ++ word42Chunk7 ++
      word42Chunk8 ++ word42Chunk9 ++ word42Chunk10 ++ word42Chunk11 ++
      word42Chunk12 ++ word42Chunk13 ++ word42Chunk14 ++ word42Chunk15 ++
      word42Chunk16 ++ word42Chunk17 ++ word42Chunk18 ++ word42Chunk19 ++
      word42Chunk20 ++ word42Chunk21 ++ word42Chunk22 ++ word42Chunk23 ++
      word42Chunk24 ++ word42Chunk25 ++ word42Chunk26 ++ word42Chunk27 ++
      word42Chunk28 ++ word42Chunk29 ++ word42Chunk30 ++ word42Chunk31 ++
      word42Chunk32 ++ word42Chunk33 ++ word42Chunk34 ++ word42Chunk35 ++
      word42Chunk36 ++ word42Chunk37 ++ word42Chunk38 ++ word42Chunk39 ++
      word42Chunk40 ++ word42Chunk41 ++ word42Chunk42 ++ word42Chunk43 ++
      word42Chunk44 ++ word42Chunk45 ++ word42Chunk46 ++ word42Chunk47 ++
      word42Chunk48 ++ word42Chunk49 ++ word42Chunk50 ++ word42Chunk51 ++
      word42Chunk52 ++ word42Chunk53 ++ word42Chunk54 ++ word42Chunk55 ++
      word42Chunk56 ++ word42Chunk57 ++ word42Chunk58 ++ word42Chunk59 ++
      word42Chunk60 ++ word42Chunk61 ++ word42Chunk62
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word42Step0, word42Step1, word42Step2, word42Step3, word42Step4,
      word42Step5, word42Step6, word42Step7, word42Step8, word42Step9,
      word42Step10, word42Step11, word42Step12, word42Step13, word42Step14,
      word42Step15, word42Step16, word42Step17, word42Step18, word42Step19,
      word42Step20, word42Step21, word42Step22, word42Step23, word42Step24,
      word42Step25, word42Step26, word42Step27, word42Step28, word42Step29,
      word42Step30, word42Step31, word42Step32, word42Step33, word42Step34,
      word42Step35, word42Step36, word42Step37, word42Step38, word42Step39,
      word42Step40, word42Step41, word42Step42, word42Step43, word42Step44,
      word42Step45, word42Step46, word42Step47, word42Step48, word42Step49,
      word42Step50, word42Step51, word42Step52, word42Step53, word42Step54,
      word42Step55, word42Step56, word42Step57, word42Step58, word42Step59,
      word42Step60, word42Step61, word42Step62]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
