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
private def word29Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word29State1 : PackedMat2 :=
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
private lemma word29Step0 :
    word29Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word29State1 := by decide +kernel

private def word29Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word29State2 : PackedMat2 :=
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
private lemma word29Step1 :
    word29Chunk1.foldl (fun acc a => a.applyPacked acc)
      word29State1 = word29State2 := by decide +kernel

private def word29Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word29State3 : PackedMat2 :=
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
private lemma word29Step2 :
    word29Chunk2.foldl (fun acc a => a.applyPacked acc)
      word29State2 = word29State3 := by decide +kernel

private def word29Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word29State4 : PackedMat2 :=
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
private lemma word29Step3 :
    word29Chunk3.foldl (fun acc a => a.applyPacked acc)
      word29State3 = word29State4 := by decide +kernel

private def word29Chunk4 : List Letter := [.h, .s, .h, .s, .s, .s, .h, .s]
private def word29State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word29Step4 :
    word29Chunk4.foldl (fun acc a => a.applyPacked acc)
      word29State4 = word29State5 := by decide +kernel

private def word29Chunk5 : List Letter := [.s, .h, .h, .t, .h, .s, .t, .h]
private def word29State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word29Step5 :
    word29Chunk5.foldl (fun acc a => a.applyPacked acc)
      word29State5 = word29State6 := by decide +kernel

private def word29Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word29State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word29Step6 :
    word29Chunk6.foldl (fun acc a => a.applyPacked acc)
      word29State6 = word29State7 := by decide +kernel

private def word29Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word29State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-9 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word29Step7 :
    word29Chunk7.foldl (fun acc a => a.applyPacked acc)
      word29State7 = word29State8 := by decide +kernel

private def word29Chunk8 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word29State9 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word29Step8 :
    word29Chunk8.foldl (fun acc a => a.applyPacked acc)
      word29State8 = word29State9 := by decide +kernel

private def word29Chunk9 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State10 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word29Step9 :
    word29Chunk9.foldl (fun acc a => a.applyPacked acc)
      word29State9 = word29State10 := by decide +kernel

private def word29Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word29State11 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((19 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word29Step10 :
    word29Chunk10.foldl (fun acc a => a.applyPacked acc)
      word29State10 = word29State11 := by decide +kernel

private def word29Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word29State12 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-29 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((49 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 6)⟩,
       ⟨((17 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((33 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-15 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word29Step11 :
    word29Chunk11.foldl (fun acc a => a.applyPacked acc)
      word29State11 = word29State12 := by decide +kernel

private def word29Chunk12 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word29State13 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 7),
        ((61 : Dyadic) * half ^ 7)⟩,
       ⟨((47 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((47 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((-41 : Dyadic) * half ^ 7),
        ((61 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word29Step12 :
    word29Chunk12.foldl (fun acc a => a.applyPacked acc)
      word29State12 = word29State13 := by decide +kernel

private def word29Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word29State14 : PackedMat2 :=
    ⟨⟨⟨((105 : Dyadic) * half ^ 8),
        ((-55 : Dyadic) * half ^ 8)⟩,
       ⟨((15 : Dyadic) * half ^ 8),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 8),
        ((77 : Dyadic) * half ^ 8)⟩,
       ⟨((113 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 8),
        ((77 : Dyadic) * half ^ 8)⟩,
       ⟨((-113 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-105 : Dyadic) * half ^ 8),
        ((55 : Dyadic) * half ^ 8)⟩,
       ⟨((15 : Dyadic) * half ^ 8),
        ((13 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word29Step13 :
    word29Chunk13.foldl (fun acc a => a.applyPacked acc)
      word29State13 = word29State14 := by decide +kernel

private def word29Chunk14 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word29State15 : PackedMat2 :=
    ⟨⟨⟨((-105 : Dyadic) * half ^ 8),
        ((-39 : Dyadic) * half ^ 9)⟩,
       ⟨((27 : Dyadic) * half ^ 8),
        ((-177 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((-165 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((207 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 6),
        ((165 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((207 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-105 : Dyadic) * half ^ 8),
        ((-39 : Dyadic) * half ^ 9)⟩,
       ⟨((-27 : Dyadic) * half ^ 8),
        ((177 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word29Step14 :
    word29Chunk14.foldl (fun acc a => a.applyPacked acc)
      word29State14 = word29State15 := by decide +kernel

private def word29Chunk15 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State16 : PackedMat2 :=
    ⟨⟨⟨((111 : Dyadic) * half ^ 9),
        ((249 : Dyadic) * half ^ 10)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((267 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-359 : Dyadic) * half ^ 9),
        ((-77 : Dyadic) * half ^ 10)⟩,
       ⟨((-1 : Dyadic) * half ^ 8),
        ((-127 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 9),
        ((-357 : Dyadic) * half ^ 10)⟩,
       ⟨((51 : Dyadic) * half ^ 8),
        ((361 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 9),
        ((-319 : Dyadic) * half ^ 10)⟩,
       ⟨((129 : Dyadic) * half ^ 8),
        ((-97 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word29Step15 :
    word29Chunk15.foldl (fun acc a => a.applyPacked acc)
      word29State15 = word29State16 := by decide +kernel

private def word29Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word29State17 : PackedMat2 :=
    ⟨⟨⟨((455 : Dyadic) * half ^ 10),
        ((-43 : Dyadic) * half ^ 9)⟩,
       ⟨((19 : Dyadic) * half ^ 10),
        ((-61 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((133 : Dyadic) * half ^ 10),
        ((-429 : Dyadic) * half ^ 10)⟩,
       ⟨((-597 : Dyadic) * half ^ 10),
        ((-165 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-597 : Dyadic) * half ^ 10),
        ((-165 : Dyadic) * half ^ 10)⟩,
       ⟨((133 : Dyadic) * half ^ 10),
        ((-429 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 10),
        ((61 : Dyadic) * half ^ 9)⟩,
       ⟨((-455 : Dyadic) * half ^ 10),
        ((43 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word29Step16 :
    word29Chunk16.foldl (fun acc a => a.applyPacked acc)
      word29State16 = word29State17 := by decide +kernel

private def word29Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word29State18 : PackedMat2 :=
    ⟨⟨⟨((-455 : Dyadic) * half ^ 11),
        ((471 : Dyadic) * half ^ 10)⟩,
       ⟨((805 : Dyadic) * half ^ 11),
        ((165 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-297 : Dyadic) * half ^ 11),
        ((5 : Dyadic) * half ^ 7)⟩,
       ⟨((-405 : Dyadic) * half ^ 11),
        ((-789 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((297 : Dyadic) * half ^ 11),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-405 : Dyadic) * half ^ 11),
        ((-789 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-455 : Dyadic) * half ^ 11),
        ((471 : Dyadic) * half ^ 10)⟩,
       ⟨((-805 : Dyadic) * half ^ 11),
        ((-165 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word29Step17 :
    word29Chunk17.foldl (fun acc a => a.applyPacked acc)
      word29State17 = word29State18 := by decide +kernel

private def word29Chunk18 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word29State19 : PackedMat2 :=
    ⟨⟨⟨((-221 : Dyadic) * half ^ 11),
        ((-1791 : Dyadic) * half ^ 12)⟩,
       ⟨((-431 : Dyadic) * half ^ 11),
        ((601 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((587 : Dyadic) * half ^ 10),
        ((133 : Dyadic) * half ^ 12)⟩,
       ⟨((-427 : Dyadic) * half ^ 10),
        ((343 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((587 : Dyadic) * half ^ 10),
        ((133 : Dyadic) * half ^ 12)⟩,
       ⟨((427 : Dyadic) * half ^ 10),
        ((-343 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((221 : Dyadic) * half ^ 11),
        ((1791 : Dyadic) * half ^ 12)⟩,
       ⟨((-431 : Dyadic) * half ^ 11),
        ((601 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word29Step18 :
    word29Chunk18.foldl (fun acc a => a.applyPacked acc)
      word29State18 = word29State19 := by decide +kernel

private def word29Chunk19 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word29State20 : PackedMat2 :=
    ⟨⟨⟨((-1239 : Dyadic) * half ^ 12),
        ((-2701 : Dyadic) * half ^ 13)⟩,
       ⟨((859 : Dyadic) * half ^ 11),
        ((-1267 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2697 : Dyadic) * half ^ 12),
        ((-491 : Dyadic) * half ^ 13)⟩,
       ⟨((323 : Dyadic) * half ^ 11),
        ((239 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((323 : Dyadic) * half ^ 11),
        ((239 : Dyadic) * half ^ 13)⟩,
       ⟨((2697 : Dyadic) * half ^ 12),
        ((-491 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-859 : Dyadic) * half ^ 11),
        ((1267 : Dyadic) * half ^ 13)⟩,
       ⟨((1239 : Dyadic) * half ^ 12),
        ((2701 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word29Step19 :
    word29Chunk19.foldl (fun acc a => a.applyPacked acc)
      word29State19 = word29State20 := by decide +kernel

private def word29Chunk20 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word29State21 : PackedMat2 :=
    ⟨⟨⟨((-3773 : Dyadic) * half ^ 13),
        ((-243 : Dyadic) * half ^ 12)⟩,
       ⟨((191 : Dyadic) * half ^ 13),
        ((61 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-2855 : Dyadic) * half ^ 13),
        ((3211 : Dyadic) * half ^ 13)⟩,
       ⟨((4175 : Dyadic) * half ^ 13),
        ((1751 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2481 : Dyadic) * half ^ 12),
        ((-165 : Dyadic) * half ^ 11)⟩,
       ⟨((-365 : Dyadic) * half ^ 11),
        ((3515 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-91 : Dyadic) * half ^ 11),
        ((-1791 : Dyadic) * half ^ 13)⟩,
       ⟨((-19 : Dyadic) * half ^ 8),
        ((-991 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word29Step20 :
    word29Chunk20.foldl (fun acc a => a.applyPacked acc)
      word29State20 = word29State21 := by decide +kernel

private def word29Chunk21 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word29State22 : PackedMat2 :=
    ⟨⟨⟨((-799 : Dyadic) * half ^ 11),
        ((-3313 : Dyadic) * half ^ 14)⟩,
       ⟨((3199 : Dyadic) * half ^ 13),
        ((-63 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-477 : Dyadic) * half ^ 12),
        ((-2595 : Dyadic) * half ^ 13)⟩,
       ⟨((599 : Dyadic) * half ^ 10),
        ((-1897 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((599 : Dyadic) * half ^ 10),
        ((-1897 : Dyadic) * half ^ 14)⟩,
       ⟨((-477 : Dyadic) * half ^ 12),
        ((-2595 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3199 : Dyadic) * half ^ 13),
        ((63 : Dyadic) * half ^ 9)⟩,
       ⟨((799 : Dyadic) * half ^ 11),
        ((3313 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word29Step21 :
    word29Chunk21.foldl (fun acc a => a.applyPacked acc)
      word29State21 = word29State22 := by decide +kernel

private def word29Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State23 : PackedMat2 :=
    ⟨⟨⟨((8281 : Dyadic) * half ^ 15),
        ((-2963 : Dyadic) * half ^ 15)⟩,
       ⟨((-20027 : Dyadic) * half ^ 15),
        ((-1621 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-17367 : Dyadic) * half ^ 15),
        ((3357 : Dyadic) * half ^ 15)⟩,
       ⟨((-12187 : Dyadic) * half ^ 15),
        ((1929 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-7215 : Dyadic) * half ^ 15),
        ((14777 : Dyadic) * half ^ 15)⟩,
       ⟨((501 : Dyadic) * half ^ 15),
        ((1295 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-9447 : Dyadic) * half ^ 15),
        ((-5873 : Dyadic) * half ^ 15)⟩,
       ⟨((3521 : Dyadic) * half ^ 15),
        ((7077 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word29Step22 :
    word29Chunk22.foldl (fun acc a => a.applyPacked acc)
      word29State22 = word29State23 := by decide +kernel

private def word29Chunk23 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word29State24 : PackedMat2 :=
    ⟨⟨⟨((15051 : Dyadic) * half ^ 16),
        ((10965 : Dyadic) * half ^ 15)⟩,
       ⟨((-27331 : Dyadic) * half ^ 16),
        ((5441 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-31493 : Dyadic) * half ^ 16),
        ((-3813 : Dyadic) * half ^ 15)⟩,
       ⟨((24353 : Dyadic) * half ^ 16),
        ((-17309 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-24935 : Dyadic) * half ^ 16),
        ((-1785 : Dyadic) * half ^ 15)⟩,
       ⟨((9683 : Dyadic) * half ^ 16),
        ((-27923 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-27371 : Dyadic) * half ^ 16),
        ((1535 : Dyadic) * half ^ 14)⟩,
       ⟨((-16489 : Dyadic) * half ^ 16),
        ((-21191 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word29Step23 :
    word29Chunk23.foldl (fun acc a => a.applyPacked acc)
      word29State23 = word29State24 := by decide +kernel

private def word29Chunk24 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State25 : PackedMat2 :=
    ⟨⟨⟨((1917 : Dyadic) * half ^ 16),
        ((-4875 : Dyadic) * half ^ 16)⟩,
       ⟨((19859 : Dyadic) * half ^ 15),
        ((-8787 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2637 : Dyadic) * half ^ 15),
        ((197 : Dyadic) * half ^ 13)⟩,
       ⟨((-48635 : Dyadic) * half ^ 16),
        ((-7539 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2637 : Dyadic) * half ^ 15),
        ((-197 : Dyadic) * half ^ 13)⟩,
       ⟨((-48635 : Dyadic) * half ^ 16),
        ((-7539 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1917 : Dyadic) * half ^ 16),
        ((-4875 : Dyadic) * half ^ 16)⟩,
       ⟨((-19859 : Dyadic) * half ^ 15),
        ((8787 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word29Step24 :
    word29Chunk24.foldl (fun acc a => a.applyPacked acc)
      word29State24 = word29State25 := by decide +kernel

private def word29Chunk25 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word29State26 : PackedMat2 :=
    ⟨⟨⟨((-55431 : Dyadic) * half ^ 17),
        ((-32501 : Dyadic) * half ^ 18)⟩,
       ⟨((-3271 : Dyadic) * half ^ 16),
        ((113047 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((65449 : Dyadic) * half ^ 17),
        ((-37105 : Dyadic) * half ^ 18)⟩,
       ⟨((-3033 : Dyadic) * half ^ 14),
        ((-56317 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((4803 : Dyadic) * half ^ 16),
        ((89713 : Dyadic) * half ^ 18)⟩,
       ⟨((46711 : Dyadic) * half ^ 17),
        ((-41185 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((36387 : Dyadic) * half ^ 16),
        ((48889 : Dyadic) * half ^ 18)⟩,
       ⟨((40273 : Dyadic) * half ^ 17),
        ((-61973 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word29Step25 :
    word29Chunk25.foldl (fun acc a => a.applyPacked acc)
      word29State25 = word29State26 := by decide +kernel

private def word29Chunk26 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word29State27 : PackedMat2 :=
    ⟨⟨⟨((19745 : Dyadic) * half ^ 17),
        ((-130507 : Dyadic) * half ^ 18)⟩,
       ⟨((10235 : Dyadic) * half ^ 15),
        ((2683 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((21295 : Dyadic) * half ^ 17),
        ((54929 : Dyadic) * half ^ 17)⟩,
       ⟨((1295 : Dyadic) * half ^ 17),
        ((13707 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((123565 : Dyadic) * half ^ 18),
        ((11295 : Dyadic) * half ^ 17)⟩,
       ⟨((96151 : Dyadic) * half ^ 18),
        ((625 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((125141 : Dyadic) * half ^ 18),
        ((-60685 : Dyadic) * half ^ 18)⟩,
       ⟨((135873 : Dyadic) * half ^ 18),
        ((21195 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word29Step26 :
    word29Chunk26.foldl (fun acc a => a.applyPacked acc)
      word29State26 = word29State27 := by decide +kernel

private def word29Chunk27 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word29State28 : PackedMat2 :=
    ⟨⟨⟨((-214653 : Dyadic) * half ^ 19),
        ((53451 : Dyadic) * half ^ 17)⟩,
       ⟨((-170121 : Dyadic) * half ^ 19),
        ((-88895 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((11481 : Dyadic) * half ^ 19),
        ((13471 : Dyadic) * half ^ 18)⟩,
       ⟨((245445 : Dyadic) * half ^ 19),
        ((124107 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-151049 : Dyadic) * half ^ 19),
        ((-128463 : Dyadic) * half ^ 19)⟩,
       ⟨((97165 : Dyadic) * half ^ 19),
        ((58491 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((124909 : Dyadic) * half ^ 19),
        ((-192387 : Dyadic) * half ^ 19)⟩,
       ⟨((302699 : Dyadic) * half ^ 19),
        ((-11133 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word29Step27 :
    word29Chunk27.foldl (fun acc a => a.applyPacked acc)
      word29State27 = word29State28 := by decide +kernel

private def word29Chunk28 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word29State29 : PackedMat2 :=
    ⟨⟨⟨((-4197 : Dyadic) * half ^ 18),
        ((-3335 : Dyadic) * half ^ 19)⟩,
       ⟨((-419261 : Dyadic) * half ^ 19),
        ((2339 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-192807 : Dyadic) * half ^ 19),
        ((13391 : Dyadic) * half ^ 18)⟩,
       ⟨((59875 : Dyadic) * half ^ 17),
        ((18911 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-345 : Dyadic) * half ^ 14),
        ((-432307 : Dyadic) * half ^ 20)⟩,
       ⟨((-16151 : Dyadic) * half ^ 17),
        ((-46693 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((12691 : Dyadic) * half ^ 19),
        ((-410867 : Dyadic) * half ^ 20)⟩,
       ⟨((6021 : Dyadic) * half ^ 19),
        ((-427655 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word29Step28 :
    word29Chunk28.foldl (fun acc a => a.applyPacked acc)
      word29State28 = word29State29 := by decide +kernel

private def word29Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word29State30 : PackedMat2 :=
    ⟨⟨⟨((21651 : Dyadic) * half ^ 17),
        ((56251 : Dyadic) * half ^ 19)⟩,
       ⟨((-879359 : Dyadic) * half ^ 20),
        ((99053 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-223599 : Dyadic) * half ^ 20),
        ((-311129 : Dyadic) * half ^ 20)⟩,
       ⟨((20215 : Dyadic) * half ^ 18),
        ((-24131 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((223599 : Dyadic) * half ^ 20),
        ((311129 : Dyadic) * half ^ 20)⟩,
       ⟨((20215 : Dyadic) * half ^ 18),
        ((-24131 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((21651 : Dyadic) * half ^ 17),
        ((56251 : Dyadic) * half ^ 19)⟩,
       ⟨((879359 : Dyadic) * half ^ 20),
        ((-99053 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word29Step29 :
    word29Chunk29.foldl (fun acc a => a.applyPacked acc)
      word29State29 = word29State30 := by decide +kernel

private def word29Chunk30 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word29State31 : PackedMat2 :=
    ⟨⟨⟨((1040523 : Dyadic) * half ^ 21),
        ((-1301511 : Dyadic) * half ^ 22)⟩,
       ⟨((-200115 : Dyadic) * half ^ 19),
        ((-581195 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-812927 : Dyadic) * half ^ 21),
        ((-941739 : Dyadic) * half ^ 22)⟩,
       ⟨((-183775 : Dyadic) * half ^ 19),
        ((-167955 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-96723 : Dyadic) * half ^ 19),
        ((-77827 : Dyadic) * half ^ 22)⟩,
       ⟨((554847 : Dyadic) * half ^ 21),
        ((1548027 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((180079 : Dyadic) * half ^ 20),
        ((-1840983 : Dyadic) * half ^ 22)⟩,
       ⟨((-941353 : Dyadic) * half ^ 21),
        ((240063 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word29Step30 :
    word29Chunk30.foldl (fun acc a => a.applyPacked acc)
      word29State30 = word29State31 := by decide +kernel

private def word29Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State32 : PackedMat2 :=
    ⟨⟨⟨((-987113 : Dyadic) * half ^ 22),
        ((1822931 : Dyadic) * half ^ 22)⟩,
       ⟨((1454477 : Dyadic) * half ^ 22),
        ((533887 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1521293 : Dyadic) * half ^ 22),
        ((-202279 : Dyadic) * half ^ 21)⟩,
       ⟨((-1574027 : Dyadic) * half ^ 22),
        ((-520437 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1574027 : Dyadic) * half ^ 22),
        ((-520437 : Dyadic) * half ^ 21)⟩,
       ⟨((1521293 : Dyadic) * half ^ 22),
        ((-202279 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1454477 : Dyadic) * half ^ 22),
        ((-533887 : Dyadic) * half ^ 22)⟩,
       ⟨((987113 : Dyadic) * half ^ 22),
        ((-1822931 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word29Step31 :
    word29Chunk31.foldl (fun acc a => a.applyPacked acc)
      word29State31 = word29State32 := by decide +kernel

private def word29Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word29State33 : PackedMat2 :=
    ⟨⟨⟨((-213737 : Dyadic) * half ^ 19),
        ((1010087 : Dyadic) * half ^ 22)⟩,
       ⟨((266589 : Dyadic) * half ^ 22),
        ((-1637721 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((2168215 : Dyadic) * half ^ 22),
        ((839211 : Dyadic) * half ^ 22)⟩,
       ⟨((-137893 : Dyadic) * half ^ 20),
        ((-155987 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-1463159 : Dyadic) * half ^ 22),
        ((-2719787 : Dyadic) * half ^ 23)⟩,
       ⟨((215263 : Dyadic) * half ^ 22),
        ((1616643 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((10343 : Dyadic) * half ^ 14),
        ((-1976485 : Dyadic) * half ^ 23)⟩,
       ⟨((313817 : Dyadic) * half ^ 21),
        ((1443307 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word29Step32 :
    word29Chunk32.foldl (fun acc a => a.applyPacked acc)
      word29State32 = word29State33 := by decide +kernel

private def word29Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word29State34 : PackedMat2 :=
    ⟨⟨⟨((3539543 : Dyadic) * half ^ 23),
        ((-1969113 : Dyadic) * half ^ 24)⟩,
       ⟨((-6811 : Dyadic) * half ^ 17),
        ((5530731 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-420073 : Dyadic) * half ^ 23),
        ((5564703 : Dyadic) * half ^ 24)⟩,
       ⟨((2322473 : Dyadic) * half ^ 22),
        ((2522787 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((760479 : Dyadic) * half ^ 22),
        ((-5065019 : Dyadic) * half ^ 24)⟩,
       ⟨((-4043745 : Dyadic) * half ^ 23),
        ((-4224873 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1874961 : Dyadic) * half ^ 22),
        ((-3975447 : Dyadic) * half ^ 24)⟩,
       ⟨((1780809 : Dyadic) * half ^ 23),
        ((3103639 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word29Step33 :
    word29Chunk33.foldl (fun acc a => a.applyPacked acc)
      word29State33 = word29State34 := by decide +kernel

private def word29Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word29State35 : PackedMat2 :=
    ⟨⟨⟨((-2356813 : Dyadic) * half ^ 23),
        ((7293045 : Dyadic) * half ^ 25)⟩,
       ⟨((-4565301 : Dyadic) * half ^ 24),
        ((1704413 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((684417 : Dyadic) * half ^ 23),
        ((-5455841 : Dyadic) * half ^ 25)⟩,
       ⟨((13675791 : Dyadic) * half ^ 24),
        ((3628747 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2271147 : Dyadic) * half ^ 23),
        ((12306957 : Dyadic) * half ^ 25)⟩,
       ⟨((-913547 : Dyadic) * half ^ 24),
        ((15044625 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((698579 : Dyadic) * half ^ 22),
        ((-148325 : Dyadic) * half ^ 25)⟩,
       ⟨((-4498729 : Dyadic) * half ^ 24),
        ((9278927 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word29Step34 :
    word29Chunk34.foldl (fun acc a => a.applyPacked acc)
      word29State34 = word29State35 := by decide +kernel

private def word29Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word29State36 : PackedMat2 :=
    ⟨⟨⟨((1311189 : Dyadic) * half ^ 22),
        ((-354739 : Dyadic) * half ^ 22)⟩,
       ⟨((5333289 : Dyadic) * half ^ 24),
        ((895595 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-11922629 : Dyadic) * half ^ 24),
        ((3200983 : Dyadic) * half ^ 25)⟩,
       ⟨((4781441 : Dyadic) * half ^ 24),
        ((630979 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-13296647 : Dyadic) * half ^ 25),
        ((1785297 : Dyadic) * half ^ 23)⟩,
       ⟨((6894681 : Dyadic) * half ^ 25),
        ((8352035 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1942317 : Dyadic) * half ^ 25),
        ((10578045 : Dyadic) * half ^ 25)⟩,
       ⟨((-3733507 : Dyadic) * half ^ 25),
        ((-88533 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word29Step35 :
    word29Chunk35.foldl (fun acc a => a.applyPacked acc)
      word29State35 = word29State36 := by decide +kernel

private def word29Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word29State37 : PackedMat2 :=
    ⟨⟨⟨((-29639049 : Dyadic) * half ^ 26),
        ((16735105 : Dyadic) * half ^ 26)⟩,
       ⟨((19175383 : Dyadic) * half ^ 26),
        ((95831 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-5103233 : Dyadic) * half ^ 26),
        ((-23362877 : Dyadic) * half ^ 26)⟩,
       ⟨((-7387437 : Dyadic) * half ^ 26),
        ((3168833 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-5103233 : Dyadic) * half ^ 26),
        ((-23362877 : Dyadic) * half ^ 26)⟩,
       ⟨((7387437 : Dyadic) * half ^ 26),
        ((-3168833 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((29639049 : Dyadic) * half ^ 26),
        ((-16735105 : Dyadic) * half ^ 26)⟩,
       ⟨((19175383 : Dyadic) * half ^ 26),
        ((95831 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word29Step36 :
    word29Chunk36.foldl (fun acc a => a.applyPacked acc)
      word29State36 = word29State37 := by decide +kernel

private def word29Chunk37 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word29State38 : PackedMat2 :=
    ⟨⟨⟨((-28437805 : Dyadic) * half ^ 27),
        ((-21354139 : Dyadic) * half ^ 27)⟩,
       ⟨((26308983 : Dyadic) * half ^ 27),
        ((-22083381 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-8582521 : Dyadic) * half ^ 27),
        ((-48606771 : Dyadic) * half ^ 27)⟩,
       ⟨((2342515 : Dyadic) * half ^ 27),
        ((14679641 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-10111793 : Dyadic) * half ^ 27),
        ((3120003 : Dyadic) * half ^ 27)⟩,
       ⟨((107325335 : Dyadic) * half ^ 27),
        ((2731259 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-65520901 : Dyadic) * half ^ 27),
        ((-1064411 : Dyadic) * half ^ 27)⟩,
       ⟨((22812623 : Dyadic) * half ^ 27),
        ((-13686697 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word29Step37 :
    word29Chunk37.foldl (fun acc a => a.applyPacked acc)
      word29State37 = word29State38 := by decide +kernel

private def word29Chunk38 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word29State39 : PackedMat2 :=
    ⟨⟨⟨((-13769487 : Dyadic) * half ^ 25),
        ((18628209 : Dyadic) * half ^ 28)⟩,
       ⟨((-33066695 : Dyadic) * half ^ 26),
        ((-43610025 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((32353829 : Dyadic) * half ^ 27),
        ((-109380927 : Dyadic) * half ^ 28)⟩,
       ⟨((39136353 : Dyadic) * half ^ 27),
        ((42947705 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((32353829 : Dyadic) * half ^ 27),
        ((-109380927 : Dyadic) * half ^ 28)⟩,
       ⟨((-39136353 : Dyadic) * half ^ 27),
        ((-42947705 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((13769487 : Dyadic) * half ^ 25),
        ((-18628209 : Dyadic) * half ^ 28)⟩,
       ⟨((-33066695 : Dyadic) * half ^ 26),
        ((-43610025 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word29Step38 :
    word29Chunk38.foldl (fun acc a => a.applyPacked acc)
      word29State38 = word29State39 := by decide +kernel

private def word29Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word29State40 : PackedMat2 :=
    ⟨⟨⟨((58989105 : Dyadic) * half ^ 27),
        ((-138036053 : Dyadic) * half ^ 29)⟩,
       ⟨((-22523657 : Dyadic) * half ^ 28),
        ((-106856047 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-40252047 : Dyadic) * half ^ 26),
        ((-99451385 : Dyadic) * half ^ 29)⟩,
       ⟨((106420651 : Dyadic) * half ^ 28),
        ((-20052779 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((39699303 : Dyadic) * half ^ 28),
        ((267428839 : Dyadic) * half ^ 29)⟩,
       ⟨((-29876041 : Dyadic) * half ^ 27),
        ((-54587537 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-15590003 : Dyadic) * half ^ 28),
        ((140501867 : Dyadic) * half ^ 29)⟩,
       ⟨((61223025 : Dyadic) * half ^ 27),
        ((-95454553 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word29Step39 :
    word29Chunk39.foldl (fun acc a => a.applyPacked acc)
      word29State39 = word29State40 := by decide +kernel

private def word29Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word29State41 : PackedMat2 :=
    ⟨⟨⟨((2843487 : Dyadic) * half ^ 25),
        ((110565963 : Dyadic) * half ^ 28)⟩,
       ⟨((58771407 : Dyadic) * half ^ 28),
        ((-101568073 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-43946913 : Dyadic) * half ^ 28),
        ((-219999825 : Dyadic) * half ^ 29)⟩,
       ⟨((-79268655 : Dyadic) * half ^ 28),
        ((55061491 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((79268655 : Dyadic) * half ^ 28),
        ((-55061491 : Dyadic) * half ^ 28)⟩,
       ⟨((43946913 : Dyadic) * half ^ 28),
        ((219999825 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((58771407 : Dyadic) * half ^ 28),
        ((-101568073 : Dyadic) * half ^ 29)⟩,
       ⟨((2843487 : Dyadic) * half ^ 25),
        ((110565963 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word29Step40 :
    word29Chunk40.foldl (fun acc a => a.applyPacked acc)
      word29State40 = word29State41 := by decide +kernel

private def word29Chunk41 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word29State42 : PackedMat2 :=
    ⟨⟨⟨((-5401769 : Dyadic) * half ^ 30),
        ((182385607 : Dyadic) * half ^ 30)⟩,
       ⟨((-47763511 : Dyadic) * half ^ 30),
        ((115472577 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-604162339 : Dyadic) * half ^ 30),
        ((-161993297 : Dyadic) * half ^ 30)⟩,
       ⟨((251915991 : Dyadic) * half ^ 30),
        ((-37127229 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-604162339 : Dyadic) * half ^ 30),
        ((-161993297 : Dyadic) * half ^ 30)⟩,
       ⟨((-251915991 : Dyadic) * half ^ 30),
        ((37127229 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((5401769 : Dyadic) * half ^ 30),
        ((-182385607 : Dyadic) * half ^ 30)⟩,
       ⟨((-47763511 : Dyadic) * half ^ 30),
        ((115472577 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word29Step41 :
    word29Chunk41.foldl (fun acc a => a.applyPacked acc)
      word29State41 = word29State42 := by decide +kernel

private def word29Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word29State43 : PackedMat2 :=
    ⟨⟨⟨((-1537516539 : Dyadic) * half ^ 31),
        ((-64672363 : Dyadic) * half ^ 31)⟩,
       ⟨((769370277 : Dyadic) * half ^ 31),
        ((-93720065 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-726947735 : Dyadic) * half ^ 31),
        ((-186427685 : Dyadic) * half ^ 31)⟩,
       ⟨((980858237 : Dyadic) * half ^ 31),
        ((-46259053 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((278945791 : Dyadic) * half ^ 31),
        ((-126955251 : Dyadic) * half ^ 31)⟩,
       ⟨((93909579 : Dyadic) * half ^ 31),
        ((426951493 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-252112493 : Dyadic) * half ^ 31),
        ((-384073131 : Dyadic) * half ^ 31)⟩,
       ⟨((122767767 : Dyadic) * half ^ 31),
        ((-72090213 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word29Step42 :
    word29Chunk42.foldl (fun acc a => a.applyPacked acc)
      word29State42 = word29State43 := by decide +kernel

private def word29Chunk43 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State44 : PackedMat2 :=
    ⟨⟨⟨((292464955 : Dyadic) * half ^ 30),
        ((-514143083 : Dyadic) * half ^ 31)⟩,
       ⟨((-1232544865 : Dyadic) * half ^ 31),
        ((296298811 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-299966287 : Dyadic) * half ^ 31),
        ((-479515163 : Dyadic) * half ^ 31)⟩,
       ⟨((-465995999 : Dyadic) * half ^ 30),
        ((-140049717 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-299966287 : Dyadic) * half ^ 31),
        ((-479515163 : Dyadic) * half ^ 31)⟩,
       ⟨((465995999 : Dyadic) * half ^ 30),
        ((140049717 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-292464955 : Dyadic) * half ^ 30),
        ((514143083 : Dyadic) * half ^ 31)⟩,
       ⟨((-1232544865 : Dyadic) * half ^ 31),
        ((296298811 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word29Step43 :
    word29Chunk43.foldl (fun acc a => a.applyPacked acc)
      word29State43 = word29State44 := by decide +kernel

private def word29Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word29State45 : PackedMat2 :=
    ⟨⟨⟨((621986365 : Dyadic) * half ^ 31),
        ((1809220483 : Dyadic) * half ^ 33)⟩,
       ⟨((1096843827 : Dyadic) * half ^ 32),
        ((-4125401607 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-30610325 : Dyadic) * half ^ 29),
        ((-127149793 : Dyadic) * half ^ 33)⟩,
       ⟨((-2230805917 : Dyadic) * half ^ 32),
        ((-1005539547 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-439194877 : Dyadic) * half ^ 32),
        ((-1985923317 : Dyadic) * half ^ 33)⟩,
       ⟨((-283172335 : Dyadic) * half ^ 31),
        ((-2475688517 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2967311045 : Dyadic) * half ^ 32),
        ((147128903 : Dyadic) * half ^ 33)⟩,
       ⟨((579045281 : Dyadic) * half ^ 31),
        ((-2340816557 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word29Step44 :
    word29Chunk44.foldl (fun acc a => a.applyPacked acc)
      word29State44 = word29State45 := by decide +kernel

private def word29Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word29State46 : PackedMat2 :=
    ⟨⟨⟨((119657407 : Dyadic) * half ^ 30),
        ((1685124215 : Dyadic) * half ^ 32)⟩,
       ⟨((-2556117397 : Dyadic) * half ^ 32),
        ((1498684295 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1673814427 : Dyadic) * half ^ 32),
        ((1162497415 : Dyadic) * half ^ 33)⟩,
       ⟨((-1173632987 : Dyadic) * half ^ 32),
        ((-115840005 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-930817405 : Dyadic) * half ^ 33),
        ((-7815335 : Dyadic) * half ^ 27)⟩,
       ⟨((-1394177425 : Dyadic) * half ^ 33),
        ((-1423723707 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((4868932725 : Dyadic) * half ^ 33),
        ((-2077487769 : Dyadic) * half ^ 33)⟩,
       ⟨((1871564135 : Dyadic) * half ^ 33),
        ((3034747025 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word29Step45 :
    word29Chunk45.foldl (fun acc a => a.applyPacked acc)
      word29State45 = word29State46 := by decide +kernel

private def word29Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word29State47 : PackedMat2 :=
    ⟨⟨⟨((10921914249 : Dyadic) * half ^ 34),
        ((-1041606479 : Dyadic) * half ^ 34)⟩,
       ⟨((2560450421 : Dyadic) * half ^ 34),
        ((-2294716889 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((9541193529 : Dyadic) * half ^ 34),
        ((1501821095 : Dyadic) * half ^ 34)⟩,
       ⟨((4755832969 : Dyadic) * half ^ 34),
        ((924989233 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((9541193529 : Dyadic) * half ^ 34),
        ((1501821095 : Dyadic) * half ^ 34)⟩,
       ⟨((-4755832969 : Dyadic) * half ^ 34),
        ((-924989233 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-10921914249 : Dyadic) * half ^ 34),
        ((1041606479 : Dyadic) * half ^ 34)⟩,
       ⟨((2560450421 : Dyadic) * half ^ 34),
        ((-2294716889 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word29Step46 :
    word29Chunk46.foldl (fun acc a => a.applyPacked acc)
      word29State46 = word29State47 := by decide +kernel

private def word29Chunk47 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word29State48 : PackedMat2 :=
    ⟨⟨⟨((2448765075 : Dyadic) * half ^ 34),
        ((8506584561 : Dyadic) * half ^ 34)⟩,
       ⟨((-753196569 : Dyadic) * half ^ 33),
        ((-82783631 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3168526257 : Dyadic) * half ^ 33),
        ((4366410771 : Dyadic) * half ^ 34)⟩,
       ⟨((7900800441 : Dyadic) * half ^ 34),
        ((834110143 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-883075157 : Dyadic) * half ^ 32),
        ((14237852955 : Dyadic) * half ^ 35)⟩,
       ⟨((2600260457 : Dyadic) * half ^ 33),
        ((1563747927 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((8672151823 : Dyadic) * half ^ 34),
        ((3955158213 : Dyadic) * half ^ 35)⟩,
       ⟨((-8341017299 : Dyadic) * half ^ 34),
        ((-942371937 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word29Step47 :
    word29Chunk47.foldl (fun acc a => a.applyPacked acc)
      word29State47 = word29State48 := by decide +kernel

private def word29Chunk48 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word29State49 : PackedMat2 :=
    ⟨⟨⟨((8630970837 : Dyadic) * half ^ 34),
        ((18171068463 : Dyadic) * half ^ 36)⟩,
       ⟨((625572109 : Dyadic) * half ^ 30),
        ((-6417546411 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((5623210817 : Dyadic) * half ^ 35),
        ((-6759587521 : Dyadic) * half ^ 36)⟩,
       ⟨((7708087633 : Dyadic) * half ^ 35),
        ((-19095387589 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((3083950017 : Dyadic) * half ^ 34),
        ((-130304801 : Dyadic) * half ^ 32)⟩,
       ⟨((12927487555 : Dyadic) * half ^ 35),
        ((-6665649225 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-12294307437 : Dyadic) * half ^ 35),
        ((1378182907 : Dyadic) * half ^ 35)⟩,
       ⟨((2938380513 : Dyadic) * half ^ 34),
        ((18640124581 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word29Step48 :
    word29Chunk48.foldl (fun acc a => a.applyPacked acc)
      word29State48 = word29State49 := by decide +kernel

private def word29Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word29State50 : PackedMat2 :=
    ⟨⟨⟨((2206617187 : Dyadic) * half ^ 32),
        ((-1273563347 : Dyadic) * half ^ 34)⟩,
       ⟨((50081321653 : Dyadic) * half ^ 36),
        ((8632922753 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-7720431583 : Dyadic) * half ^ 36),
        ((2920885671 : Dyadic) * half ^ 36)⟩,
       ⟨((5364415059 : Dyadic) * half ^ 34),
        ((-10716015045 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((7720431583 : Dyadic) * half ^ 36),
        ((-2920885671 : Dyadic) * half ^ 36)⟩,
       ⟨((5364415059 : Dyadic) * half ^ 34),
        ((-10716015045 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((2206617187 : Dyadic) * half ^ 32),
        ((-1273563347 : Dyadic) * half ^ 34)⟩,
       ⟨((-50081321653 : Dyadic) * half ^ 36),
        ((-8632922753 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word29Step49 :
    word29Chunk49.foldl (fun acc a => a.applyPacked acc)
      word29State49 = word29State50 := by decide +kernel

private def word29Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word29State51 : PackedMat2 :=
    ⟨⟨⟨((23946446107 : Dyadic) * half ^ 37),
        ((-51660882575 : Dyadic) * half ^ 37)⟩,
       ⟨((51869706469 : Dyadic) * half ^ 37),
        ((-8544300575 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((63883195585 : Dyadic) * half ^ 37),
        ((3018229357 : Dyadic) * half ^ 35)⟩,
       ⟨((73939105309 : Dyadic) * half ^ 37),
        ((3073570995 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-190368761 : Dyadic) * half ^ 30),
        ((-68911150447 : Dyadic) * half ^ 37)⟩,
       ⟨((27670819 : Dyadic) * half ^ 34),
        ((2513977431 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-30102591575 : Dyadic) * half ^ 36),
        ((148078423 : Dyadic) * half ^ 29)⟩,
       ⟨((-2694786375 : Dyadic) * half ^ 33),
        ((-13961630181 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word29Step50 :
    word29Chunk50.foldl (fun acc a => a.applyPacked acc)
      word29State50 = word29State51 := by decide +kernel

private def word29Chunk51 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word29State52 : PackedMat2 :=
    ⟨⟨⟨((-182815930161 : Dyadic) * half ^ 38),
        ((34170635541 : Dyadic) * half ^ 38)⟩,
       ⟨((-14189338203 : Dyadic) * half ^ 38),
        ((1771444567 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-114097221339 : Dyadic) * half ^ 38),
        ((-81056038845 : Dyadic) * half ^ 38)⟩,
       ⟨((-37558414785 : Dyadic) * half ^ 38),
        ((38617042235 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-114097221339 : Dyadic) * half ^ 38),
        ((-81056038845 : Dyadic) * half ^ 38)⟩,
       ⟨((37558414785 : Dyadic) * half ^ 38),
        ((-38617042235 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((182815930161 : Dyadic) * half ^ 38),
        ((-34170635541 : Dyadic) * half ^ 38)⟩,
       ⟨((-14189338203 : Dyadic) * half ^ 38),
        ((1771444567 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word29Step51 :
    word29Chunk51.foldl (fun acc a => a.applyPacked acc)
      word29State51 = word29State52 := by decide +kernel

private def word29Chunk52 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word29State53 : PackedMat2 :=
    ⟨⟨⟨((-228735808947 : Dyadic) * half ^ 39),
        ((-184298614383 : Dyadic) * half ^ 39)⟩,
       ⟨((-41212458203 : Dyadic) * half ^ 39),
        ((-61264806207 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-144175655903 : Dyadic) * half ^ 39),
        ((193236400831 : Dyadic) * half ^ 39)⟩,
       ⟨((-161288348755 : Dyadic) * half ^ 39),
        ((59971642385 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-313179685601 : Dyadic) * half ^ 39),
        ((152732002329 : Dyadic) * half ^ 39)⟩,
       ⟨((-73293116061 : Dyadic) * half ^ 39),
        ((-4278173213 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-306828226797 : Dyadic) * half ^ 39),
        ((-134974133575 : Dyadic) * half ^ 39)⟩,
       ⟨((-61769001969 : Dyadic) * half ^ 39),
        ((-23440418843 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word29Step52 :
    word29Chunk52.foldl (fun acc a => a.applyPacked acc)
      word29State52 = word29State53 := by decide +kernel

private def word29Chunk53 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word29State54 : PackedMat2 :=
    ⟨⟨⟨((-41424805571 : Dyadic) * half ^ 40),
        ((-75628807023 : Dyadic) * half ^ 38)⟩,
       ⟨((-599157913065 : Dyadic) * half ^ 40),
        ((-183016267143 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-456885917027 : Dyadic) * half ^ 40),
        ((4485626319 : Dyadic) * half ^ 36)⟩,
       ⟨((219799450251 : Dyadic) * half ^ 40),
        ((-406718793769 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-334948772665 : Dyadic) * half ^ 40),
        ((-29635808347 : Dyadic) * half ^ 38)⟩,
       ⟨((478488814873 : Dyadic) * half ^ 40),
        ((-338342683639 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((485531495235 : Dyadic) * half ^ 40),
        ((160145679659 : Dyadic) * half ^ 39)⟩,
       ⟨((119498960949 : Dyadic) * half ^ 40),
        ((-278866553747 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word29Step53 :
    word29Chunk53.foldl (fun acc a => a.applyPacked acc)
      word29State53 = word29State54 := by decide +kernel

private def word29Chunk54 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word29State55 : PackedMat2 :=
    ⟨⟨⟨((-112835996685 : Dyadic) * half ^ 40),
        ((548310255341 : Dyadic) * half ^ 41)⟩,
       ⟨((24714288585 : Dyadic) * half ^ 40),
        ((-973443162261 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-168854330277 : Dyadic) * half ^ 39),
        ((-233183390401 : Dyadic) * half ^ 41)⟩,
       ⟨((-163968538767 : Dyadic) * half ^ 38),
        ((-10945756737 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((168854330277 : Dyadic) * half ^ 39),
        ((233183390401 : Dyadic) * half ^ 41)⟩,
       ⟨((-163968538767 : Dyadic) * half ^ 38),
        ((-10945756737 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-112835996685 : Dyadic) * half ^ 40),
        ((548310255341 : Dyadic) * half ^ 41)⟩,
       ⟨((-24714288585 : Dyadic) * half ^ 40),
        ((973443162261 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word29Step54 :
    word29Chunk54.foldl (fun acc a => a.applyPacked acc)
      word29State54 = word29State55 := by decide +kernel

private def word29Chunk55 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word29State56 : PackedMat2 :=
    ⟨⟨⟨((1186707077455 : Dyadic) * half ^ 41),
        ((520766012051 : Dyadic) * half ^ 42)⟩,
       ⟨((-502995446899 : Dyadic) * half ^ 40),
        ((1422685952765 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((769628002105 : Dyadic) * half ^ 41),
        ((1110604896993 : Dyadic) * half ^ 42)⟩,
       ⟨((21423329045 : Dyadic) * half ^ 38),
        ((-242377287025 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((676491092009 : Dyadic) * half ^ 41),
        ((598241369745 : Dyadic) * half ^ 42)⟩,
       ⟨((-54264225623 : Dyadic) * half ^ 38),
        ((-941014634465 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((450959970357 : Dyadic) * half ^ 41),
        ((-2192697971253 : Dyadic) * half ^ 42)⟩,
       ⟨((121465747801 : Dyadic) * half ^ 38),
        ((180716183657 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word29Step55 :
    word29Chunk55.foldl (fun acc a => a.applyPacked acc)
      word29State55 = word29State56 := by decide +kernel

private def word29Chunk56 : List Letter := [.t, .h]
private def word29State57 : PackedMat2 :=
    ⟨⟨⟨((407842727261 : Dyadic) * half ^ 40),
        ((244541884945 : Dyadic) * half ^ 39)⟩,
       ⟨((832531619895 : Dyadic) * half ^ 41),
        ((-588688763079 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((294919442471 : Dyadic) * half ^ 41),
        ((-208539537675 : Dyadic) * half ^ 41)⟩,
       ⟨((295077166435 : Dyadic) * half ^ 40),
        ((-417302130719 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-294919442471 : Dyadic) * half ^ 41),
        ((208539537675 : Dyadic) * half ^ 41)⟩,
       ⟨((295077166435 : Dyadic) * half ^ 40),
        ((-417302130719 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((407842727261 : Dyadic) * half ^ 40),
        ((244541884945 : Dyadic) * half ^ 39)⟩,
       ⟨((-832531619895 : Dyadic) * half ^ 41),
        ((588688763079 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word29Step56 :
    word29Chunk56.foldl (fun acc a => a.applyPacked acc)
      word29State56 = word29State57 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word29_check : check word29 29 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word29 = word29State57.toMatrix := by
    unfold evalRingPacked
    change ((
      word29Chunk0 ++ word29Chunk1 ++ word29Chunk2 ++ word29Chunk3 ++
      word29Chunk4 ++ word29Chunk5 ++ word29Chunk6 ++ word29Chunk7 ++
      word29Chunk8 ++ word29Chunk9 ++ word29Chunk10 ++ word29Chunk11 ++
      word29Chunk12 ++ word29Chunk13 ++ word29Chunk14 ++ word29Chunk15 ++
      word29Chunk16 ++ word29Chunk17 ++ word29Chunk18 ++ word29Chunk19 ++
      word29Chunk20 ++ word29Chunk21 ++ word29Chunk22 ++ word29Chunk23 ++
      word29Chunk24 ++ word29Chunk25 ++ word29Chunk26 ++ word29Chunk27 ++
      word29Chunk28 ++ word29Chunk29 ++ word29Chunk30 ++ word29Chunk31 ++
      word29Chunk32 ++ word29Chunk33 ++ word29Chunk34 ++ word29Chunk35 ++
      word29Chunk36 ++ word29Chunk37 ++ word29Chunk38 ++ word29Chunk39 ++
      word29Chunk40 ++ word29Chunk41 ++ word29Chunk42 ++ word29Chunk43 ++
      word29Chunk44 ++ word29Chunk45 ++ word29Chunk46 ++ word29Chunk47 ++
      word29Chunk48 ++ word29Chunk49 ++ word29Chunk50 ++ word29Chunk51 ++
      word29Chunk52 ++ word29Chunk53 ++ word29Chunk54 ++ word29Chunk55 ++
      word29Chunk56
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word29Step0, word29Step1, word29Step2, word29Step3, word29Step4,
      word29Step5, word29Step6, word29Step7, word29Step8, word29Step9,
      word29Step10, word29Step11, word29Step12, word29Step13, word29Step14,
      word29Step15, word29Step16, word29Step17, word29Step18, word29Step19,
      word29Step20, word29Step21, word29Step22, word29Step23, word29Step24,
      word29Step25, word29Step26, word29Step27, word29Step28, word29Step29,
      word29Step30, word29Step31, word29Step32, word29Step33, word29Step34,
      word29Step35, word29Step36, word29Step37, word29Step38, word29Step39,
      word29Step40, word29Step41, word29Step42, word29Step43, word29Step44,
      word29Step45, word29Step46, word29Step47, word29Step48, word29Step49,
      word29Step50, word29Step51, word29Step52, word29Step53, word29Step54,
      word29Step55, word29Step56]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
