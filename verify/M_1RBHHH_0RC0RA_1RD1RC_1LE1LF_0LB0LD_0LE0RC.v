From Coq Require Import String List PeanoNat Lia.
From BusyCoq Require Import Individual62.
Import ListNotations.

Open Scope list_scope.
Open Scope sym_scope.
Open Scope nat_scope.

Definition tm := Eval compute in
  (TM_from_str "1RB---_0RC0RA_1RD1RC_1LE1LF_0LB0LD_0LE0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive Sym3 : Type := V0 | V1 | V2.

Fixpoint encL (w : list nat) : side :=
  match w with
  | [] => 1%sym >> 0inf%sym
  | 0 :: w' => 1%sym >> (1%sym >> (0%sym >> encL w'))
  | S n :: w' => 1%sym >> ([0]%sym^^(S n) *> encL w')
  end.

Lemma encL_head (w : list nat) : hd (encL w) = 1%sym.
Proof.
  destruct w as [| [| n] w']; reflexivity.
Qed.

Definition bumpW (w : list nat) : list nat :=
  match w with
  | [] => []
  | 0 :: w' => 1 :: 1 :: w'
  | S n :: w' => S (S n) :: w'
  end.

Lemma encL_bumpW (w : list nat) :
  1%sym >> (0%sym >> tl (encL w)) = encL (bumpW w).
Proof.
  destruct w as [| [| n] w']; cbn; [| reflexivity | reflexivity].
  rewrite <- const_unfold; reflexivity.
Qed.

Fixpoint encR (v : list Sym3) : side :=
  match v with
  | [] => 0inf%sym
  | V0 :: v' => 0%sym >> encR v'
  | V1 :: v' => 1%sym >> (0%sym >> encR v')
  | V2 :: v' => 1%sym >> (1%sym >> (0%sym >> encR v'))
  end.

Inductive GoodVA : nat -> list Sym3 -> Prop :=
  | GoodVA_zero : GoodVA 0 [V0]
  | GoodVA_z001 {a v} : GoodVA a (V0 :: v) -> GoodVA 0 (V0 :: V0 :: V1 :: v)
  | GoodVA_z01 {a v} : GoodVA a (V0 :: v) -> GoodVA (S a) (V0 :: V1 :: v)
  | GoodVA_z02 {a v} : GoodVA a (V0 :: v) -> GoodVA 0 (V0 :: V2 :: v).

Inductive GoodCD : nat -> list Sym3 -> Prop :=
  | GoodCD_nil : GoodCD 0 []
  | GoodCD_z01 {a v} : GoodVA a (V0 :: v) -> GoodCD 0 (V0 :: V1 :: v)
  | GoodCD_z1 {b v} : GoodCD b v -> GoodCD (S b) (V1 :: v).

Lemma GoodVA_cons0 {b : nat} {v : list Sym3} (H : GoodCD b v) : GoodVA b (V0 :: v).
Proof.
  induction H as [| a v hv | b v hv IH].
  - exact GoodVA_zero.
  - exact (GoodVA_z001 hv).
  - exact (GoodVA_z01 IH).
Qed.

Inductive SafeW : nat -> list nat -> Prop :=
  | SafeW_nil {b} : SafeW b []
  | SafeW_z0 {b w} : SafeW 0 w -> SafeW b (0 :: w)
  | SafeW_z1 {b w} : SafeW (S b) w -> SafeW b (1 :: w)
  | SafeW_z2 {b w} : SafeW b w -> SafeW b (2 :: w)
  | SafeW_z3 {b k w} : SafeW b (S (S k) :: w) -> SafeW (S b) (S (S (S k)) :: w).

Lemma SafeW_mono_aux {b : nat} {w : list nat} (hw : SafeW b w) :
  forall d, b <= d -> SafeW d w.
Proof.
  induction hw as [b | b w hw0 _ | b w _ IH | b w _ IH | b k w _ IH]; intros d hd.
  - exact SafeW_nil.
  - exact (SafeW_z0 hw0).
  - exact (SafeW_z1 (IH (S d) ltac:(lia))).
  - exact (SafeW_z2 (IH d hd)).
  - destruct d as [| d']; [lia |].
    exact (SafeW_z3 (IH d' ltac:(lia))).
Qed.

Lemma SafeW_mono {b b' : nat} (h : b <= b') {w : list nat} (hw : SafeW b w) : SafeW b' w.
Proof. exact (SafeW_mono_aux hw b' h). Qed.

Lemma bumpW_safe {b : nat} {w : list nat} (hw : SafeW b w) : SafeW (S b) (bumpW w).
Proof.
  destruct hw as [b | b w hw0 | b w hw1 | b w hw2 | b k w hw3]; cbn [bumpW].
  - exact SafeW_nil.
  - exact (SafeW_z1 (SafeW_z1 (SafeW_mono (Nat.le_0_l _) hw0))).
  - exact (SafeW_z2 hw1).
  - exact (SafeW_z3 (k := 0) (SafeW_z2 hw2)).
  - exact (SafeW_z3 (k := S k) (SafeW_z3 hw3)).
Qed.

Inductive SafeWA : nat -> list nat -> Prop :=
  | SafeWA_nil {a} : SafeWA a []
  | SafeWA_z0 {a w} : SafeW 0 w -> SafeWA a (0 :: w)
  | SafeWA_z1 {a w} : SafeW a w -> SafeWA a (1 :: w).

Lemma SafeWA_succ_to_SafeW {a : nat} {w : list nat} (hw : SafeWA (S a) w) : SafeW a w.
Proof.
  inverts hw as hw0; [exact SafeW_nil | exact (SafeW_z0 hw0) | exact (SafeW_z1 hw0)].
Qed.

Lemma SafeWA_zero_to_SafeW0 {w : list nat} (hw : SafeWA 0 w) : SafeW 0 w.
Proof.
  inverts hw as hw0; [exact SafeW_nil | exact (SafeW_z0 hw0) | exact (SafeW_z1 (SafeW_mono (Nat.le_0_l _) hw0))].
Qed.

Inductive SymMode : Type := modeC | modeD | modeA.

Definition evalSym (m : SymMode) (w : list nat) (v : list Sym3) : Q * tape :=
  match m with
  | modeC => encL w <{{E}} encR v
  | modeD => (1%sym >> encL w) <{{B}} (0%sym >> encR v)
  | modeA => encL w {{C}}> encR v
  end.

Inductive GoodSym : Q * tape -> Prop :=
  | GoodSym_mkC {b w v} : SafeW b w -> GoodCD b v -> GoodSym (evalSym modeC w v)
  | GoodSym_mkD {b w v} : SafeW (S b) w -> GoodCD b v -> GoodSym (evalSym modeD w v)
  | GoodSym_mkA {a w v} : SafeWA a w -> GoodVA a v -> GoodSym (evalSym modeA w v).

Ltac run_sym :=
  cbn [evalSym encL encR lpow app Str_app hd tl];
  simpl_tape;
  repeat rewrite encL_head;
  start_progress;
  repeat (
    repeat rewrite encL_head;
    cbn [hd tl];
    try solve [try rewrite encL_bumpW; simpl_tape; finish];
    step
  );
  try rewrite encL_bumpW;
  simpl_tape;
  finish.

Lemma step_sym_closed (cfg : Q * tape) (h : GoodSym cfg) :
  exists cfg', GoodSym cfg' /\ cfg -->+ cfg'.
Proof.
  destruct h as [b w v hw hv | b w v hw hv | a w v hw hv].
  - destruct hw as [b | b w' hw' | b w' hw' | b w' hw' | b0 k w' hw'].
    + exists (evalSym modeA [] (V0 :: v)).
      split; [exact (GoodSym_mkA SafeWA_nil (GoodVA_cons0 hv)) | run_sym].
    + exists (evalSym modeC w' (V0 :: V1 :: v)).
      split; [exact (GoodSym_mkC hw' (GoodCD_z01 (GoodVA_cons0 hv))) | run_sym].
    + exists (evalSym modeC w' (V1 :: v)).
      split; [exact (GoodSym_mkC hw' (GoodCD_z1 hv)) | run_sym].
    + exists (evalSym modeD (bumpW w') v).
      split; [exact (GoodSym_mkD (bumpW_safe hw') hv) | run_sym].
    + inverts hv as hvt.
      exists (evalSym modeA (1 :: S (S k) :: w') (V0 :: v0)).
      split; [exact (GoodSym_mkA (SafeWA_z1 hw') (GoodVA_cons0 hvt)) | run_sym].
  - destruct hv as [| a vt hvt | b' vt hvt].
    + exists (evalSym modeC (1 :: w) [V1; V1]).
      split; [exact (GoodSym_mkC (SafeW_z1 (SafeW_mono (b := 1) (b' := 3) ltac:(lia) hw)) (GoodCD_z1 (GoodCD_z1 GoodCD_nil))) | run_sym].
    + exists (evalSym modeA (1 :: 1 :: w) (V0 :: vt)).
      split; [exact (GoodSym_mkA (SafeWA_z1 (SafeW_mono (Nat.le_0_l _) (SafeW_z1 hw))) hvt) | run_sym].
    + exists (evalSym modeD (1 :: w) vt).
      split; [exact (GoodSym_mkD (SafeW_z1 hw) hvt) | run_sym].
  - inverts hv as hvt.
    + inverts hw as hw'.
      * exists (evalSym modeA [] [V0; V2; V1]).
        split; [exact (GoodSym_mkA SafeWA_nil (GoodVA_z02 (GoodVA_z01 GoodVA_zero))) | run_sym].
      * exists (evalSym modeA (1 :: 2 :: w0) [V0]).
        split; [exact (GoodSym_mkA (SafeWA_z1 (SafeW_z2 hw')) GoodVA_zero) | run_sym].
      * exists (evalSym modeC w0 [V0; V1; V1]).
        split; [exact (GoodSym_mkC hw' (GoodCD_z01 (GoodVA_z01 GoodVA_zero))) | run_sym].
    + inverts hw as hw'.
      * exists (evalSym modeA [] (V0 :: V2 :: V2 :: v0)).
        split; [exact (GoodSym_mkA SafeWA_nil (GoodVA_z02 (GoodVA_z02 hvt))) | run_sym].
      * exists (evalSym modeA (0 :: 2 :: w0) (V0 :: v0)).
        split; [exact (GoodSym_mkA (SafeWA_z0 (SafeW_z2 hw')) hvt) | run_sym].
      * exists (evalSym modeC w0 (V0 :: V1 :: V2 :: v0)).
        split; [exact (GoodSym_mkC hw' (GoodCD_z01 (GoodVA_z02 hvt))) | run_sym].
    + exists (evalSym modeA (1 :: w) (V0 :: v0)).
      split; [exact (GoodSym_mkA (SafeWA_z1 (SafeWA_succ_to_SafeW hw)) hvt) | run_sym].
    + exists (evalSym modeA (0 :: w) (V0 :: v0)).
      split; [exact (GoodSym_mkA (SafeWA_z0 (SafeWA_zero_to_SafeW0 hw)) hvt) | run_sym].
Qed.

Lemma init_reaches_sym : c0 -->* evalSym modeC [] [V1; V1].
Proof.
  cbn [evalSym encL encR hd tl].
  simpl_tape.
  execute.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init_reaches_sym |].
  eapply progress_nonhalt; [exact step_sym_closed |].
  exact (GoodSym_mkC SafeW_nil (GoodCD_z1 (GoodCD_z1 GoodCD_nil))).
Qed.

Print Assumptions nonhalt.
