(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC25_R3.v. *)
Module SOC25_R3.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Hypothesis ROv3: forall l r n,
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [1;0;0] *> r.
Hypothesis ROv4_0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Hypothesis ROv4_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0;0] len n (rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0] *> rd1 *> RC m).
Definition RC4 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC3,RC4,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC4_Inc len n m l: 1+n<2^(len+1) -> l |> RC4 len (1+n) m -->+ l <| RC4 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC3_Ov len k h i m:
  LC len k |> RC3 h 0 ((m*2+1)*2^i) -->+
  LC len k <| RC3 (h+i+1) (((2^i-1)*2+1)*2^(h+1)-1) m.
Proof. replace (h+i+1) with (i+(h+1)) by lia; solve_rule ROv3. Qed.
Lemma RC3_Ov_blank len k h:
  LC len k |> RC3 h 0 0 -->+ LC len k <| RC (2^(h+1)).
Proof. epose proof (ROv3 _ 0inf h) as H; solve_rule H. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*5+2)) ((k*2+1)*2^(a*5+2)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Lemma RC4_Ov_0 len k a m: k<2^len ->
  LC len k |> RC4 (a*2) 0 m -->+
  LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> RC (m*2+1).
Proof. solve_rule ROv4_0. Qed.
Lemma RC4_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv4_1. Qed.
Lemma RC4_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 0 -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC 0.
Proof. epose proof (ROv4_1 _ 0inf a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
(* b is the bit length, with Size 0 0.  Constructors follow the ROv3 split. *)
Inductive Size: nat -> nat -> Prop :=
| size0: Size 0 0
| sizeS x b i: Size x b -> Size ((x*2+1)*2^i) (b+i+1).
Lemma size_bounds m b: Size m b -> m<2^b<=m*2+1.
Proof. induction 1; [cbn; lia|arith]. Qed.
Lemma size_exists m: exists b, Size m b.
Proof.
  induction m using strong_induction; lowbit_cases m.
  - exists 0; constructor.
  - destruct (H x ltac:(nia)) as [b Hb]; eexists; constructor; exact Hb.
Qed.

Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR3 (len k h n m:nat) | cfgR4 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
| cfgR4 len k h n m => LC len k |> RC4 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR4 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR3 len k h n m => exists b, Size m b /\ 1<=len /\ k<2^len /\
    n<2^(h+1) /\ n+(2^b-1)*2^(h+1)<=k /\ k-n+2^(h+1)<2^len*2
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)); lia.
    + eexists (cfgR4 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); lia.
    + destruct (size_exists x) as [b Hb].
      eexists (cfgR3 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; exists b; split; [exact Hb|].
      pose proof (size_bounds _ _ Hb).
      pose proof (append_bounds len k (n'*5+3) ltac:(lia)); arith.
  - destruct HP as [b [Hb HP]]; destruct n as [|n].
    2: { destruct k as [|k]; [nia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; exists b; split; [exact Hb|lia]. }
    destruct Hb as [|m b i Hb].
    + eexists (cfgL _ _ _); split; [apply RC3_Ov_blank|cbn [P]; arith].
    + destruct k as [|k]; [arith|].
      eexists (cfgR3 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC3_Ov|].
        apply progress_evstep; apply LC_Inc; lia.
      * cbn [P]; exists b; split; [exact Hb|arith].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR4 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC4_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+1) ltac:(lia)); lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RC4_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)); lia.
      * eexists (cfgR4 _ _ _ _ _); split; [apply RC4_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros H HP; eapply multistep_nonhalt; [exact H|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
(* ES_v2 only includes the corresponding rotations for words of length <=6. *)
Lemma lpow_unrotate_10 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::=
  rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 || rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 || rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_10.
End SOC25_R3.

(* SOC25_R3.TM26 *)
Module TM26.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC25_R3.

Definition tm := Eval compute in (TM_from_str "1RB1RB_1RC1LB_1LD1RE_1LA0LD_1RF0RC_1RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{B}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [1;0;0] *> r.
Proof. es. Qed.
Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 6 24 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=B) (QR:=C) (len:=6) (k:=24) (n:=O).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv3|exact ROv4_0|exact ROv4_1|exact ROv'_0|exact ROv'_1|
    exact init|cbn [Counter.P]; lia].
Qed.
End TM26.

(* SOC25_R3.TM27 *)
Module TM27.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC25_R3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC---_1RD1RD_1RE1LD_1LF1RA_1LC0LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [1;0;0] *> r.
Proof. es. Qed.
Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 5 20 <| Counter.RC 0.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=D) (QR:=E) (len:=5) (k:=20) (n:=O).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv3|exact ROv4_0|exact ROv4_1|exact ROv'_0|exact ROv'_1|
    exact init|cbn [Counter.P]; lia].
Qed.
End TM27.

(* SOC25_R3.TM28 *)
Module TM28.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC25_R3.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1RA_1RF0RB_1RD---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [1;0;0] *> r.
Proof. es. Qed.
Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 4 7 <| Counter.RC 4.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=A) (QR:=B) (len:=4) (k:=7) (n:=4).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv3|exact ROv4_0|exact ROv4_1|exact ROv'_0|exact ROv'_1|
    exact init|cbn [Counter.P]; lia].
Qed.
End TM28.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC25_R3zero.v. *)
Module SOC25_R3zero.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{QR}}> r) (at level 30).

Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Hypothesis ROv1_0: forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Hypothesis ROv3: forall l r n,
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [0;0;0] *> r.
Hypothesis ROv4_0: forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Hypothesis ROv4_1: forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Hypothesis ROv'_0: forall l n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Hypothesis ROv'_1: forall l n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0;0] len n (rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0] *> rd1 *> RC m).
Definition RC4 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0] *> rd1 *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC3,RC4,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC4_Inc len n m l: 1+n<2^(len+1) -> l |> RC4 len (1+n) m -->+ l <| RC4 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC3_Ov len k h i m:
  LC len k |> RC3 h 0 ((m*2+1)*2^i) -->+
  LC len k <| RC3 (h+i+1) (2^(h+i+1+1)-1) m.
Proof. solve_rule ROv3. Qed.
Lemma RC3_Ov_blank len k h:
  LC len k |> RC3 h 0 0 -->+ LC len k <| RC 0.
Proof.
  epose proof (ROv3 (LC len k) 0inf h) as H.
  unfold LC,RC3,RC in *; rw_Bin; cbn [Str_app] in *.
  repeat rewrite <-(const_unfold _ 0) in *.
  rewrite lpow_all0 in H by solve_const0_eq.
  exact H.
Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*5+2)) ((k*2+1)*2^(a*5+2)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Lemma RC4_Ov_0 len k a m: k<2^len ->
  LC len k |> RC4 (a*2) 0 m -->+
  LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> RC (m*2+1).
Proof. solve_rule ROv4_0. Qed.
Lemma RC4_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv4_1. Qed.
Lemma RC4_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 0 -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC 0.
Proof. epose proof (ROv4_1 _ 0inf a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR3 (len k h n m:nat) | cfgR4 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
| cfgR4 len k h n m => LC len k |> RC4 h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR4 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR3 len k h n m => 1<=len /\ n+m*2^(h+2)<k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)); lia.
    + eexists (cfgR4 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); lia.
    + eexists (cfgR3 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [nia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    lowbit_cases m.
    + eexists (cfgL _ _ _); split; [apply RC3_Ov_blank|cbn [P]; arith].
    + destruct k as [|k]; [arith|].
      eexists (cfgR3 _ _ _ _ _); split.
      * eapply progress_evstep_trans; [apply RC3_Ov|].
        apply progress_evstep; apply LC_Inc; lia.
      * cbn [P]; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR4 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC4_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+1) ltac:(lia)); lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RC4_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)); lia.
      * eexists (cfgR4 _ _ _ _ _); split; [apply RC4_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
Qed.

Theorem nonhalt_from len k n:
  c0 -->* to_config (cfgL len k n) -> P (cfgL len k n) -> ~halts tm c0.
Proof.
  intros H HP; eapply multistep_nonhalt; [exact H|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
(* ES_v2 only includes the corresponding rotations for words of length <=6. *)
Lemma lpow_unrotate_10 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::=
  rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 || rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 || rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_10.
End SOC25_R3zero.

(* SOC25_R3zero.TM78 *)
Module TM78.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC25_R3zero.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_1LC0LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. destruct n; es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 5 19 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=A) (len:=5) (k:=19) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv3|exact ROv4_0|exact ROv4_1|exact ROv'_0|exact ROv'_1|
    exact init|cbn [Counter.P]; lia].
Qed.
End TM78.

(* SOC25_R3zero.TM79 *)
Module TM79.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.

Import SOC25_R3zero.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1RD1LC_1LB1RF_1LC0LE_1RA0RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. destruct n; es. Qed.
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [0;0;0] *> r.
Proof. es. Qed.
Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.
Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. intros; st; sr_r; do 5 step1; finish; simpl_rotate; reflexivity. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. intros; st; sr_r; do 11 step1; finish; simpl_rotate; reflexivity. Qed.

Lemma init: c0 -->* Counter.LC 8 144 <| Counter.RC 1.
Proof. cbn [Counter.LC Counter.RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=C) (QR:=D) (len:=8) (k:=144) (n:=1%nat).
  all: first [exact LInc|exact RInc|exact LOv|exact ROv1_0|exact ROv1_1|
    exact ROv3|exact ROv4_0|exact ROv4_1|exact ROv'_0|exact ROv'_1|
    exact init|cbn [Counter.P]; lia].
Qed.
End TM79.

(* TM84 omitted: its old equivalence class is merged with TM78 by
   Eqv_Misc_New.TM71.eqv. See SOC_FT7_CONSOLIDATION.md. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* SOC25_TM34.TM34 *)
Module TM34.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].
Lemma lpow_unrotate_10 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::=
  rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 || rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 || rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_10.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RB_1RD1LC_1LF1RE_1RA0RD_1LC0LF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. destruct n; es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(1+n) *> [0;1;0] *> r.
Proof. es. Qed.

Lemma ROv3'_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1] *> r.
Proof. es. Qed.

Lemma ROv3'_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> r.
Proof. es. Qed.

Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof. es. Qed.

Lemma ROv'_0 l n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+2) <| 0inf.
Proof. es' n & l. Qed.
Lemma ROv'_1 l n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld0 <* ld1^^(n*5+4) <| rd1 *> 0inf.
Proof. es' n & l. Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0;0] len n (rd1 *> RC m).
Definition RC3 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0] *> rd1 *> RC m).
Definition RC4 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0] *> rd1 *> RC m).
Definition RCS len n m := BinDec2 [0] [1] [0;0;0;0] len n ([1;0] *> RC m).
Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1] *> 0inf).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC3,RC4,RCS,RC',RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC1_Inc len n m l: 1+n<2^(len+1) -> l |> RC1 len (1+n) m -->+ l <| RC1 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC3_Inc len n m l: 1+n<2^(len+1) -> l |> RC3 len (1+n) m -->+ l <| RC3 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC4_Inc len n m l: 1+n<2^(len+1) -> l |> RC4 len (1+n) m -->+ l <| RC4 len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RCS_Inc len n m l: 1+n<2^(len+1) -> l |> RCS len (1+n) m -->+ l <| RCS len n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC'_Inc len n l: 1+n<2^(len+1) -> l |> RC' len (1+n) -->+ l <| RC' len n.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov len m i:
  LC len 0 <| RC ((m*2+1)*2^i) -->+ LC len (2^len-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma RC1_Ov_0 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof. solve_rule ROv1_0. Qed.
Lemma RC1_Ov_0_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2) 0 0 -->+ LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC 1.
Proof. epose proof (ROv1_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RC1_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC1 (a*2+1) 0 0 -->+ LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC 0.
Proof. epose proof (ROv1_1 _ 0inf a) as H; solve_rule H. Qed.

Lemma RC3_Ov len k h m:
  LC len k |> RC3 h 0 m -->+ LC len k <| RCS (h+1) (2^(h+1+1)-1) m.
Proof. replace (h+1) with (1+h) by lia; solve_rule ROv3. Qed.
Lemma RCS_Ov_0 len k a i m: k<2^len ->
  LC len k |> RCS (a*2) 0 ((m*2+1)*2^i) -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC1 i ((2^i-1)*2) m.
Proof. solve_rule ROv3'_0. Qed.
Lemma RCS_Ov_0_blank len k a: k<2^len ->
  LC len k |> RCS (a*2) 0 0 -->+
  LC (len+1+a*5) ((k*2+1)*2^(a*5)-1) |> RC 1.
Proof. epose proof (ROv3'_0 _ 0inf a) as H; solve_rule H. Qed.
Lemma RCS_Ov_1 len k a m: k<2^len ->
  LC len k |> RCS (a*2+1) 0 m -->+
  LC (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) |> RC m.
Proof. solve_rule ROv3'_1. Qed.
Lemma RC'_Ov_0 len k a: k<2^len ->
  LC len k |> RC' (a*2) 0 -->+ LC (len+1+(a*5+2)) ((k*2+1)*2^(a*5+2)) <| RC 0.
Proof. epose proof (ROv'_0 _ a) as H; solve_rule H. Qed.
Lemma RC'_Ov_1 len k a: k<2^len ->
  LC len k |> RC' (a*2+1) 0 -->+ LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)) <| RC 1.
Proof. epose proof (ROv'_1 _ a) as H; solve_rule H. Qed.

Lemma RC4_Ov_0 len k a m: k<2^len ->
  LC len k |> RC4 (a*2) 0 m -->+
  LC (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) |> RC (m*2+1).
Proof. solve_rule ROv4_0. Qed.
Lemma RC4_Ov_1 len k a i m: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 ((m*2+1)*2^i) -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof. solve_rule ROv4_1. Qed.
Lemma RC4_Ov_1_blank len k a: k<2^len ->
  LC len k |> RC4 (a*2+1) 0 0 -->+
  LC (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) |> RC 0.
Proof. epose proof (ROv4_1 _ 0inf a) as H; solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma RC1_Incs len k h n m: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> RC1 h (n+k+1) m -->* LC len 0 <| RC1 h n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc RC1_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc RC1_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC1 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) ((2^len-1)*2) |> RC' h ((2^h-1)*2).
Proof.
  rewrite Nat.add_comm; unfold LC,RC1,RC',RC; rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv; cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as H; follow100 H.
  simpl_rotate; simpl_tape; finish.
Qed.
Lemma RC'_Incs len k h n: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC' h n -->* LC len k |> RC' h 0.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RC'_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma corner_case len:
  LC (len+1) 0 <| RC (2^(len+1)) -->+
  LC (len+1+1) (2^len*2) |> RC' len 0.
Proof.
  replace (2^(len+1)) with ((0*2+1)*2^(len+1)) by arith.
  follow10 LC_Ov.
  replace ((2^(len+1)-1)*2) with
    (((0*2+1)*2^len-1)*2+(2^(len+1)-1)+1) by arith.
  follow RC1_Incs; [arith|arith|].
  follow100 LC_Ov'.
  replace ((2^(len+1)-1)*2) with (2^len*2+(2^len-1)*2) by arith.
  follow RC'_Incs; [arith|arith|finish].
Qed.

Close Scope sym.
Inductive Config := cfgL (len k n:nat) | cfgR (len k n:nat)
  | cfgR1 (len k h n m:nat) | cfgR3 (len k h n m:nat) | cfgR4 (len k h n m:nat) | cfgRS (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k n => LC len k <| RC n
| cfgR len k n => LC len k |> RC n
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR3 len k h n m => LC len k |> RC3 h n m
| cfgR4 len k h n m => LC len k |> RC4 h n m
| cfgRS len k h n m => LC len k |> RCS h n m
end.
Definition P x := match x with
| cfgL len k n => 1<=len /\ k<2^len /\ 1<=k+n<2^len*2
| cfgR len k n => 1<=len /\ k<2^len /\ 1<=k+n+1<2^len*2
| cfgR1 len k h n m | cfgR4 len k h n m | cfgRS len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgR3 len k h n m => 1<=len /\ n+m+2^(h+2)<=k<2^len /\ n<2^(h+1)
end.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|len]; [cbn in HP; lia|].
        replace (S len) with (len+1) by lia; divmod2_cases len.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_0; arith.
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|].
              apply progress_evstep; apply RC'_Ov_1; arith.
           ++ cbn [P]; arith.
      * lowbit_cases m; [lia|].
        eexists (cfgR1 _ _ _ _ _); split; [apply LC_Ov|].
        cbn [P]; pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; lowbit_cases m.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_0_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)); lia.
    + eexists (cfgR4 _ _ _ _ _); split; [apply RC1_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov_1_blank; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); lia.
    + eexists (cfgR3 _ _ _ _ _); split; [apply RC1_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [nia|].
      eexists (cfgR3 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC3_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    destruct k as [|k]; [arith|].
    eexists (cfgRS _ _ _ _ _); split.
    + eapply progress_evstep_trans; [apply RC3_Ov|].
      apply progress_evstep; apply LC_Inc; lia.
    + cbn [P]; arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR4 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + eexists (cfgR _ _ _); split; [apply RC4_Ov_0; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+1) ltac:(lia)); lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RC4_Ov_1_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)); lia.
      * eexists (cfgR4 _ _ _ _ _); split; [apply RC4_Ov_1; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5+4) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgRS _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply RCS_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h.
    + lowbit_cases m.
      * eexists (cfgR _ _ _); split; [apply RCS_Ov_0_blank; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)); lia.
      * eexists (cfgR1 _ _ _ _ _); split; [apply RCS_Ov_0; lia|].
        cbn [P]; pose proof (append_bounds len k (n'*5) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
    + eexists (cfgR _ _ _); split; [apply RCS_Ov_1; lia|].
      cbn [P]; pose proof (append_bounds len k (n'*5+3) ltac:(lia)); lia.
Qed.

Lemma init: c0 -->* to_config (cfgL 5 19 1).
Proof. cbn [to_config LC RC]; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|cbn [P]; lia].
Qed.
End TM34.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC25_TM85.v. *)
Module SOC25_TM85.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].
Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC n := BinInc rd1 n.

Definition RP h n r := BinDec2 [0] [1] [0;0;0;0] h n r.
Definition CP h n m := RP h n ([0;1;0;0;0;0] *> RC m).
Definition Val h n m := (m+1)*2^(h+2)-n.
Definition Weight h m := m*2^h.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

Lemma CP_zero h m: CP h 0 m = rd1^^h *> [1;0;1;0;0;0;0] *> RC m.
Proof. unfold CP,RP; rewrite BinDec2_O; reflexivity. Qed.
Lemma CP_full h m:
  CP h (2^(h+1)-1) m = rd0^^h *> [0;0;1;0;0;0;0] *> RC m.
Proof. unfold CP,RP; rewrite BinDec2_full; reflexivity. Qed.

Inductive Num: nat -> nat -> side -> Prop :=
| NumCP h n m: n<2^(h+1) -> Num (Val h n m) (Weight h m) (CP h n m).

Lemma Num_bounds v w r: Num v w r -> w*4<v /\ (0<w -> v<=w*8).
Proof. destruct 1; unfold Val,Weight; destruct m; split; intros; arith. Qed.
Lemma Num_terminal v r: Num v 0 r ->
  exists h n, n<2^(h+1) /\ r=CP h n 0 /\
    v=2^(h+2)-n /\ 2^(h+1)<v<=2^(h+2).
Proof.
  intros H; remember 0%nat as w eqn:Hw in H; destruct H; unfold Weight in Hw.
  assert (m=0%nat) by nia; subst m.
  exists h,n; unfold Val; repeat split; try reflexivity; arith.
Qed.

(* The unconsumed finite high part ends at an arbitrary, untouched suffix.
   Its digits start with the four separating zeroes; this includes adjacent
   marks when p=0.  d is the number of calls until all low digits are one. *)
Notation gd1 := [0;0;0;0;1].
Definition FP h n p m r := RP h n ([0;1] *> BinDec rd0 gd1 p m r).
Inductive Pending (tail:side): nat -> nat -> side -> Prop :=
| PendingFP h n p m: n<2^(h+1) -> m<2^p ->
  Pending tail (h+p) (m*2^(h+2)+n) (FP h n p m tail).

Lemma Pending_end t r tail: Pending tail t 0 r ->
  exists h p, t=h+p /\ r=rd1^^h *> [1;0;1] *> gd1^^p *> tail.
Proof.
  intros H; remember 0%nat as d eqn:Hd in H; destruct H.
  assert (m=0%nat /\ n=0%nat) as [-> ->] by nia.
  exists h,p; split; [reflexivity|].
  unfold FP,RP; rewrite BinDec2_O,BinDec_O; reflexivity.
Qed.

Section Rules.
Variable tm:TM.
Variables QL QR:Q.
Variables qL qR:list Sym.
Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis ROv2: forall l r n m,
  l |> rd1^^n *> [1;0;1;0;0;0;0] *> rd1^^m *> [0] *> r -->+
  l <| [0;0] *> rd0^^(n+m+1) *> [1] *> r.

Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX; finish.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RP_Inc h n r l: 1+n<2^(h+1) ->
  l |> RP h (1+n) r -->+ l <| RP h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma CP_Inc h n m l: 1+n<2^(h+1) ->
  l |> CP h (1+n) m -->+ l <| CP h n m.
Proof. apply RP_Inc. Qed.
Lemma CP_Ov h j q l:
  l |> CP h 0 ((q*2+1)*2^j-1) -->+
  l <| CP (h+j+1) (2^(h+j+2)-1) q.
Proof.
  rewrite CP_zero.
  replace (h+j+2) with ((h+j+1)+1) by lia; rewrite CP_full.
  unfold RC; rewrite BinInc_mulpow2sub1.
  follow10 ROv2; finish; simpl_rotate; reflexivity.
Qed.

Lemma Num_step v w r l: Num v w r ->
  exists w' r', Num (v+1) w' r' /\ w'<=w /\ l |> r -->+ l <| r'.
Proof.
  destruct 1 as [h [|n] m HN].
  - remember (m+1) as u eqn:HU; destruct (lowbit_cases' u) as [|q j]; [lia|].
    assert (HM: m=(q*2+1)*2^j-1) by lia.
    exists (Weight (h+j+1) q),(CP (h+j+1) (2^(h+j+2)-1) q); split.
    + applys_eq (NumCP (h+j+1) (2^(h+j+2)-1) q ltac:(arith));
        unfold Val; arith.
    + split; [unfold Weight; rewrite HM; arith|].
      rewrite HM; apply CP_Ov.
  - exists (Weight h m),(CP h n m); split.
    + applys_eq (NumCP h n m ltac:(lia)); unfold Val; arith.
    + split; [lia|]; apply CP_Inc; lia.
Qed.

Lemma Num_increments len k v w r: k<2^len -> Num v w r ->
  exists w' r', Num (v+k+1) w' r' /\ w'<=w /\
    LC len k |> r -->+ LC len 0 <| r'.
Proof.
  gen v w r; induction k; intros v w r HK HN.
  - rewrite Nat.add_0_r; apply Num_step,HN.
  - destruct (Num_step _ _ _ (LC len (S k)) HN) as [w1 [r1 [HN1 [HW1 HE1]]]].
    destruct (IHk _ _ _ ltac:(lia) HN1) as [w2 [r2 [HN2 [HW2 HE2]]]].
    exists w2,r2; split.
    + applys_eq HN2; flia.
    + split; [lia|]. follow11 HE1.
      change (LC len (1+k) <| r1 -->+ LC len 0 <| r2).
      eapply progress_trans; [apply LC_Inc; lia|exact HE2].
Qed.
Lemma Finish_num len k v w r: k<2^len -> w*8<v+k+1 -> Num v w r ->
  exists r', Num (v+k+1) 0 r' /\ LC len k |> r -->+ LC len 0 <| r'.
Proof.
  intros HK HB HN; destruct (Num_increments _ _ _ _ _ HK HN) as [w' [r' [HN' [HW HE]]]].
  assert (w'=0%nat) by (pose proof (Num_bounds _ _ _ HN'); lia).
  subst w'; eauto.
Qed.
Lemma Finish_left len k v w r: 0<k<2^len -> w*8<v+k -> Num v w r ->
  exists r', Num (v+k) 0 r' /\ LC len k <| r -->+ LC len 0 <| r'.
Proof.
  intros HK HB HN; destruct k; [lia|].
  destruct (Finish_num len k v w r ltac:(lia) ltac:(lia) HN) as [r' [HN' HE]].
  exists r'; split; [applys_eq HN'; flia|].
  eapply progress_trans; [apply LC_Inc; lia|exact HE].
Qed.

Lemma RP_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RP h n r -->* LC len k |> RP h 0 r.
Proof.
  gen k; induction n; intros k HK Hn; [finish|].
  eapply evstep_trans; [apply progress_evstep,RP_Inc; lia|].
  rewrite Nat.add_succ_r.
  eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
  follow IHn; try lia; finish.
Qed.
Lemma Low_run0 len k h r: k+(2^(h+1)-1)<2^len ->
  LC len (k+(2^(h+1)-1)) |> [0] *> rd0^^h *> r -->*
  LC len k |> rd1^^h *> [1] *> r.
Proof.
  intros HK; epose proof (RP_Incs len k h (2^(h+1)-1) r HK ltac:(arith)) as H.
  unfold RP in H; rewrite BinDec2_O,BinDec2_full in H.
  rewrite lpow_rotate' in H; exact H.
Qed.
Lemma FP_Ov h j p m l r: m<2^p ->
  l |> FP h 0 (p+1+j) ((m*2+1)*2^j) r -->+
  l <| FP (h+j+1) (2^(h+j+2)-1) p m r.
Proof.
  intros HM; unfold FP,RP; rewrite BinDec2_O.
  replace (h+j+2) with ((h+j+1)+1) by lia; rewrite BinDec2_full.
  rewrite BinDec_mulpow2 by arith; rewrite BinDec_mul2add1 by arith.
  change (l |> rd1^^h *> [1;0;1] *> gd1^^j *> [0;0;0;0] *> [0] *>
    BinDec rd0 gd1 p m r -->+
    l <| rd0^^(h+j+1) *> [0;0;1] *> BinDec rd0 gd1 p m r).
  rewrite (lpow_rotate' [1] [0;0;0;0]).
  follow10 ROv2; finish; simpl_rotate; reflexivity.
Qed.
Lemma Pending_step t d r tail l: Pending tail t (1+d) r ->
  exists r', Pending tail t d r' /\ l |> r -->+ l <| r'.
Proof.
  intros H; remember (1+d) as u eqn:HU in H; destruct H as [h [|n] p m HN HM].
  - lowbit_cases m; [lia|].
    assert (HI:i<p).
    { apply (proj2 (Nat.pow_lt_mono_r_iff 2 i p ltac:(lia))); nia. }
    replace p with (p-i-1+1+i) in HM |- * by lia.
    exists (FP (h+i+1) (2^(h+i+2)-1) (p-i-1) x tail); split.
    + applys_eq (PendingFP tail (h+i+1) (2^(h+i+2)-1) (p-i-1) x
        ltac:(arith) ltac:(arith)); arith.
    + apply FP_Ov; arith.
  - exists (FP h n p m tail); split.
    + applys_eq (PendingFP tail h n p m ltac:(lia) HM); flia.
    + unfold FP; apply RP_Inc; lia.
Qed.
Lemma Pending_run len k t d r tail: k+d<2^len -> Pending tail t d r ->
  exists r', Pending tail t 0 r' /\ LC len (k+d) |> r -->* LC len k |> r'.
Proof.
  gen r; induction d; intros r HK HP.
  - exists r; split; [exact HP|finish].
  - destruct (Pending_step _ _ _ _ (LC len (k+S d)) HP) as [r1 [HP1 HE1]].
    destruct (IHd _ ltac:(lia) HP1) as [r2 [HP2 HE2]].
    exists r2; split; [exact HP2|].
    eapply evstep_trans; [apply progress_evstep,HE1|].
    rewrite Nat.add_succ_r.
    eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|exact HE2].
Qed.

Hypothesis R24: forall l r h,
  l |> rd1^^h *> [1;0;1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(h+1) *> [0;0;0;0;1] *> r.
Hypothesis ROv22: forall l r h p,
  l |> rd1^^h *> [1;0;1;0;0;0;0] *> rd1^^p *> [1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(h+p+2) *> [0;0;0;0;1] *> r.

Lemma Pending_collision t r tail l: Pending ([0;1;0;0;0;0;0] *> tail) t 0 r ->
  l |> r -->+ l <| rd0^^(t+1) *> [0;0;0;0;1] *> tail.
Proof.
  intros H; destruct (Pending_end _ _ _ H) as [h [p [-> ->]]].
  destruct p.
  - cbn [lpow]; rewrite Nat.add_0_r; apply R24.
  - rewrite lpow_S.
    change (l |> rd1^^h *> [1;0;1;0;0;0;0] *> [1] *> gd1^^p *>
      [0;1;0;0;0;0;0] *> tail -->+
      l <| rd0^^(h+S p+1) *> [0;0;0;0;1] *> tail).
    rewrite <-(lpow_rotate' [0;0;0;0] [1]).
    replace (h+S p+1) with (h+p+2) by lia; apply ROv22.
Qed.

Hypothesis LOv1: forall r len j,
  ldh <* ld1^^len <| rd1^^(1+j) *> [0] *> r -->+
  ldh <* ld0^^len <* ld1^^2 |> [0;0] *> rd0^^j *> [1] *> r.
Hypothesis LOvTerminal: forall len h,
  ldh <* ld1^^len <| rd1^^h *> [1;0;1] *> 0inf -->+
  ldh <* ld0^^len <* ld1 <* ld0 <| rd0^^h *> [0;0;0;0;1] *> 0inf.

Lemma LC_reset len:
  LC (len+2) (2^(len+2)-4) = ldh <* ld0^^len <* ld1^^2.
Proof.
  unfold LC; replace (2^(len+2)-4) with ((2^len-1)*2^2) by arith.
  rewrite BinDec_mulpow2 by arith; rewrite BinDec_full; reflexivity.
Qed.
Lemma LC_reset_terminal len:
  LC (len+2) (2^(len+2)-3) = ldh <* ld0^^len <* ld1 <* ld0.
Proof.
  unfold LC; replace (len+2) with (len+1+1) by lia.
  replace (2^(len+1+1)-3) with (((2^len-1)*2)*2+1) by arith.
  rewrite BinDec_mul2add1 by arith; rewrite BinDec_mul2 by arith.
  rewrite BinDec_full; reflexivity.
Qed.
Lemma Marked_enter len j p m: m<2^p ->
  LC len 0 <| CP (p+(1+j)) ((m*2+1)*2^(1+j)) 0 -->+
  LC (len+2) (2^(len+2)-4) |>
    FP j (2^(j+1)-1) p m ([0;1;0;0;0;0;0] *> 0inf).
Proof.
  intros HM; rewrite LC_reset; unfold LC,CP,FP,RP,RC; rewrite BinDec_O,BinInc_O.
  rewrite BinDec2_mulpow2 by arith; rewrite BinDec2_full.
  follow10 LOv1; finish; simpl_rotate; repeat rewrite <-(const_unfold _ 0); reflexivity.
Qed.

Lemma Marked_prepare len h n: h<len -> n<2^h ->
  LC len 0 <| CP h (n*2) 0 -->+
  LC (len+2) (2^(len+2)-n*2-3) <| rd0^^h *> [0;0;0;0;1] *> 0inf.
Proof.
  intros HL HN; lowbit_cases n.
  - rewrite Nat.mul_0_l,Nat.sub_0_r,LC_reset_terminal,CP_zero.
    unfold LC,RC; rewrite BinDec_O,BinInc_O.
    follow_rule (LOvTerminal len h).
  - assert (HI:i<h).
    { apply (proj2 (Nat.pow_lt_mono_r_iff 2 i h ltac:(lia))); nia. }
    assert (HH:h=(h-i-1)+(1+i)) by lia.
    assert (HX:x<2^(h-i-1)) by (rewrite HH in HN; arith).
    assert (HC:2^h<=2^len) by (apply Nat.pow_le_mono_r; lia).
    set (d:= (x*2+1)*2^i*2-1).
    set (k:= 2^(len+2)-(x*2+1)*2^i*2-3).
    assert (HK:k+d=2^(len+2)-4) by (unfold k,d; arith).
    assert (HP:Pending ([0;1;0;0;0;0;0] *> 0inf) (h-1) d
      (FP i (2^(i+1)-1) (h-i-1) x ([0;1;0;0;0;0;0] *> 0inf))).
    { applys_eq (PendingFP ([0;1;0;0;0;0;0] *> 0inf) i (2^(i+1)-1) (h-i-1) x ltac:(arith) HX);
        unfold d; arith. }
    destruct (Pending_run (len+2) k (h-1) d _ _ ltac:(rewrite HK; arith) HP)
      as [r [HP' HE]].
    eapply progress_evstep_trans.
    + applys_eq (Marked_enter len i (h-i-1) x HX).
      rewrite Nat.pow_add_r; cbn [Nat.pow]; flia.
    + rewrite <-HK; eapply evstep_trans; [exact HE|].
      replace h with (h-1+1) at 1 by lia.
      apply progress_evstep,Pending_collision,HP'.
Qed.

Lemma Marked_frontier len h n: h<len -> n<2^h ->
  LC len 0 <| CP h (n*2) 0 -->+
  LC (len+2) (2^(len+2)-n*2-2^(h+1)-3) |>
    rd1^^h *> [1;0;0;0;1] *> 0inf.
Proof.
  intros HL HN.
  assert (HC:2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  set (k:=2^(len+2)-n*2-2^(h+1)-3).
  assert (HE:2^(len+2)-n*2-3=1+(k+(2^(h+1)-1))) by (unfold k; arith).
  follow11 (Marked_prepare len h n HL HN); rewrite HE.
  eapply progress_evstep_trans; [apply LC_Inc; unfold k; arith|].
  change (LC (len+2) (k+(2^(h+1)-1)) |> rd0^^h *> [0] *> [0;0;0;1] *> 0inf -->*
    LC (len+2) k |> rd1^^h *> [1] *> [0;0;0;1] *> 0inf).
  rewrite (lpow_rotate' [0;0;0;0] [0]); apply Low_run0; unfold k; arith.
Qed.

Lemma LC_app10 len k s: k<2^len ->
  LC (len+1+s) ((k*2+1)*2^s) = LC len k <* ld0 <* ld1^^s.
Proof.
  intros HK; unfold LC; rewrite BinDec_mulpow2 by arith.
  rewrite BinDec_mul2add1 by arith; reflexivity.
Qed.
Lemma LC_app01 len k s: k<2^len ->
  LC (len+1+s) ((k*2+1)*2^s-1) = LC len k <* ld1 <* ld0^^s.
Proof. intros HK; unfold LC; rewrite BinDec_mulpow2sub1 by arith; reflexivity. Qed.

Lemma RC_Drain len k n: k<2^len ->
  LC len k |> RC n -->+ LC len 0 <| RC (n+k+1).
Proof.
  gen n; induction k; intros n HK.
  - applys_eq (RC_Inc n (LC len 0)); flia.
  - follow11 RC_Inc.
    eapply progress_trans; [apply LC_Inc; lia|].
    applys_eq (IHk (1+n) ltac:(lia)); flia.
Qed.
Lemma RC_Drain_left len k n: 0<k<2^len ->
  LC len k <| RC n -->+ LC len 0 <| RC (n+k).
Proof.
  intros HK; destruct k; [lia|].
  eapply progress_trans; [apply LC_Inc; lia|].
  applys_eq (RC_Drain len k n ltac:(lia)); flia.
Qed.

Inductive P: (Q*tape) -> Prop :=
| POrd len n: 3<=len -> n<2^len -> P (LC len 0 <| RC n)
| PMarked len h n: 3<=len -> h<len -> n<2^h -> P (LC len 0 <| CP h (n*2) 0).
Definition ToP c := exists c', P c' /\ c -->+ c'.
Lemma ToP_trans c c': c -->* c' -> ToP c' -> ToP c.
Proof. intros H [c'' [HP HE]]; exists c''; split; [exact HP|eapply evstep_progress_trans; eauto]. Qed.

Lemma P_Num len v r: 3<=len -> v<=2^(len+1) -> (exists j,v=j*2) ->
  Num v 0 r -> P (LC len 0 <| r).
Proof.
  intros HL HV [j ->] HN.
  destruct (Num_terminal _ _ HN) as [h [n [HN' [-> [HV' HB]]]]].
  assert (HH:h+1<len+1).
  { apply (proj2 (Nat.pow_lt_mono_r_iff 2 (h+1) (len+1) ltac:(lia))); lia. }
  divmod2_cases n.
  - apply PMarked; try lia; arith.
  - arith.
Qed.
Lemma ToP_RNum len k v w r: 3<=len -> k<2^len -> w*8<v+k+1 ->
  v+k+1<=2^(len+1) -> (exists j,v+k+1=j*2) -> Num v w r -> ToP (LC len k |> r).
Proof.
  intros HL HK HB HV HP HN; destruct (Finish_num _ _ _ _ _ HK HB HN) as [r' [HN' HE]].
  exists (LC len 0 <| r'); split; [eapply P_Num; eauto|exact HE].
Qed.
Lemma ToP_LNum len k v w r: 3<=len -> 0<k<2^len -> w*8<v+k ->
  v+k<=2^(len+1) -> (exists j,v+k=j*2) -> Num v w r -> ToP (LC len k <| r).
Proof.
  intros HL HK HB HV HP HN; destruct (Finish_left _ _ _ _ _ HK HB HN) as [r' [HN' HE]].
  exists (LC len 0 <| r'); split; [eapply P_Num; eauto|exact HE].
Qed.
Lemma ToP_ROrd len k n: 3<=len -> k<2^len -> n+k+1<2^len -> ToP (LC len k |> RC n).
Proof.
  intros; exists (LC len 0 <| RC (n+k+1)); split; [apply POrd|apply RC_Drain]; lia.
Qed.
Lemma ToP_LOrd len k n: 3<=len -> 0<k<2^len -> n+k<2^len -> ToP (LC len k <| RC n).
Proof.
  intros; exists (LC len 0 <| RC (n+k)); split; [apply POrd|apply RC_Drain_left]; lia.
Qed.

Hypothesis R4even: forall l r a,
  l |> rd1^^(a*2) *> [1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <| r.
Hypothesis R4blank: forall l a,
  l |> rd1^^(a*2+1) *> [1;0;0;0;1] *> 0inf -->+
  l <* ld1 <* ld0^^(a*5+5) <| [0;0;1] *> 0inf.

Lemma Num_001: Num 3 0 ([0;0;1] *> 0inf).
Proof.
  applys_eq (NumCP 0 1 0 ltac:(cbn; lia)); try reflexivity.
  cbn; repeat rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Lemma Marked_exit len k h: 3<=len -> 0<k<2^len ->
  ToP (LC len k |> rd1^^h *> [1;0;0;0;1] *> 0inf).
Proof.
  intros HL HK; divmod2_cases h.
  - eapply ToP_trans.
    + apply progress_evstep; applys_eq (R4even (LC len k) 0inf n').
      cbn [Str_app]; repeat rewrite <-(const_unfold _ 0); reflexivity.
    + rewrite <-(LC_app10 len k (n'*5+3)) by lia.
      replace 0inf with (RC 0) by (unfold RC; rewrite BinInc_O; reflexivity).
      apply ToP_LOrd; arith.
  - eapply ToP_trans; [apply progress_evstep,R4blank|].
    rewrite <-(LC_app01 len k (n'*5+5)) by lia.
    apply ToP_LNum with (v:=3%nat) (w:=0%nat); try arith.
    + exists ((k*2+1)*2^(n'*5+4)+1); arith.
    + apply Num_001.
Qed.
Lemma Marked_closed len h n: 3<=len -> h<len -> n<2^h ->
  ToP (LC len 0 <| CP h (n*2) 0).
Proof.
  intros HL HH HN.
  assert (HC:2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  eapply ToP_trans; [apply progress_evstep,Marked_frontier; eauto|].
  apply Marked_exit; arith.
Qed.

Lemma FP_Incs len k h n p m r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> FP h n p m r -->* LC len k |> FP h 0 p m r.
Proof. apply RP_Incs. Qed.

Lemma FP_run_zero len k h n p r:
  k+((2^p-1)*2^(h+2)+n)<2^len -> n<2^(h+1) ->
  LC len (k+((2^p-1)*2^(h+2)+n)) |> FP h n p (2^p-1) r -->*
  LC len k |> FP (h+p) 0 0 0 r.
Proof.
  gen k h n; induction p; intros k h n HK HN.
  - cbn [Nat.pow Nat.sub Nat.mul] in *; rewrite Nat.add_0_r; apply FP_Incs; assumption.
  - set (b:=k+((2^p-1)*2^(h+3)+(2^(h+2)-1))).
    replace (k+((2^S p-1)*2^(h+2)+n)) with (b+1+n) in HK |- * by (unfold b; arith).
    eapply evstep_trans; [apply FP_Incs; eauto|].
    eapply evstep_trans.
    + apply progress_evstep; applys_eq (FP_Ov h 0 p (2^p-1) (LC len (b+1)) r ltac:(arith));
        rewrite Nat.pow_succ_r'; cbn [Nat.pow]; flia.
    + repeat rewrite Nat.add_0_r; rewrite (Nat.add_comm b 1).
      eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
      applys_eq (IHp k (h+1) (2^(h+2)-1) ltac:(unfold b in HK; arith) ltac:(arith));
        unfold b; flia.
Qed.
Lemma Zero_marked_run len k p r: k+(2^(p+2)-3)<2^len ->
  LC len (k+(2^(p+2)-3)) |> [0;0;1] *> rd0^^p *> r -->*
  LC len k |> rd1^^p *> [1;0;1] *> r.
Proof.
  intros HK; pose proof (FP_run_zero len k 0 1 p r ltac:(arith) ltac:(cbn; lia)) as H.
  unfold FP,RP in H; rewrite BinDec_full,BinDec2_O,BinDec_O in H.
  cbn [BinDec2] in H.
  applys_eq H; rewrite Nat.pow_add_r; cbn [Nat.pow]; flia.
Qed.

Hypothesis R1even: forall l r a,
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1^^2 <| r.
Hypothesis R1odd: forall l r a,
  l |> rd1^^(a*2+1) *> [1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <* ld0 <| r.
Hypothesis R1zero: forall l r a,
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+1) <* ld1 <* ld0 <| [0;0;1] *> r.
Hypothesis R23even1: forall l r a,
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+3) <* ld1^^2 <| r.
Hypothesis R23even0: forall l r a,
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1 <* ld0 <| [0;0;1] *> r.
Hypothesis R23odd: forall l r a,
  l |> rd1^^(a*2+1) *> [1;0;1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+5) |> r.

Definition AuxPre (b:bool) := if b then [0;0;1] else [0].
Definition AuxWord (b:bool) := if b then [1;0;1;1;0;0;0] else [1;1;0;0;0].
Definition AuxCost (b:bool) i := if b then 2^(i+2)-3 else 2^(i+1)-1.

Lemma Aux_frontier b len k i m: k+AuxCost b i<2^len ->
  LC len (k+AuxCost b i) |> AuxPre b *> RC ((m*2+1)*2^i) -->*
  LC len k |> rd1^^i *> AuxWord b *> [0] *> RC m.
Proof.
  destruct b; cbn [AuxPre AuxWord AuxCost]; intros HK;
    unfold RC; rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0].
  - apply Zero_marked_run; exact HK.
  - apply Low_run0; exact HK.
Qed.
Lemma LC_app0100 len k s: k<2^len ->
  LC (len+1+(s+2)) ((k*2+1)*2^(s+2)-4) =
  LC len k <* ld1 <* ld0^^s <* ld1^^2.
Proof.
  intros HK; unfold LC; replace (len+1+(s+2)) with (len+1+s+2) by lia.
  replace ((k*2+1)*2^(s+2)-4) with (((k*2+1)*2^s-1)*2^2) by arith.
  rewrite BinDec_mulpow2 by arith; rewrite BinDec_mulpow2sub1 by arith; reflexivity.
Qed.
Lemma LC_app0101 len k s: k<2^len ->
  LC (len+1+(s+2)) ((k*2+1)*2^(s+2)-3) =
  LC len k <* ld1 <* ld0^^s <* ld1 <* ld0.
Proof.
  intros HK; unfold LC; replace (len+1+(s+2)) with (len+1+s+1+1) by lia.
  replace ((k*2+1)*2^(s+2)-3) with ((((k*2+1)*2^s-1)*2)*2+1) by arith.
  rewrite BinDec_mul2add1 by arith; rewrite BinDec_mul2 by arith.
  rewrite BinDec_mulpow2sub1 by arith; reflexivity.
Qed.
Lemma Aux_odd b len k a r: k<2^len ->
  LC len k |> rd1^^(a*2+1) *> AuxWord b *> r -->+
  LC (len+1+(a*5+(if b then 5 else 4))) ((k*2+1)*2^(a*5+(if b then 5 else 4))) |> r.
Proof.
  destruct b; cbn [AuxWord]; intros HK.
  - rewrite LC_app10 by lia; apply R23odd.
  - follow10 R1odd; rewrite LC_app10 by lia.
    replace (a*5+4) with (a*5+3+1) by lia.
    rewrite <-lpow_add' with (n1:=a*5+3) (n2:=1%nat).
    follow100 (LInc (LC len k <* ld0 <* ld1^^(a*5+3)) r 0); finish; simpl_rotate; reflexivity.
Qed.
Lemma Aux_one b len k a r: k<2^len ->
  LC len k |> rd1^^(a*2) *> AuxWord b *> [0;1;0;0;0;0] *> r -->+
  LC (len+1+(a*5+(if b then 5 else 4))) ((k*2+1)*2^(a*5+(if b then 5 else 4))-5) |>
    [0] *> r.
Proof.
  destruct b; cbn [AuxWord]; intros HK.
  - follow10 R23even1.
    rewrite <-(LC_app0100 len k (a*5+3)) by lia.
    eapply progress_evstep; applys_eq (LC_Inc (len+1+(a*5+5))
      ((k*2+1)*2^(a*5+5)-5) ([0] *> r) ltac:(arith)); repeat (arith || f_equal).
  - follow10 R1even.
    rewrite <-(LC_app0100 len k (a*5+2)) by lia.
    eapply progress_evstep; applys_eq (LC_Inc (len+1+(a*5+4))
      ((k*2+1)*2^(a*5+4)-5) ([0] *> r) ltac:(arith)); repeat (arith || f_equal).
Qed.
Lemma Aux_zero b len k a r: k<2^len ->
  LC len k |> rd1^^(a*2) *> AuxWord b *> [0;0;0;0;0;0] *> r -->+
  LC (len+1+(a*5+(if b then 4 else 3))) ((k*2+1)*2^(a*5+(if b then 4 else 3))-4) |>
    [0;0;1] *> r.
Proof.
  destruct b; cbn [AuxWord]; intros HK.
  - follow10 R23even0.
    rewrite <-(LC_app0101 len k (a*5+2)) by lia.
    eapply progress_evstep; applys_eq (LC_Inc (len+1+(a*5+4))
      ((k*2+1)*2^(a*5+4)-4) ([0;0;1] *> r) ltac:(arith)); repeat (arith || f_equal).
  - follow10 R1zero.
    rewrite <-(LC_app0101 len k (a*5+1)) by lia.
    eapply progress_evstep; applys_eq (LC_Inc (len+1+(a*5+3))
      ((k*2+1)*2^(a*5+3)-4) ([0;0;1] *> r) ltac:(arith)); repeat (arith || f_equal).
Qed.

Lemma Auxiliary_closed m: forall b len k,
  3<=len -> m*4+4<=k -> k+4<2^len ->
  (b=true -> exists j,k=j*2) -> ToP (LC len k |> AuxPre b *> RC m).
Proof.
  induction m using strong_induction; intros b len k HL HM HK HE; lowbit_cases m.
  - unfold RC; rewrite BinInc_O; destruct b; cbn [AuxPre].
    + apply ToP_RNum with (v:=3%nat) (w:=0%nat); try arith.
      * destruct (HE eq_refl) as [j ->]; exists (j+2); lia.
      * apply Num_001.
    + replace ([0] *> 0inf) with (RC 0) by
        (unfold RC; rewrite BinInc_O; apply const_unfold).
      apply ToP_ROrd; lia.
  - set (K:=k-AuxCost b i).
    assert (HC:1<=AuxCost b i /\ K+AuxCost b i=k /\ x*4+4<K /\ K<k).
    { unfold K,AuxCost; destruct b; arith. }
    eapply ToP_trans.
    + replace k with (K+AuxCost b i) at 1 by lia; apply Aux_frontier; lia.
    + divmod2_cases i; rename n' into a.
      * divmod2_cases x; rename n' into q; unfold RC; rw_Bin; cbn [BinaryCounter.d0].
        -- eapply ToP_trans; [apply progress_evstep,Aux_zero; lia|].
           apply (H q ltac:(arith) true); try (destruct b; arith).
           intros _; exists ((K*2+1)*2^(a*5+(if b then 3 else 2))-2); destruct b; arith.
        -- eapply ToP_trans; [apply progress_evstep,Aux_one; lia|].
           apply (H q ltac:(arith) false); try (destruct b; arith); discriminate.
      * eapply ToP_trans; [apply progress_evstep,Aux_odd; lia|].
        apply (H x ltac:(arith) false); try (destruct b; arith); discriminate.
Qed.

Hypothesis LOv0: forall r n,
  ldh <* ld1^^(n+1) <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0;1;0;0;0] *> r.
Hypothesis R21even: forall l r a,
  l |> rd1^^(a*2) *> [1;0;1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+4) <| r.
Hypothesis R21odd: forall l r a b,
  l |> rd1^^(a*2+1) *> [1;0;1;0;0] *> [0;1;0;0;0]^^(1+b) *> [0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+6) <| rd0^^b *> [0;0;1] *> r.

Lemma Ordinary_enter len r: 0<len ->
  LC len 0 <| rd0 *> r -->+ LC len (2^len-2) |> [0;0;1;0;0;0] *> r.
Proof.
  intros HL; destruct len; [lia|]; replace (S len) with (len+1) by lia.
  unfold LC; rewrite BinDec_O.
  replace (2^(len+1)-2) with ((2^len-1)*2) by arith.
  rewrite BinDec_mul2 by arith; rewrite BinDec_full; apply LOv0.
Qed.
Lemma Odd_enter len b q:
  LC len 0 <| RC ((q*2+1)*2^(1+b)-1) -->+
  LC (len+2) (2^(len+2)-4) |> CP b (2^(b+1)-1) q.
Proof.
  rewrite LC_reset,CP_full; unfold LC,RC; rewrite BinDec_O,BinInc_mulpow2sub1.
  follow10 LOv1; finish; simpl_rotate; reflexivity.
Qed.
Lemma Ordinary_zero len: 3<=len -> ToP (LC len 0 <| RC 0).
Proof.
  intros HL; destruct len; [lia|].
  eapply ToP_trans.
  - apply progress_evstep; applys_eq (Ordinary_enter (S len) 0inf ltac:(lia)).
    unfold RC; rewrite BinInc_O; cbn [Str_app]; repeat rewrite <-(const_unfold _ 0); reflexivity.
  - cbn [Str_app]; repeat rewrite <-(const_unfold _ 0).
    apply ToP_RNum with (v:=3%nat) (w:=0%nat); try arith.
    + exists (2^len+1); arith.
    + apply Num_001.
Qed.
Lemma Ordinary_odd len m: 3<=len -> m*2+1<2^len -> ToP (LC len 0 <| RC (m*2+1)).
Proof.
  intros HL HM; remember (m+1) as u eqn:HU; destruct (lowbit_cases' u) as [|q b]; [lia|].
  assert (HE:m*2+1=(q*2+1)*2^(1+b)-1) by arith.
  rewrite HE; eapply ToP_trans; [apply progress_evstep,Odd_enter|].
  apply ToP_RNum with (v:=Val b (2^(b+1)-1) q) (w:=Weight b q);
    try (unfold Val,Weight; arith).
  - exists (2^(len+1)+(q*2+1)*2^b-1); unfold Val; arith.
  - apply NumCP; arith.
Qed.
Lemma Ordinary_even_frontier len i m: (m*2+1)*2^(i+1)<2^len ->
  LC len 0 <| RC ((m*2+1)*2^(i+1)) -->+
  LC len (2^len-2^(i+2)+1) |> rd1^^i *> [1;0;1;0;0;0;1;0;0;0;0] *> RC m.
Proof.
  intros HM.
  assert (HI:i+1<len).
  { apply (proj2 (Nat.pow_lt_mono_r_iff 2 (i+1) len ltac:(lia))); nia. }
  assert (HC:2^(i+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  unfold RC; rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0].
  replace (i+1) with (1+i) by lia; rewrite lpow_S.
  eapply progress_evstep_trans; [apply Ordinary_enter; lia|].
  replace (2^len-2) with ((2^len-2^(i+2)+1)+(2^(i+2)-3)) by arith.
  change (LC len ((2^len-2^(i+2)+1)+(2^(i+2)-3)) |>
    [0;0;1] *> [0;0;0] *> rd0^^i *> [1;0;0;0;0] *> BinInc rd1 m -->*
    LC len (2^len-2^(i+2)+1) |> rd1^^i *> [1;0;1] *> [0;0;0;1;0;0;0;0] *> BinInc rd1 m).
  rewrite <-(lpow_rotate' [0;0] [0;0;0]); apply Zero_marked_run; arith.
Qed.
Lemma R21_odd_num len k a b q: k<2^len ->
  LC len k |> rd1^^(a*2+1) *> [1;0;1;0;0;0;1;0;0;0;0] *> RC ((q*2+1)*2^b-1) -->+
  LC (len+1+(a*5+6)) ((k*2+1)*2^(a*5+6)-1) <| CP b (2^(b+1)-1) q.
Proof.
  intros HK; rewrite LC_app01 by lia; rewrite CP_full.
  unfold RC; rewrite BinInc_mulpow2sub1.
  change (LC len k |> rd1^^(a*2+1) *> [1;0;1;0;0] *> [0;1;0;0;0] *>
    [0] *> rd1^^b *> [0] *> [0;0;0;0] *> BinInc rd1 q -->+
    LC len k <* ld1 <* ld0^^(a*5+6) <| rd0^^b *> [0;0;1;0;0;0;0] *> BinInc rd1 q).
  rewrite <-(lpow_rotate' [1;0;0;0] [0]).
  change (LC len k |> rd1^^(a*2+1) *> [1;0;1;0;0] *> [0;1;0;0;0]^^(1+b) *>
    [0;0] *> [0;0;0;0] *> BinInc rd1 q -->+
    LC len k <* ld1 <* ld0^^(a*5+6) <| rd0^^b *> [0;0;1;0;0;0;0] *> BinInc rd1 q).
  apply R21odd.
Qed.
Lemma Ordinary_even len i m: 3<=len -> (m*2+1)*2^(i+1)<2^len ->
  ToP (LC len 0 <| RC ((m*2+1)*2^(i+1))).
Proof.
  intros HL HM.
  assert (HI:i+1<len).
  { apply (proj2 (Nat.pow_lt_mono_r_iff 2 (i+1) len ltac:(lia))); nia. }
  assert (HC:2^(i+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  set (K:=2^len-2^(i+2)+1).
  assert (HK:0<K /\ K+2<2^len /\ m<K) by (unfold K; destruct m; arith).
  eapply ToP_trans; [apply progress_evstep,Ordinary_even_frontier; eauto|].
  divmod2_cases i; rename n' into a; fold K.
  - eapply ToP_trans.
    + apply progress_evstep; follow10 R21even.
      rewrite <-(LC_app10 len K (a*5+4)) by lia.
      eapply progress_evstep; applys_eq (LC_Inc (len+1+(a*5+4))
        ((K*2+1)*2^(a*5+4)-1) ([0] *> RC m) ltac:(arith)); repeat (arith || f_equal).
    + apply (Auxiliary_closed m false); try arith; discriminate.
  - remember (m+1) as u eqn:HU; destruct (lowbit_cases' u) as [|q b]; [lia|].
    assert (HE:m=(q*2+1)*2^b-1) by lia; rewrite HE.
    eapply ToP_trans; [apply progress_evstep,R21_odd_num; lia|].
    apply ToP_LNum with (v:=Val b (2^(b+1)-1) q) (w:=Weight b q);
      try (unfold Val,Weight; arith).
    + exists ((K*2+1)*2^(a*5+5)+(q*2+1)*2^b); unfold Val; arith.
    + apply NumCP; arith.
Qed.
Lemma P_closed c: P c -> ToP c.
Proof.
  destruct 1.
  - lowbit_cases n.
    + apply Ordinary_zero; assumption.
    + destruct i.
      * cbn [Nat.pow] in *; rewrite Nat.mul_1_r in *; apply Ordinary_odd; assumption.
      * replace (S i) with (i+1) in * by lia; apply Ordinary_even; assumption.
  - apply Marked_closed; assumption.
Qed.

Lemma P_nonhalt c: P c -> ~halts tm c.
Proof.
  intros HP; apply (progress_nonhalt_cond tm (Q*tape) c (fun x=>x) P).
  - intros c' HP'; destruct (P_closed _ HP') as [c'' [HP'' HE]].
    exists c''; auto.
  - exact HP.
Qed.
Theorem nonhalt_from len n: 3<=len -> n<2^len ->
  c0 -->* LC len 0 <| RC n -> ~halts tm c0.
Proof.
  intros HL HN HI; eapply multistep_nonhalt; [exact HI|].
  apply P_nonhalt,POrd; assumption.
Qed.

End Rules.
End SOC25_TM85.

(* SOC25_TM85.TM85 *)
Module TM85.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM85.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RE_1RF1RD_1RC---").

Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1] {{A}}> r) (at level 30).
Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. destruct n; es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(n+1) <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0;1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv2_short l r n m:
  l |> rd1^^n *> [1;0;1;0;0;0;0] *> rd1^^m *> [0] *> r -->+
  l <| [0;0] *> rd0^^(n+m+1) *> [1] *> r.
Proof. es' n m & l r. Qed.
Lemma LOv_1short r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> [0] *> r -->+
  ldh <* ld0^^n <* ld1^^2 |> [0;0] *> rd0^^m *> [1] *> r.
Proof. es' n m & r. Qed.
Lemma R21odd_scan l r a b:
  l |> rd1^^(a*2+1) *> [1;0;1;0;0] *> [0;1;0;0;0]^^(1+b) *> [0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+6) <| rd0^^b *> [0;0;1] *> r.
Proof. es' a b & l r. Qed.
Lemma ROv22 l r n m:
  l |> rd1^^n *> [1;0;1;0;0;0;0] *> rd1^^m *> [1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(n+m+2) *> [0;0;0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma R21even l r a:
  l |> rd1^^(a*2) *> [1;0;1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+4) <| r.
Proof. es' a & l r. Qed.
Lemma R1even l r a:
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1^^2 <| r.
Proof. es' a & l r. Qed.
Lemma R1odd l r a:
  l |> rd1^^(a*2+1) *> [1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <* ld0 <| r.
Proof.
  rewrite <- lpow_add' with (n2:=1%nat).
  st; sr_r; do 4 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
Qed.
Lemma R4even l r a:
  l |> rd1^^(a*2) *> [1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <| r.
Proof. es' a & l r. Qed.
Lemma R24 l r n:
  l |> rd1^^n *> [1;0;1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(n+1) *> [0;0;0;0;1] *> r.
Proof. es' n & l r. Qed.
Lemma R1zero l r a:
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+1) <* ld1 <* ld0 <| [0;0;1] *> r.
Proof. es' a & l r. Qed.
Lemma R4blank l a:
  l |> rd1^^(a*2+1) *> [1;0;0;0;1] *> 0inf -->+
  l <* ld1 <* ld0^^(a*5+5) <| [0;0;1] *> 0inf.
Proof. es' a & l. Qed.

Lemma R23even1 l r a:
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+3) <* ld1^^2 <| r.
Proof. es' a & l r. Qed.
Lemma R23even0 l r a:
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1 <* ld0 <| [0;0;1] *> r.
Proof. es' a & l r. Qed.
Lemma R23odd l r a:
  l |> rd1^^(a*2+1) *> [1;0;1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+5) |> r.
Proof. es' a & l r. Qed.
Lemma LOv_terminal n h:
  ldh <* ld1^^n <| rd1^^h *> [1;0;1] *> 0inf -->+
  ldh <* ld0^^n <* ld1 <* ld0 <| rd0^^h *> [0;0;0;0;1] *> 0inf.
Proof. es' n h. Qed.

Lemma init_zero: c0 -[tm]->* (LC 8 0 <| RC 184).
Proof. unfold LC,RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt_from with (QL:=C) (QR:=A) (len:=8) (n:=184).
  all: try solve [eauto using LInc,RInc,ROv2_short,R24,ROv22,LOv_1short,LOv_terminal,
    R4even,R4blank,R1even,R1odd,R1zero,R23even1,R23even0,R23odd,LOv_0,R21even,R21odd_scan,init_zero].
  all: cbn; lia.
Qed.
End TM85.

(* SOC25_TM85.TM86 *)
Module TM86.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM85.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC---_1RD1LC_1LE1RF_1LC0LE_1RA0RA").

Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1] {{D}}> r) (at level 30).
Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. destruct n; es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(n+1) <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0;1;0;0;0] *> r.
Proof. es. Qed.
Lemma ROv2_short l r n m:
  l |> rd1^^n *> [1;0;1;0;0;0;0] *> rd1^^m *> [0] *> r -->+
  l <| [0;0] *> rd0^^(n+m+1) *> [1] *> r.
Proof. es' n m & l r. Qed.
Lemma LOv_1short r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> [0] *> r -->+
  ldh <* ld0^^n <* ld1^^2 |> [0;0] *> rd0^^m *> [1] *> r.
Proof. es' n m & r. Qed.
Lemma R21odd_scan l r a b:
  l |> rd1^^(a*2+1) *> [1;0;1;0;0] *> [0;1;0;0;0]^^(1+b) *> [0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+6) <| rd0^^b *> [0;0;1] *> r.
Proof. es' a b & l r. Qed.
Lemma ROv22 l r n m:
  l |> rd1^^n *> [1;0;1;0;0;0;0] *> rd1^^m *> [1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(n+m+2) *> [0;0;0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma R21even l r a:
  l |> rd1^^(a*2) *> [1;0;1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+4) <| r.
Proof. es' a & l r. Qed.
Lemma R1even l r a:
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1^^2 <| r.
Proof. es' a & l r. Qed.
Lemma R1odd l r a:
  l |> rd1^^(a*2+1) *> [1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <* ld0 <| r.
Proof.
  rewrite <- lpow_add' with (n2:=1%nat).
  st; sr_r; do 4 (simpl_rotate; step1); finish; simpl_rotate; reflexivity.
Qed.
Lemma R4even l r a:
  l |> rd1^^(a*2) *> [1;0;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+3) <| r.
Proof. es' a & l r. Qed.
Lemma R24 l r n:
  l |> rd1^^n *> [1;0;1;0;1;0;0;0;0;0] *> r -->+
  l <| rd0^^(n+1) *> [0;0;0;0;1] *> r.
Proof. es' n & l r. Qed.
Lemma R1zero l r a:
  l |> rd1^^(a*2) *> [1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+1) <* ld1 <* ld0 <| [0;0;1] *> r.
Proof. es' a & l r. Qed.
Lemma R4blank l a:
  l |> rd1^^(a*2+1) *> [1;0;0;0;1] *> 0inf -->+
  l <* ld1 <* ld0^^(a*5+5) <| [0;0;1] *> 0inf.
Proof. es' a & l. Qed.

Lemma R23even1 l r a:
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;1;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+3) <* ld1^^2 <| r.
Proof. es' a & l r. Qed.
Lemma R23even0 l r a:
  l |> rd1^^(a*2) *> [1;0;1;1;0;0;0;0;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1 <* ld0 <| [0;0;1] *> r.
Proof. es' a & l r. Qed.
Lemma R23odd l r a:
  l |> rd1^^(a*2+1) *> [1;0;1;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(a*5+5) |> r.
Proof. es' a & l r. Qed.
Lemma LOv_terminal n h:
  ldh <* ld1^^n <| rd1^^h *> [1;0;1] *> 0inf -->+
  ldh <* ld0^^n <* ld1 <* ld0 <| rd0^^h *> [0;0;0;0;1] *> 0inf.
Proof. es' n h. Qed.

Lemma init_zero: c0 -[tm]->* (LC 10 0 <| RC 736).
Proof. unfold LC,RC; esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply nonhalt_from with (QL:=C) (QR:=D) (len:=10) (n:=736).
  all: try solve [eauto using LInc,RInc,ROv2_short,R24,ROv22,LOv_1short,LOv_terminal,
    R4even,R4blank,R1even,R1odd,R1zero,R23even1,R23even0,R23odd,LOv_0,R21even,R21odd_scan,init_zero].
  all: cbn; lia.
Qed.
End TM86.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC25_TM91.v. *)
Module SOC25_TM91.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation d := [1;0;0;0;0].
Notation z := [0;0;0;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1] {{QR}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;0;1] {{QR}}> r) (at level 30).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> d^^n *> [0] *> r -->+ l <| z^^n *> [1] *> r.
Hypothesis LOv: forall r n,
  ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |2> [0] *> r.
Hypothesis ROv': forall l r,
  l |2> [0;0] *> r -->+ l <* ld1 |2> r.
Hypothesis ROv'_1: forall l r n,
  l |2> d^^(1+n) *> z *> r -->+ l <* ld1 |> [0;0;0] *> z^^n *> d *> r.
Hypothesis ROv'_0: forall l r,
  l |2> [0] *> d *> r -->+ l <* ld1^^2 |> [1;0] *> r.
Hypothesis ROv2_0_00: forall l r a,
  l |> d^^(a*2) *> [1;0;1;0;0;0;0] *> z *> z *> r -->+
  l <* ld1 <* ld0^^(a*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |> [0;0;0] *> r.
Hypothesis ROv2_0_01: forall l r a,
  l |> d^^(a*2) *> [1;0;1;0;0;0;0] *> z *> d *> r -->+
  l <* ld1 <* ld0^^(a*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |2> [0;0;0] *> r.
Hypothesis ROv2_0_1: forall l r a b,
  l |> d^^(a*2) *> [1;0;1;0;0;0;0] *> d^^(1+b) *> z *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1 <* ld0 <* ld1 |> z^^b *> d *> r.
Hypothesis ROv2_1: forall l r a b,
  l |> d^^(a*2+1) *> [1;0;1;0;0;0;0] *> d^^b *> z *> r -->+
  l <* ld1 <* ld0^^(a*5+3) <* ld1 |> [0;0] *> z^^b *> d *> r.
Hypothesis ROv3_0: forall l r a b,
  l |> d^^(a*2) *> [1;0;0;1;0;0;0;0] *> d^^b *> z *> r -->+
  l <* ld1 <* ld0^^(a*5+2) <* ld1 |> z^^b *> d *> r.
Hypothesis ROv3_1: forall l r a,
  l |> d^^(a*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(a*5+5) |2> [0] *> r.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc d m.
Definition T2 h n m := BinDec2 [0] [1] [0;0;0;0] h n ([0] *> d *> RC m).
Definition T3 h n m := BinDec2 [0] [1] [0;0;0;0] h n ([0;0] *> d *> RC m).
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; try unfold BinaryCounter.d0 in *;
  cbn [List.length List.repeat Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,T2,T3,RC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc l m: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma Mark_Inc l h n r: 1+n<2^(h+1) ->
  l |> BinDec2 [0] [1] [0;0;0;0] h (1+n) r -->+
  l <| BinDec2 [0] [1] [0;0;0;0] h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma LC_Ov len m:
  LC len 0 <| RC m -->+ LC len (2^len-1) |2> [0] *> RC m.
Proof. solve_rule LOv. Qed.

Lemma LC_double len k: k<2^len -> LC (len+1) (k*2) = LC len k <* ld1.
Proof. intros; unfold LC; rw_Bin; try solve[arith]; reflexivity. Qed.

Lemma LC_tail len k q: k<2^len ->
  LC (len+1+q+1) ((k*2+1)*2^(q+1)-2) = LC len k <* ld1 <* ld0^^q <* ld1.
Proof.
  intros; unfold LC.
  replace ((k*2+1)*2^(q+1)-2) with (((k*2+1)*2^q-1)*2) by arith.
  rw_Bin; try solve[arith]; reflexivity.
Qed.
Lemma LC_tail3 len k q: k<2^len ->
  LC (len+1+q+3) ((k*2+1)*2^(q+3)-6) =
  LC len k <* ld1 <* ld0^^q <* ld1 <* ld0 <* ld1.
Proof.
  intros; unfold LC; replace (len+1+q+3) with (len+1+q+1+1+1) by lia.
  replace ((k*2+1)*2^(q+3)-6) with (((((k*2+1)*2^q-1)*2)*2+1)*2) by arith.
  rw_Bin; try solve[arith]; reflexivity.
Qed.
Lemma LC_tail6 len k q: k<2^len ->
  LC (len+1+q+6) ((k*2+1)*2^(q+6)-41) =
  LC len k <* ld1 <* ld0^^q <* ld1 <* ld0 <* ld1 <* ld0^^3.
Proof.
  intros; unfold LC; replace (len+1+q+6) with (len+1+q+1+1+1+3) by lia.
  replace ((k*2+1)*2^(q+6)-41) with
    ((((((k*2+1)*2^q-1)*2)*2+1)*2+1)*2^3-1) by arith.
  rw_Bin; try solve[arith]; reflexivity.
Qed.

Lemma T3_Even len k a b m: k<2^len ->
  LC len k |> T3 (a*2) 0 ((m*2+1)*2^b-1) -->+
  LC (len+1+(a*5+2)+1) ((k*2+1)*2^(a*5+2+1)-2) |> RC ((m*2+1)*2^b).
Proof. intros; rewrite LC_tail by lia; solve_rule ROv3_0. Qed.
Lemma T3_Odd len k a m: k<2^len ->
  LC len k |> T3 (a*2+1) 0 m -->+
  LC (len+1+(a*5+5)) ((k*2+1)*2^(a*5+5)-1) |2> [0] *> RC m.
Proof. solve_rule ROv3_1. Qed.
Lemma T2_Odd len k a b m: k<2^len ->
  LC len k |> T2 (a*2+1) 0 ((m*2+1)*2^b-1) -->+
  LC (len+1+(a*5+3)+1) ((k*2+1)*2^(a*5+3+1)-2) |> T2 b (2^(b+1)-1) m.
Proof. intros; rewrite LC_tail by lia; solve_rule ROv2_1. Qed.
Lemma T2_Even1 len k a b m: k<2^len ->
  LC len k |> T2 (a*2) 0 ((m*2+1)*2^(b+1)-1) -->+
  LC (len+1+(a*5+2)+3) ((k*2+1)*2^(a*5+2+3)-6) |> RC ((m*2+1)*2^b).
Proof.
  intros; rewrite LC_tail3 by lia.
  rewrite (Nat.add_comm b 1); solve_rule ROv2_0_1.
Qed.
Lemma T2_Even00 len k a b m: k<2^len ->
  LC len k |> T2 (a*2) 0 (((m*2+1)*2^b)*2*2) -->+
  LC (len+1+a*5+6) ((k*2+1)*2^(a*5+6)-41) |> T3 b (2^(b+1)-1) m.
Proof. intros; rewrite LC_tail6 by lia; solve_rule ROv2_0_00. Qed.
Lemma T2_Even00_blank len k a: k<2^len ->
  LC len k |> T2 (a*2) 0 0 -->+
  LC (len+1+a*5+6) ((k*2+1)*2^(a*5+6)-41) |> RC 0.
Proof.
  intros; rewrite LC_tail6 by lia.
  epose proof (ROv2_0_00 _ 0inf a) as HB; solve_rule HB.
Qed.
Lemma T2_Even01 len k a m: k<2^len ->
  LC len k |> T2 (a*2) 0 ((m*2+1)*2) -->+
  LC (len+1+a*5+6+1) (((k*2+1)*2^(a*5+6)-41)*2) |2> [0] *> RC m.
Proof.
  intros; rewrite LC_double by arith.
  rewrite LC_tail6 by lia; unfold LC,T2,RC; rw_Bin.
  follow10 ROv2_0_01; follow100 ROv'; repeat (simpl_rotate || simpl_tape); finish.
Qed.

Lemma S_zeros l r a:
  l |2> [0] *> z^^(a*2) *> r -->* l <* ld1^^(a*5) |2> [0] *> r.
Proof.
  gen l; induction a; intros; [cbn; finish|].
  replace (S a*2) with (2+a*2) by lia.
  rewrite lpow_add; cbn [lpow List.app Str_app].
  do 5 (eapply evstep_trans; [apply progress_evstep,ROv'|]).
  follow IHa; repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma S_Even_word l r a:
  l |2> [0] *> z^^(a*2) *> d *> r -->+ l <* ld1^^(a*5+2) |> [1;0] *> r.
Proof.
  eapply evstep_progress_trans; [apply S_zeros|].
  follow10 ROv'_0; repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma S_Odd_word l r a b:
  l |2> [0] *> z^^(a*2+1) *> d^^(b+1) *> z *> r -->+
  l <* ld1^^(a*5+4) |> [0;0;0] *> z^^b *> d *> r.
Proof.
  rewrite (Nat.add_comm b 1).
  rewrite lpow_add,Str_app_assoc; cbn [lpow List.app Str_app].
  eapply evstep_progress_trans; [apply S_zeros|].
  follow10 ROv'; follow100 ROv'; follow100 ROv'; follow100 ROv'_1.
  repeat (simpl_rotate || simpl_tape); finish.
Qed.
Lemma S_Blank len k: k<2^len ->
  LC len k |2> [0] *> RC 0 -->+ LC (len+1) (k*2) |2> [0] *> RC 0.
Proof. epose proof (ROv' _ 0inf) as H; solve_rule H. Qed.
Lemma S_Even len k a b m: k<2^len ->
  LC len k |2> [0] *> RC ((((m*2+1)*2^b)*2+1)*2^(a*2)) -->+
  LC (len+(a*5+2)) (k*2^(a*5+2)) |> T2 b ((2^b-1)*2) m.
Proof.
  solve_rule S_Even_word.
Qed.
Lemma S_Even_blank len k a: k<2^len ->
  LC len k |2> [0] *> RC ((0*2+1)*2^(a*2)) -->+
  LC (len+(a*5+2)) (k*2^(a*5+2)) |> RC 1.
Proof.
  solve_rule S_Even_word.
Qed.
Lemma S_Odd len k a b m: k<2^len ->
  LC len k |2> [0] *> RC (((m*2+1)*2^(b+1)-1)*2^(a*2+1)) -->+
  LC (len+(a*5+4)) (k*2^(a*5+4)) |> T3 b (2^(b+1)-1) m.
Proof.
  solve_rule S_Odd_word.
Qed.

Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat) | cfgS (len k m:nat)
  | cfg2 (len k h n m:nat) | cfg3 (len k h n m:nat).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfgS len k m => LC len k |2> [0%sym] *> RC m
| cfg2 len k h n m => LC len k |> T2 h n m
| cfg3 len k h n m => LC len k |> T3 h n m
end.
Definition P x := match x with
| cfgL len k m => 1<=len /\ k<2^len /\ 1<=k+m<2^(len+1)
| cfgR len k m => 1<=len /\ k<2^len /\ 1<=k+m+1<2^(len+1)
| cfgS len k m => 1<=len /\ k<2^len /\ m<=k*2+1
| cfg2 len k h n m | cfg3 len k h n m =>
    1<=len /\ k<2^len /\ n<2^(h+1) /\ n+m<=k
end.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k m|len k h n m|len k h n m];
    cbn [P to_config]; intros HP.
  - destruct k as [|k].
    + exists (cfgS len (2^len-1) m); split; [apply LC_Ov|cbn [P]; arith].
    + exists (cfgR len k m); split; [apply LC_Inc; lia|cbn [P]; lia].
  - exists (cfgL len k (1+m)); split; [apply RC_Inc|cbn [P]; lia].
  - destruct (lowbit_cases' m) as [|u h].
    + exists (cfgS (len+1) (k*2) 0); split; [apply S_Blank; lia|cbn [P]; arith].
    + divmod2_cases h; rename n' into a.
      * destruct (lowbit_cases' u) as [|m b].
        -- exists (cfgR (len+(a*5+2)) (k*2^(a*5+2)) 1).
           split; [apply S_Even_blank; lia|cbn [P]; arith].
        -- exists (cfg2 (len+(a*5+2)) (k*2^(a*5+2)) b ((2^b-1)*2) m).
           split; [apply S_Even; lia|cbn [P]; arith].
      * destruct (lowbitS_cases' u) as [m b].
        replace (((m*2+1)*2^b-1)*2+1) with ((m*2+1)*2^(b+1)-1) in * by arith.
        exists (cfg3 (len+(a*5+4)) (k*2^(a*5+4)) b (2^(b+1)-1) m).
        split; [apply S_Odd; lia|cbn [P]; arith].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      exists (cfg2 len k h n m); split.
      - eapply progress_evstep_trans; [apply Mark_Inc; lia|].
        apply progress_evstep,LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + divmod2_cases m; rename n' into b.
      * divmod2_cases b; rename n' into u.
        -- destruct (lowbit_cases' u) as [|m b].
           ++ exists (cfgR (len+1+a*5+6) ((k*2+1)*2^(a*5+6)-41) 0).
              split; [apply T2_Even00_blank; lia|cbn [P]; arith].
           ++ exists (cfg3 (len+1+a*5+6) ((k*2+1)*2^(a*5+6)-41) b (2^(b+1)-1) m).
              split; [apply T2_Even00; lia|cbn [P]; arith].
        -- exists (cfgS (len+1+a*5+6+1) (((k*2+1)*2^(a*5+6)-41)*2) u).
           split; [apply T2_Even01; lia|cbn [P]; arith].
      * destruct (lowbitS_cases' b) as [m b].
        replace (((m*2+1)*2^b-1)*2+1) with ((m*2+1)*2^(b+1)-1) in * by arith.
        exists (cfgR (len+1+(a*5+2)+3) ((k*2+1)*2^(a*5+2+3)-6) ((m*2+1)*2^b)).
        split; [apply T2_Even1; lia|cbn [P]; arith].
    + destruct (lowbitS_cases' m) as [m b].
      exists (cfg2 (len+1+(a*5+3)+1) ((k*2+1)*2^(a*5+3+1)-2) b (2^(b+1)-1) m).
      split; [apply T2_Odd; lia|cbn [P]; arith].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      exists (cfg3 len k h n m); split.
      - eapply progress_evstep_trans; [apply Mark_Inc; lia|].
        apply progress_evstep,LC_Inc; lia.
      - cbn [P]; lia. }
    divmod2_cases h; rename n' into a.
    + destruct (lowbitS_cases' m) as [m b].
      exists (cfgR (len+1+(a*5+2)+1) ((k*2+1)*2^(a*5+2+1)-2) ((m*2+1)*2^b)).
      split; [apply T3_Even; lia|cbn [P]; arith].
    + exists (cfgS (len+1+(a*5+5)) ((k*2+1)*2^(a*5+5)-1) m).
      split; [apply T3_Odd; lia|cbn [P]; arith].
Qed.
Theorem nonhalt_from len k m:
  c0 -->* to_config (cfgL len k m) -> P (cfgL len k m) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.
End Counter.
End Counter.

Open Scope sym.
End SOC25_TM91.

(* SOC25_TM91.TM91 *)
Module TM91.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM91.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC---_1LD1RE_1RC1LD_1RF0RC_1LA0RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1] {{F}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;0;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+
  l <| z^^n *> [1] *> r.
Proof. destruct n; es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |2> [0] *> r.
Proof. es. Qed.

Lemma ROv' l r:
  l |2> [0;0] *> r -->+
  l <* ld1 |2> r.
Proof. es. Qed.

Lemma ROv'_1 l r n:
  l |2> d^^(1+n) *> z *> r -->+
  l <* ld1 |> [0;0;0] *> z^^n *> d *> r.
Proof. es. Qed.

Lemma ROv'_0 l r:
  l |2> [0] *> d *> r -->+
  l <* ld1^^2 |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_00 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> z *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_01 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> d *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |2> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_1 l r n m:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> d^^(1+m) *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 <* ld0 <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n m:
  l |> d^^(n*2+1) *> [1;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1 |> [0;0] *> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_0 l r n m:
  l |> d^^(n*2) *> [1;0;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_1 l r n:
  l |> d^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+5) |2> [0] *> r.
Proof. es. Qed.

Lemma init: c0 -->* (BinDec ld0 ld1 9 248 ldh <| BinInc d 0).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=D) (QR:=F) (len:=9) (k:=248) (m:=0%nat).
  all: try solve[eauto using LInc,RInc,LOv,ROv',ROv'_1,ROv'_0,
    ROv2_0_00,ROv2_0_01,ROv2_0_1,ROv2_1,ROv3_0,ROv3_1,init].
  cbn [Counter.P]; lia.
Qed.
End TM91.

(* SOC25_TM91.TM92 *)
Module TM92.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM91.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA1LB_1RD0RA_1LE0RF_1RF0LE_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+
  l <| z^^n *> [1] *> r.
Proof. destruct n; es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |2> [0] *> r.
Proof. es. Qed.

Lemma ROv' l r:
  l |2> [0;0] *> r -->+
  l <* ld1 |2> r.
Proof. es. Qed.

Lemma ROv'_1 l r n:
  l |2> d^^(1+n) *> z *> r -->+
  l <* ld1 |> [0;0;0] *> z^^n *> d *> r.
Proof. es. Qed.

Lemma ROv'_0 l r:
  l |2> [0] *> d *> r -->+
  l <* ld1^^2 |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_00 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> z *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_01 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> d *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |2> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_1 l r n m:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> d^^(1+m) *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 <* ld0 <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n m:
  l |> d^^(n*2+1) *> [1;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1 |> [0;0] *> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_0 l r n m:
  l |> d^^(n*2) *> [1;0;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_1 l r n:
  l |> d^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+5) |2> [0] *> r.
Proof. es. Qed.

Lemma init: c0 -->* (BinDec ld0 ld1 5 30 ldh <| BinInc d 1).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=B) (QR:=D) (len:=5) (k:=30) (m:=1%nat).
  all: try solve[eauto using LInc,RInc,LOv,ROv',ROv'_1,ROv'_0,
    ROv2_0_00,ROv2_0_01,ROv2_0_1,ROv2_1,ROv3_0,ROv3_1,init].
  cbn [Counter.P]; lia.
Qed.
End TM92.

(* SOC25_TM91.TM95 *)
Module TM95.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM91.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC0RD_1LB1RE_---1LC_1RF0RC_1LA0RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1] {{F}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;0;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+
  l <| z^^n *> [1] *> r.
Proof. destruct n; es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |2> [0] *> r.
Proof. es. Qed.

Lemma ROv' l r:
  l |2> [0;0] *> r -->+
  l <* ld1 |2> r.
Proof. es. Qed.

Lemma ROv'_1 l r n:
  l |2> d^^(1+n) *> z *> r -->+
  l <* ld1 |> [0;0;0] *> z^^n *> d *> r.
Proof. es. Qed.

Lemma ROv'_0 l r:
  l |2> [0] *> d *> r -->+
  l <* ld1^^2 |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_00 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> z *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_01 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> d *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |2> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_1 l r n m:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> d^^(1+m) *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 <* ld0 <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n m:
  l |> d^^(n*2+1) *> [1;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1 |> [0;0] *> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_0 l r n m:
  l |> d^^(n*2) *> [1;0;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_1 l r n:
  l |> d^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+5) |2> [0] *> r.
Proof. es. Qed.

Lemma init: c0 -->* (BinDec ld0 ld1 1 0 ldh <| BinInc d 2).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=B) (QR:=F) (len:=1%nat) (k:=0%nat) (m:=2).
  all: try solve[eauto using LInc,RInc,LOv,ROv',ROv'_1,ROv'_0,
    ROv2_0_00,ROv2_0_01,ROv2_0_1,ROv2_1,ROv3_0,ROv3_1,init].
  cbn [Counter.P]; lia.
Qed.
End TM95.

(* SOC25_TM91.TM96 *)
Module TM96.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC25_TM91.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0RF_1RD0RA_1LE0RB_1RB0LE_---1LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;0;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> d^^n *> [0] *> r -->+
  l <| z^^n *> [1] *> r.
Proof. destruct n; es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |2> [0] *> r.
Proof. es. Qed.

Lemma ROv' l r:
  l |2> [0;0] *> r -->+
  l <* ld1 |2> r.
Proof. es. Qed.

Lemma ROv'_1 l r n:
  l |2> d^^(1+n) *> z *> r -->+
  l <* ld1 |> [0;0;0] *> z^^n *> d *> r.
Proof. es. Qed.

Lemma ROv'_0 l r:
  l |2> [0] *> d *> r -->+
  l <* ld1^^2 |> [1;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_00 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> z *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_01 l r n:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> z *> d *> r -->+
  l <* ld1 <* ld0^^(n*5) <* ld1 <* ld0 <* ld1 <* ld0^^3 |2> [0;0;0] *> r.
Proof. es. Qed.

Lemma ROv2_0_1 l r n m:
  l |> d^^(n*2) *> [1;0;1;0;0;0;0] *> d^^(1+m) *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 <* ld0 <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n m:
  l |> d^^(n*2+1) *> [1;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1 |> [0;0] *> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_0 l r n m:
  l |> d^^(n*2) *> [1;0;0;1;0;0;0;0] *> d^^m *> z *> r -->+
  l <* ld1 <* ld0^^(n*5+2) <* ld1 |> z^^m *> d *> r.
Proof. es. Qed.

Lemma ROv3_1 l r n:
  l |> d^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+5) |2> [0] *> r.
Proof. es. Qed.

Lemma init: c0 -->* (BinDec ld0 ld1 5 30 ldh <| BinInc d 1).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=B) (QR:=D) (len:=5) (k:=30) (m:=1%nat).
  all: try solve[eauto using LInc,RInc,LOv,ROv',ROv'_1,ROv'_0,
    ROv2_0_00,ROv2_0_01,ROv2_0_1,ROv2_1,ROv3_0,ROv3_1,init].
  cbn [Counter.P]; lia.
Qed.
End TM96.
