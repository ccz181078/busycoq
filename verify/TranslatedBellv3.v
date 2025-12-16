From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import DivModCases.


Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; try reflexivity.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1RC0LE_1RD0RF_1LA1RC_0LA1RD_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l {{D}}> RC ls [1+n] -->*
  l <{{E}} [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] {{D}}> RC (ls++[n]) [O] -->*
  l <{{E}} [0;0] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l {{D}}> RC ls (2+n::1+n0::ls0) -->*
  l <{{E}} [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <{{B}} [0;1;0;1;1;0;1]^^a *> [1;0;1]^^b *> [0;1;0;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0 n1:
  S1 a b 0 (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 a (2+b) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ (b) *>
  1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf {{D}}>
  RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf {{D}}> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (1+a+length (ls0++[n1])+n0) (2+b) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d (1+b) a ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d (1+b) (1+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 7 (er; sr).
  do 9 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 1 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (2+c+length (ls0++[n1])+n0) (2+c) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0 n1:
  S1 1 0 c (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 (1+c) (2+c) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 1 0 c (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n1 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::n1::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,c*3::(map S (4+d*3::n::n0::n1::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n1 n0' n1' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n1::n0'::n1'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,3+c*3::(map S (4+c*3::4+d*3::n::n0::n1::n0'::n1'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (2+(1+(1+c*2))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=5 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    destruct ls as [|n0' [|n1' ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (53,17,51::(map (Nat.add 3) [26;20;21;15;9])++[16]).
Proof.
  stepn 180137%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 5 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0RF_1LD1RB_1RA0LA_0LD1RC_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Notation "l |> r" := (l {{C}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l <l| r" := (l <{{A}} r) (at level 30).

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l |> RC ls [1+n] -->*
  l <| [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] |> RC (ls++[n]) [O] -->*
  l <| [0;0] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l |> RC ls (2+n::1+n0::ls0) -->*
  l <| [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <l| [0;1;0;1;1;0;1]^^a *> [1;0;1]^^b *> [0;1;0;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0 n1:
  S1 a b 0 (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 a (2+b) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ (b) *>
  1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf |>
  RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf |> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (1+a+length (ls0++[n1])+n0) (2+b) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d (1+b) a ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d (1+b) (1+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 7 (er; sr).
  do 9 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 1 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (2+c+length (ls0++[n1])+n0) (2+c) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0 n1:
  S1 1 0 c (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 (1+c) (2+c) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 1 0 c (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n1 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::n1::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,c*3::(map S (4+d*3::n::n0::n1::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n1 n0' n1' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n1::n0'::n1'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,3+c*3::(map S (4+c*3::4+d*3::n::n0::n1::n0'::n1'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (2+(1+(1+c*2))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=5 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    destruct ls as [|n0' [|n1' ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (394,141,423::(map (Nat.add 3) [269;263;264;162;156])++[163]).
Proof.
  stepn 11342335%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 5 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1RD0LD_1RA0LE_0LC1RB_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Notation "l |> r" := (l {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l <l| r" := (l <{{D}} r) (at level 30).

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l |> RC ls [1+n] -->*
  l <| [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] |> RC (ls++[n]) [O] -->*
  l <| [0;0] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l |> RC ls (2+n::1+n0::ls0) -->*
  l <| [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <l| [0;1;0;1;1;0;1]^^a *> [1;0;1]^^b *> [0;1;0;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0 n1:
  S1 a b 0 (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 a (2+b) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ (b) *>
  1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf |>
  RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> [1; 1; 1; 1; 1; 0; 0] ^^ a *> 0inf |> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (1+a+length (ls0++[n1])+n0) (2+b) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d (1+b) a ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d (1+b) (1+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 7 (er; sr).
  do 9 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 1 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 1 0 (2+c+length (ls0++[n1])+n0) (2+c) [] ((d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0 n1:
  S1 1 0 c (3+d*2) ls (2+n::3+n0::1+n1::ls0) -->+
  S1 1 0 (1+c) (2+c) ((4+d*3)::((ls++[n])++[n0])) (n1::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 1 0 c (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n1 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::n1::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,c*3::(map S (4+d*3::n::n0::n1::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n1 n0' n1' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n1::n0'::n1'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,3+c*3::(map S (4+c*3::4+d*3::n::n0::n1::n0'::n1'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (2+(1+(1+c*2))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=5 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    destruct ls as [|n0' [|n1' ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (375,133,399::(map (Nat.add 3) [284;278;177;171;172])++[109]).
Proof.
  stepn 10180415%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 5 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0LC_0LA1RD_1LA1RE_1RD0RF_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Notation "l |> r" := (l {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l <l| r" := (l <{{B}} r) (at level 30).

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l |> RC ls [1+n] -->*
  l <| [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] |> RC (ls++[n]) [O] -->*
  l <| [] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l |> RC ls (2+n::1+n0::ls0) -->*
  l <| [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <l| [0;1;0;1;0;1;1]^^a *> [0;1;0;1;0;1] *> [0;1;1]^^b *> [0;1;0;1] *> [0;0;1;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0:
  S1 a b 0 (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+a) (1+b) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+a+length (ls0++[n1])+n0) (1+b) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d b (1+a) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d b (3+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 5 (er; sr).
  do 12 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 0 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+c+length (ls0++[n1])+n0) (1+c) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0:
  S1 0 0 c (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+c) (1+c) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 0 0 (1+c) (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,1+c*3::(map S (4+d*3::n::n0::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n0' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n0'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,4+c*3::(map S (4+c*3::4+d*3::n::n0::n0'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (1+(1+(1+(1+c*2)))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=3 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 ls].
    1: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (81,26,79::(map (Nat.add 3) [77;41;36;24])++[25]).
Proof.
  stepn 479462%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 4 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LB_0LC1RD_1RA0LA_1LC1RE_1RD0RF_0RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Notation "l |> r" := (l {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} r) (at level 30).
Notation "l <l| r" := (l <{{A}} r) (at level 30).

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l |> RC ls [1+n] -->*
  l <| [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] |> RC (ls++[n]) [O] -->*
  l <| [] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l |> RC ls (2+n::1+n0::ls0) -->*
  l <| [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <l| [0;1;0;1;0;1;1]^^a *> [0;1;0;1;0;1] *> [0;1;1]^^b *> [0;1;0;1] *> [0;0;1;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0:
  S1 a b 0 (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+a) (1+b) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+a+length (ls0++[n1])+n0) (1+b) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d b (1+a) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d b (3+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 5 (er; sr).
  do 12 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 0 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+c+length (ls0++[n1])+n0) (1+c) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0:
  S1 0 0 c (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+c) (1+c) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 0 0 (1+c) (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,1+c*3::(map S (4+d*3::n::n0::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n0' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n0'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,4+c*3::(map S (4+c*3::4+d*3::n::n0::n0'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (1+(1+(1+(1+c*2)))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=3 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 ls].
    1: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (51,15,46::(map (Nat.add 3) [23;18;15])++[16]).
Proof.
  stepn 155004%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 3 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1RD0LD_1LE0LE_0LC1RB_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint RC' ls :=
match ls with
| [] => 0inf
| h::t => [1;0]^^h *> [0] *> RC' t
end.

Fixpoint RC ls ls0 :=
match ls with
| [] => RC' ls0
| h::t => [1;0]^^h *> [1;1;0] *> RC t ls0
end.

Notation "l |> r" := (l {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{E}} r) (at level 30).
Notation "l <l| r" := (l <{{D}} r) (at level 30).

Ltac esf := repeat (es; er; try follow).

Lemma RInc l ls n:
  l |> RC ls [1+n] -->*
  l <| [0;0;1;0] *> RC ls [n].
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma ROv l ls n:
  l <* [0] |> RC (ls++[n]) [O] -->*
  l <| [] *> RC [] ((map S ls)++[4+n]).
Proof.
  gen l n.
  induction ls; esf.
Qed.

Lemma RInc' l ls ls0 n n0:
  l |> RC ls (2+n::1+n0::ls0) -->*
  l <| [0;0;1;0] *> RC (ls++[n]) (n0::ls0).
Proof.
  gen l n ls0.
  induction ls; esf.
Qed.

Definition S1 a b c d ls ls0 :=
  0inf <l| [0;1;0;1;0;1;1]^^a *> [0;1;0;1;0;1] *> [0;1;1]^^b *> [0;1;0;1] *> [0;0;1;0;1;0;1]^^c *> [0;1;0]^^d *> RC ls ls0.

Lemma Inc1 a b c d ls ls0:
  S1 a b (1+c) d ls ls0 -->*
  S1 (1+a) (1+b) c d ls ls0.
Proof.
  es.
Qed.

Lemma Incs1 a b c d ls ls0:
  S1 a b c d ls ls0 -->*
  S1 (c+a) (c+b) 0 d ls ls0.
Proof.
  gen a b d ls ls0.
  ind c Inc1.
Qed.

Lemma Ov1_1 a b d ls ls0 n n0:
  S1 a b 0 (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+a) (1+b) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  epose proof RInc'.
  esf.
Qed.

Definition S2 d b a ls ls0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls ls0.

Lemma Inc2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::1+n0::ls0) -->*
  S2 d b (1+a) (ls++[n]) (n0::ls0).
Proof.
  pose proof RInc'.
  esf.
Qed.

Lemma Incs2 d b a ls ls0 n n0:
  S2 d b a ls (2+n::(map (Nat.add 3) ls0)++[1+n0]) -->*
  S2 d b (length ls0+1+a) (ls++n::ls0) [n0].
Proof.
  gen a ls n.
  induction ls0; intros; cbn.
  - follow Inc2.
    finish.
  - follow Inc2.
    follow IHls0.
    rewrite <-app_assoc.
    finish.
Qed.

Definition S3 d b a ls n0 :=
  0 >> 0 >> 1 >> 1 >> 1 >> [1; 1; 1; 1; 1; 1] ^^ d *> [0; 0; 1] ^^ b *> 1 >> 1 >> 1 >> [1; 1; 1; 0; 0; 1; 1] ^^ a *> 0inf |> RC ls [n0].

Lemma Inc3 d b a ls n0:
  S3 d b a ls (1+n0) -->*
  S3 d b (1+a) ls n0.
Proof.
  pose proof RInc.
  esf.
Qed.

Lemma Incs3 d b a ls n0:
  S3 d b a ls n0 -->*
  S3 d b (n0+a) ls 0.
Proof.
  gen a.
  ind n0 Inc3.
Qed.

Lemma Ov1_0 a b d ls ls0 n n0 n1:
  S1 a b 0 (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+a+length (ls0++[n1])+n0) (1+b) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  mid10 (S2 d b (1+a) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0])).
  1: es.
  follow Incs2.
  mid (S3 d b (3+length (ls0++[n1])+a) (ls++n::(ls0++[n1])) n0).
  1: es.
  follow Incs3.
  unfold S3.
  rewrite app_comm_cons,app_assoc.
  follow ROv.
  unfold S1.
  do 5 (er; sr).
  do 12 step1.
  st.
  er.
Qed.

Lemma BigStep0 c d ls ls0 n n0 n1:
  S1 0 0 c (2+d*2) ls (2+n::(map (Nat.add 3) (ls0++[n1]))++[1+n0]) -->+
  S1 0 0 (2+c+length (ls0++[n1])+n0) (1+c) [] ((1+d*3)::map S (ls++n::ls0)++[4+n1]).
Proof.
  follow Incs1.
  follow10 Ov1_0.
  finish.
Qed.

Lemma BigStep1 c d ls ls0 n n0:
  S1 0 0 c (3+d*2) ls (2+n::1+n0::ls0) -->+
  S1 0 0 (1+c) (1+c) ((4+d*3)::(ls++[n])) (n0::ls0).
Proof.
  follow Incs1.
  follow10 Ov1_1.
  finish.
Qed.

Definition S' '(c,d,ls) := S1 0 0 (1+c) (3+d*2) [] ls.

Lemma BigStep10 c d ls0 n n0 n2 n3:
  S' (c*2,d,2+n::(map (Nat.add 3) (n0::(ls0++[n2])))++[1+n3]) -->+
  S' (3+c*2+length (ls0++[n2])+n3,c,1+c*3::(map S (4+d*3::n::n0::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow10 BigStep0.
  finish.
Qed.

Lemma BigStep110 c d ls0 n n0 n0' n2 n3:
  S' (1+c*2,d,2+n::(map (Nat.add 3) (n0::n0'::(ls0++[n2])))++[1+n3]) -->+
  S' (5+c*2+length (ls0++[n2])+n3,1+c,4+c*3::(map S (4+c*3::4+d*3::n::n0::n0'::ls0))++[4+n2]).
Proof.
  unfold S'.
  cbn[map].
  follow11 BigStep1.
  follow11 BigStep1.
  replace (1+(1+(1+(1+c*2)))) with (2+(1+c)*2) by lia.
  follow10 BigStep0.
  finish.
Qed.

Lemma map_add3_cons h t:
  h>=3 ->
  h::map (Nat.add 3) t =
  map (Nat.add 3) (h-3::t).
Proof.
  intros; cbn; flia.
Qed.

Inductive WF: (list nat)->Prop :=
| WF_O: WF []
| WF_S h t:
  WF t ->
  h>=(length t)*2 ->
  WF (h::t).

Ltac lia' :=
  cbn[length] in *; lia.

Lemma WF_map_S ls n:
  WF (ls++[n]) ->
  let ls':=(map (fun x => Nat.sub x 2) ls) in
  map S ls = map (Nat.add 3) ls' /\
  WF ls'.
Proof.
  induction ls; cbn; intros.
  - split.
    + trivial.
    + apply WF_O.
  - inverts H.
    apply IHls in H2.
    destruct H2 as [I1 I2].
    split.
    + rewrite I1.
      rewrite length_app in H3.
      cbn in H3.
      flia.
    + eapply WF_S.
      1: apply I2.
      rewrite length_map.
      rewrite length_app in H3.
      cbn in H3.
      lia.
Qed.

Inductive P: nat*nat*(list nat)->Prop :=
  | P_intro c d ls n n':
  WF ls ->
  length ls>=3 ->
  c/2*3>=4+(length ls)*2 ->
  n'>=(length ls)*2 ->
  d*3>=(length ls)*2 ->
  P (c,d,2+n'::(map (Nat.add 3) ls)++[1+n]).

Local Opaque Nat.div Nat.modulo.

Ltac lia'' := repeat (rewrite length_app || rewrite length_map || cbn); try lia.

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\ P x'.
Proof.
  intro HP.
  inverts HP.
  destruct (mod2 c); subst c.
  - cbn[map].
    destruct ls as [|n0 ls].
    1: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep10.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 2 rewrite map_cons.
    rewrite I1.
    do 2 (rewrite map_add3_cons by lia).
    replace (a*3) with (2+(a*3-2)) by lia.
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-2: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
  - cbn[map].
    destruct ls as [|n0 [|n1 ls]].
    1,2: lia'.
    unshelve epose proof (@exists_last _ ls _) as [ls' [n2 I1]].
    1: destruct ls; [lia'|congruence].
    subst ls.
    eexists; split.
    1: apply BigStep110.
    fold Nat.add.
    repeat rewrite app_comm_cons in H.
    eapply WF_map_S in H.
    destruct H as [I1 I2].
    do 3 rewrite map_cons.
    rewrite I1.
    do 3 (rewrite map_add3_cons by lia).
    cbn in H0,H1,H2,H3.
    rewrite length_app in H0,H1,H2,H3.
    cbn in H0,H1,H2,H3.
    eapply P_intro.
    + eapply WF_S.
      1: eapply WF_S.
      1: eapply WF_S.
      1: apply I2.
      1-3: lia''.
    + lia''.
    + lia''.
    + lia''.
    + lia''.
Qed.

Lemma init:
  c0 -->*
  S' (31,8,25::(map (Nat.add 3) [23;20;15])++[21]).
Proof.
  stepn 72457%N.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2:{
    econstructor.
    2-5: cbn; lia.
    do 3 (apply WF_S; [|cbn; lia]).
    apply WF_O.
  }
  intro x.
  apply closed.
Qed.

End TM6.


