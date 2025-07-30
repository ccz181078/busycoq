From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.

Open Scope list.

Ltac flia := repeat (lia || f_equal).

Lemma lrcons_lpow1' h1 h2 n:
  lrcons h1 ([(h2, h1)] ^^ n) h2 = [(h1, h2)] ^^ (n+1).
Proof.
  applys_eq lrcons_lpow1; flia.
Qed.

Lemma segRLs_trans_add tm h h' n1 n2 n1' n2' w1 w2 w3:
  segRLs tm (h^^n1) (h'^^n1') w1 w3 ->
  segRLs tm (h^^n2) (h'^^n2') w3 w2 ->
  segRLs tm (h^^(n1+n2)) (h'^^(n1'+n2')) w1 w2.
Proof.
  intros.
  do 2 rewrite lpow_add.
  eapply segRLs_trans; eassumption.
Qed.

Lemma sideRLs_trans_add tm h n1 n2 w1 w2 w3:
  sideRLs tm (h^^n1) w1 w3 ->
  sideRLs tm (h^^n2) w3 w2 ->
  sideRLs tm (h^^(n1+n2)) w1 w2.
Proof.
  intros.
  rewrite lpow_add.
  eapply sideRLs_trans; eassumption.
Qed.

Lemma sideRLs_trans_S tm h n w1 w2 w3:
  sideRLs tm (h^^n) w1 w3 ->
  sideRLs tm h w3 w2 ->
  sideRLs tm (h^^(S n)) w1 w2.
Proof.
  intros.
  replace (S n) with (n+1) by lia.
  eapply sideRLs_trans_add.
  - apply H.
  - cbn.
    rewrite app_nil_r.
    apply H0.
Qed.

Ltac sideRLs_ind k :=
  induction k;
  [ try esx |
    eapply sideRLs_trans_S;
    [ eassumption | ];
    try esx ].

Ltac ss2 a b :=
  assert_fails (is_evar a);
  solve_seg.

Ltac ss1 :=
match goal with
| |- segRR _ _ _ ?a ?b => ss2 a b
| |- segRL _ _ _ ?a ?b => ss2 a b
| |- segLR _ _ _ ?a ?b => ss2 a b
| |- segLL _ _ _ ?a ?b => ss2 a b
end.

Ltac ss :=
  try ss1.



Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0LC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,[(0,4)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,[(0,4)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0LA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w1'^^n) (w0'^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + b + Rn t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = l + Rn ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n)) (RCa ls) (RCb ls n).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2+1-Rn ls)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls+1) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+(n-1)) by lia.
    rewrite <-Nat.add_assoc.
    apply RIncs.
  - follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,[(0,3)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w1'^^n) (w0'^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + b + Rn t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = l + Rn ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n)) (RCa ls) (RCb ls n).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2+1-Rn ls)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls+1) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+(n-1)) by lia.
    rewrite <-Nat.add_assoc.
    apply RIncs.
  - follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,[(0,3)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RB---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w1'^^n) (w0'^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + b + Rn t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = l + Rn ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n)) (RCa ls) (RCb ls n).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2+1-Rn ls)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls+1) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+(n-1)) by lia.
    rewrite <-Nat.add_assoc.
    apply RIncs.
  - follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0LB---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w1'^^n) (w0'^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + b + Rn t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = l + Rn ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n)) (RCa ls) (RCb ls n).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2+1-Rn ls)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls+1) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+(n-1)) by lia.
    rewrite <-Nat.add_assoc.
    apply RIncs.
  - follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA0LB_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w1'^^n) (w0'^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + b + Rn t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = l + Rn ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n)) (RCa ls) (RCb ls n).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2+1-Rn ls)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls+1) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+(n-1)) by lia.
    rewrite <-Nat.add_assoc.
    apply RIncs.
  - follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0LE1RF_0RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0LE1RF_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,[(0,4)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0LD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RE_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0'^^n *> 0inf.

Lemma Incs0 n:
  sideRLs tm (hRL^^n) (RC0 0) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma Incs' n m:
  segRLs tm (hRL^^(1+m)) (hRL^^(1+m)) (w1'^^n) (w0'^^n).
Proof.
  eapply segRLs_trans_add.
  1: esx.
  eapply segRLs_wall.
  1: solve_seg.
  1: solve_seg.
Qed.

Fixpoint RCa ls :=
match ls with
| [] => 0inf
| (a,b)::t => w1'^^a *> w0^^b *> RCa t
end.

Fixpoint RCb ls n :=
match ls with
| [] => RC0 n
| (a,b)::t => w0'^^a *> w1^^b *> RCb t n
end.

Fixpoint cons(l:nat)(x:list (nat*nat))(r:nat) :=
match x with
| [] => [(l,r)]
| (a,b)::t => (l,a)::cons b t r
end.

Lemma RCb_shift ls n:
  RCb ls n = [0;0] *> RCa (cons 0 ls n).
Proof.
  gen n.
  induction ls; intros.
  - cbn; unfold RC0.
    simpl_rotate; reflexivity.
  - destruct a as [a b].
    cbn.
    rewrite IHls.
    destruct ls as [|[a0 b0] ls];
    simpl_rotate; reflexivity.
Qed.

Fixpoint Rn (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => b + Rn t
end.

Fixpoint Rn' (ls:list (nat*nat)) :=
match ls with
| [] => O
| (a,b)::t => a + Rn' t
end.

Lemma Rn_cons l ls r:
  Rn (cons l ls r) = Rn' ls + r.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.

Lemma Rn'_cons l ls r:
  Rn' (cons l ls r) = Rn ls + l.
Proof.
  gen l.
  induction ls; intros; cbn.
  - lia.
  - destruct a as [a b]; cbn.
    rewrite IHls.
    lia.
Qed.


Lemma RIncs ls n:
  sideRLs tm (hRL^^(Rn ls+n+1)) (RCa ls) (RCb ls (n+1)).
Proof.
  induction ls.
  - cbn.
    apply Incs0.
  - destruct a as [a b].
    cbn.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs' a (b+Rn ls+n)); flia.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (Incs b (Rn ls+n+1)); flia.
    apply IHls.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RCa ls.

Lemma Rst k ls n:
  dh <* d1^^k {{{ (hL,L) }}} RCb ls n -->*
  S (k,cons 0 ls n).
Proof.
  rewrite RCb_shift.
  es.
Qed.

Lemma BigStep k ls:
  Rn ls <= (2^k-1)*2 ->
  S (k,ls) -->+
  S (1+k,cons 0 ls ((2^k-1)*2-Rn ls+1)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-Rn ls) as n.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2) with (Rn ls+n) by lia.
    apply RIncs.
  - apply Rst.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[(0,1)])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => Rn ls<=(2^k-1)*2 /\ Rn' ls <= Rn ls + (2^k*2-1)).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Rn_cons.
  rewrite Rn'_cons.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC0RE_1LA1LD_0RA1RF_1RD---_0RB0RA").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0]).
Notation hL := (A,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;1;1;0].
Notation d1 := <[0;1;0;1].
Notation dh := (0inf <* [1]).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((3^n-1))) (dh <* d0^^n) (dh <* d1^^n).
Proof.
  induction n.
  1: esx.
  remember (3^n-1) as k.
  replace (3^S n-1) with (k*3+2) by (cbn; lia).
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 n m :=
  [0;1;0]^^(1+n) *> [0] *> [0;1;0]^^m *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(n*4)) (RC0 0 (n+m)) (RC0 n m).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  gen m.
  induction n; intros.
  - esx.
  - specialize (IHn (S m)).
    eapply sideRLs_trans_S.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*2)) (RC0 m 0) (RC0 (n+m) 0).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^(n*4+m*2)) (RC0 0 n) (RC0 (m+n) 0).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (RIncs0 n 0); flia.
  apply RIncs1.
Qed.

Definition S '(k,n) :=
  dh <* d0^^k {{{ (hL,L) }}} RC0 0 n.

Lemma Rst k n:
  dh <* d1^^k {{{ (hL,L) }}} RC0 (1+n) 0 -->+
  S (1+k,n).
Proof.
  unfold S,RC0.
  es.
Qed.

Lemma pow3sub1_mod2 k:
  (3^k-1) mod 2 = O.
Proof.
  induction k; cbn[Nat.pow]; lia.
Qed.

Lemma BigStep k n:
  n*4<3^k-1 ->
  S (k,n) -->+
  S (1+k,(3^k-1)/2-n-1).
Proof.
  intros Hn.
  remember ((3^k-1)/2-n*2) as m.
  unfold S.
  epose proof (sideRLs_concat_1L (RIncs n m)) as I1.
  epose proof (pow3sub1_mod2 k).
  replace (n*4+m*2) with (3^k-1) in I1 by lia.
  specialize (I1 (LIncs _)).
  follow I1.
  replace (m+n) with (1+(m+n-1)) by lia.
  follow10 Rst.
  unfold S.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n) => n*4<3^k-1).
  2: cbn; lia.
  intros [k n] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r in * by lia.
  lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC0LA_1RA0RD_1RE---_0RB1RF_0RC0RB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (B,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;1;1;0].
Notation d1 := <[0;1;0;1].
Notation dh := (0inf <* [1]).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((3^n-1))) (dh <* d0^^n) (dh <* d1^^n).
Proof.
  induction n.
  1: esx.
  remember (3^n-1) as k.
  replace (3^S n-1) with (k*3+2) by (cbn; lia).
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 n m :=
  [0;1;0]^^(1+n) *> [0] *> [0;1;0]^^m *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(n*4)) (RC0 0 (n+m)) (RC0 n m).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  gen m.
  induction n; intros.
  - esx.
  - specialize (IHn (S m)).
    eapply sideRLs_trans_S.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*2)) (RC0 m 0) (RC0 (n+m) 0).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^(n*4+m*2)) (RC0 0 n) (RC0 (m+n) 0).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (RIncs0 n 0); flia.
  apply RIncs1.
Qed.

Definition S '(k,n) :=
  dh <* d0^^k {{{ (hL,L) }}} RC0 0 n.

Lemma Rst k n:
  dh <* d1^^k {{{ (hL,L) }}} RC0 (1+n) 0 -->+
  S (1+k,n).
Proof.
  unfold S,RC0.
  es.
Qed.

Lemma pow3sub1_mod2 k:
  (3^k-1) mod 2 = O.
Proof.
  induction k; cbn[Nat.pow]; lia.
Qed.

Lemma BigStep k n:
  n*4<3^k-1 ->
  S (k,n) -->+
  S (1+k,(3^k-1)/2-n-1).
Proof.
  intros Hn.
  remember ((3^k-1)/2-n*2) as m.
  unfold S.
  epose proof (sideRLs_concat_1L (RIncs n m)) as I1.
  epose proof (pow3sub1_mod2 k).
  replace (n*4+m*2) with (3^k-1) in I1 by lia.
  specialize (I1 (LIncs _)).
  follow I1.
  replace (m+n) with (1+(m+n-1)) by lia.
  follow10 Rst.
  unfold S.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n) => n*4<3^k-1).
  2: cbn; lia.
  intros [k n] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r in * by lia.
  lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_1RD0LE_1RE0RA_1LC1LB_0RD0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;1;1;0].
Notation d1 := <[0;1;0;1].
Notation dh := (0inf <* <[1;0;1;1;0;1;0;1]).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((3^n-1))) (dh <* d0^^n) (dh <* d1^^n).
Proof.
  induction n.
  1: esx.
  remember (3^n-1) as k.
  replace (3^S n-1) with (k*3+2) by (cbn; lia).
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 n m :=
  [0;1;0]^^(1+n) *> [0] *> [0;1;0]^^m *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(n*4)) (RC0 0 (n+m)) (RC0 n m).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  gen m.
  induction n; intros.
  - esx.
  - specialize (IHn (S m)).
    eapply sideRLs_trans_S.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*2)) (RC0 m 0) (RC0 (n+m) 0).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^(n*4+m*2)) (RC0 0 n) (RC0 (m+n) 0).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (RIncs0 n 0); flia.
  apply RIncs1.
Qed.

Definition S '(k,n) :=
  dh <* d0^^k {{{ (hL,L) }}} RC0 0 n.

Lemma Rst k n:
  dh <* d1^^k {{{ (hL,L) }}} RC0 (1+n) 0 -->+
  S (1+k,n).
Proof.
  unfold S,RC0.
  es.
Qed.

Lemma pow3sub1_mod2 k:
  (3^k-1) mod 2 = O.
Proof.
  induction k; cbn[Nat.pow]; lia.
Qed.

Lemma BigStep k n:
  n*4<3^k-1 ->
  S (k,n) -->+
  S (1+k,(3^k-1)/2-n-1).
Proof.
  intros Hn.
  remember ((3^k-1)/2-n*2) as m.
  unfold S.
  epose proof (sideRLs_concat_1L (RIncs n m)) as I1.
  epose proof (pow3sub1_mod2 k).
  replace (n*4+m*2) with (3^k-1) in I1 by lia.
  specialize (I1 (LIncs _)).
  follow I1.
  replace (m+n) with (1+(m+n-1)) by lia.
  follow10 Rst.
  unfold S.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n) => n*4<3^k-1).
  2: cbn; lia.
  intros [k n] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r in * by lia.
  lia.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LE_1RA0LB_1RE---_0RC1RF_0RA0RC").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;1;1;0].
Notation d1 := <[0;1;0;1].
Notation dh := (0inf <* <[1;0;1;1;0;1;0;1]).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((3^n-1))) (dh <* d0^^n) (dh <* d1^^n).
Proof.
  induction n.
  1: esx.
  remember (3^n-1) as k.
  replace (3^S n-1) with (k*3+2) by (cbn; lia).
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 n m :=
  [0;1;0]^^(1+n) *> [0] *> [0;1;0]^^m *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(n*4)) (RC0 0 (n+m)) (RC0 n m).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  gen m.
  induction n; intros.
  - esx.
  - specialize (IHn (S m)).
    eapply sideRLs_trans_S.
    1: applys_eq IHn; flia.
    esx.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*2)) (RC0 m 0) (RC0 (n+m) 0).
Proof.
  rewrite lpow_mul.
  unfold RC0.
  sideRLs_ind n.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^(n*4+m*2)) (RC0 0 n) (RC0 (m+n) 0).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (RIncs0 n 0); flia.
  apply RIncs1.
Qed.

Definition S '(k,n) :=
  dh <* d0^^k {{{ (hL,L) }}} RC0 0 n.

Lemma Rst k n:
  dh <* d1^^k {{{ (hL,L) }}} RC0 (1+n) 0 -->+
  S (1+k,n).
Proof.
  unfold S,RC0.
  es.
Qed.

Lemma pow3sub1_mod2 k:
  (3^k-1) mod 2 = O.
Proof.
  induction k; cbn[Nat.pow]; lia.
Qed.

Lemma BigStep k n:
  n*4<3^k-1 ->
  S (k,n) -->+
  S (1+k,(3^k-1)/2-n-1).
Proof.
  intros Hn.
  remember ((3^k-1)/2-n*2) as m.
  unfold S.
  epose proof (sideRLs_concat_1L (RIncs n m)) as I1.
  epose proof (pow3sub1_mod2 k).
  replace (n*4+m*2) with (3^k-1) in I1 by lia.
  specialize (I1 (LIncs _)).
  follow I1.
  replace (m+n) with (1+(m+n-1)) by lia.
  follow10 Rst.
  unfold S.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n) => n*4<3^k-1).
  2: cbn; lia.
  intros [k n] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r in * by lia.
  lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0RC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hR' := (D,<[0;0;1;1;1]).
Notation hL' := (A,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[true])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_0LD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (A,[0;0;1]).
Notation hR' := (D,<[0;0;1;1;1]).
Notation hL' := (A,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[true])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA0RF_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0LA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA0RC_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1LC_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RD_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA0RF_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_0RD1RA_0LA1RE_0RA0RC_0LE---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hR' := (A,<[0;0;1;1;1]).
Notation hL' := (B,[0;0;1;0;0]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Notation w0 := [0;0;1;0;0].
Notation w1 := [0;0;1;0;1].
Notation w0' := [0;0;0;0;1].
Notation w1' := [1;0;1;0;0].

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Lemma Incs n m:
  segRLs tm (hRL^^(n+m)) (hRL^^m) (w0^^n) (w1^^n).
Proof.
  eapply UC1.Incs.
  all: ss.
Qed.

Definition RC0 n := w0^^n *> 0inf.

Lemma RC0_Incs n:
  sideRLs tm (hRL'^^n) (0inf) (RC0 n).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 n := w0'^^n *> 0inf.

Lemma RC1_Incs n:
  sideRLs tm (hRL^^n) (0inf) (RC1 n).
Proof.
  unfold RC1.
  sideRLs_ind n.
Qed.

Definition Rmp0(b:bool) :=
  if b then w1' else w0.

Definition Rmp1(b:bool) :=
  if b then w0' else w1.

Fixpoint cnt1(ls:list bool) :=
match ls with
| [] => O
| true::t => 1 + cnt1 t
| false::t => 0 + cnt1 t
end.

Lemma Rmp1_shift (ls:list bool):
  flat_map Rmp1 ls *> 0inf =
  [0;0] *> flat_map Rmp0 (map negb ls) *> 0inf.
Proof.
  induction ls.
  - st; reflexivity.
  - st.
    rewrite IHls.
    destruct a; st; reflexivity.
Qed.

Lemma RInc1 ls:
  segRLs tm hRL' hRL' (flat_map Rmp0 ls) (flat_map Rmp0 ls).
Proof.
  induction ls.
  - esx.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; esx.
Qed.

Lemma RIncs0 ls:
  segRLs tm (hRL^^(length ls)) (hRL'^^(cnt1 ls)) (flat_map Rmp0 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - esx.
  - destruct a;
    cbn[length];
    cbn[cnt1];
    cbn[flat_map];
    cbn[Rmp0]; cbn[Rmp1];
    rewrite <-Nat.add_1_l.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        2: apply RInc1.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
    + eapply segRLs_trans_add.
      * eapply segRLs_concat.
        1: esx.
        esx.
      * eapply segRLs_concat.
        2: apply IHls.
        eapply segRLs_wall; ss.
Qed.

Lemma RIncs1 n ls:
  segRLs tm (hRL^^n) (hRL^^n) (flat_map Rmp1 ls) (flat_map Rmp1 ls).
Proof.
  induction ls.
  - eapply segRLs_wall; ss.
  - cbn.
    eapply segRLs_concat.
    2: apply IHls.
    destruct a; eapply segRLs_wall; ss.
Qed.

Lemma RC0_spec n:
  RC0 n = flat_map Rmp0 ([false]^^n) *> 0inf.
Proof.
  unfold RC0.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma RC1_spec n:
  RC1 n = flat_map Rmp1 ([true]^^n) *> 0inf.
Proof.
  unfold RC1.
  rewrite flat_map_lpow.
  reflexivity.
Qed.

Lemma cnt1_all0 n:
  cnt1 ([false]^^n) = O.
Proof.
  induction n; cbn; lia.
Qed.

Lemma cnt1_all1 n:
  cnt1 ([true]^^n) = n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma RIncs ls n:
  sideRLs tm (hRL^^(length ls+cnt1 ls+n)) (flat_map Rmp0 ls *> 0inf) (flat_map Rmp1 (ls++[false]^^cnt1 ls++[true]^^n) *> 0inf).
Proof.
  rewrite app_assoc.
  rewrite flat_map_app.
  rewrite Str_app_assoc.
  rewrite <-RC1_spec.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs0.
  1: apply RC0_Incs.
  1: rewrite RC0_spec.
  1: eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  1: eapply segRLs_sideRLs_concat.
  1: applys_eq RIncs0; rewrite lpow_length; cbn; flia.
  1: apply RC0_Incs.
  rewrite RC0_spec.
  rewrite cnt1_all0.
  cbn[lpow].
  cbn[flat_map].
  cbn[Str_app].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs1.
  apply RC1_Incs.
Qed.
  
Lemma Rst k r:
  dh <* d1^^k {{{ (hL,L) }}} [0;0] *> r -->*
  dh <* d0^^k <* d1 {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition S '(k,ls) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} flat_map Rmp0 ls *> 0inf.

Lemma BigStep k ls:
  length ls+cnt1 ls<=(2^k-1)*2+1 ->
  S (k,ls) -->+
  S (1+k,map negb (ls++[false]^^cnt1 ls++[true]^^((2^k-1)*2+1-length ls-cnt1 ls))).
Proof.
  remember ((2^k-1)*2+1-length ls-cnt1 ls) as m.
  intros Hk.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    applys_eq (RIncs ls m); flia.
  - rewrite Rmp1_shift.
    follow Rst.
    finish.
Qed.

Lemma cnt1_negb ls:
  cnt1 (map negb ls) + cnt1 ls = length ls.
Proof.
  induction ls.
  - reflexivity.
  - destruct a; cbn; lia.
Qed.

Lemma cnt1_app a b:
  cnt1 (a++b) = cnt1 a + cnt1 b.
Proof.
  induction a as [|[|]]; cbn; lia.
Qed.

Lemma map_lpow {A B} (f:A->B) a n:
  map f (a^^n) = (map f a)^^n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite map_app,IHn.
    reflexivity.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,[false])%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls) => length ls+cnt1 ls<=(2^k-1)*2+1 ).
  2: cbn; lia.
  intros [k ls] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite length_map.
  repeat rewrite length_app.
  repeat rewrite lpow_length.
  cbn[length].
  repeat rewrite map_app.
  repeat rewrite cnt1_app.
  repeat rewrite map_lpow.
  cbn[map].
  cbn[negb].
  rewrite cnt1_all1.
  rewrite cnt1_all0.
  pose proof (cnt1_negb ls).
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_1RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0;0]).
Notation hL := (B,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Definition RC0 k n m := [1;0;0;1;0]^^k *> [1;1;0] *> [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Definition RC1 n m := [1;0;0;1;0]^^n *> [0;0;0;1;0]^^m *> 0inf.

Lemma RC0_Incs k n m:
  sideRLs tm (hRL^^(n+1)) (RC0 k n (2+m)) (RC1 (2+n+k) m).
Proof.
  unfold RC0,RC1.
  gen k.
  induction n; intros.
  - esx.
  - replace (S n+1) with (1+(n+1)) by lia.
    eapply sideRLs_trans_add.
    2: applys_eq (IHn (S k)); flia.
    esx.
Qed.

Lemma RC1_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n m) (RC1 (m+n) 0).
Proof.
  gen n.
  induction m; intros.
  - esx.
  - eapply sideRLs_trans_add with (n1:=1%nat).
    2: applys_eq (IHm (S n)); flia.
    unfold RC1; esx.
Qed.


Definition RC2 n m := [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Lemma RC2_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n 0) (RC2 n m).
Proof.
  unfold RC1,RC2.
  sideRLs_ind m.
Qed.

Definition S '(k,n,m) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RC0 0 n (2+m).

Lemma Rst k n m:
  dh <* d1^^k {{{ (hL,L) }}} RC2 (1+n) (2+m) -->*
  S (k,n,m).
Proof.
  unfold S,RC0,RC2.
  es.
Qed.

Lemma RIncs n m k:
  sideRLs tm (hRL^^((n+1)+m+k)) (RC0 0 n (2+m)) (RC2 (2+m+n) k).
Proof.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: apply RC0_Incs.
  1: apply RC1_Incs.
  applys_eq RC2_Incs; flia.
Qed.

Lemma BigStep k n m:
  n+m+2<=(2^k-1)*2 ->
  S (k,n,m) -->+
  S (1+k,1+n+m,(2^k-1)*2-(n+m+2)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-(n+m+2)) as a.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2+1) with ((n+1)+m+(2+a)) by lia.
    apply RIncs.
  - replace (2+m+n) with (1+(1+n+m)) by lia.
    follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n,m) => n+m+2<=(2^k-1)*2).
  2: cbn; lia.
  intros [[k n] m] HP.
  eexists (_,_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LE1RF_1LB---_0RA0RE").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0;0]).
Notation hL := (B,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Definition RC0 k n m := [1;0;0;1;0]^^k *> [1;1;0] *> [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Definition RC1 n m := [1;0;0;1;0]^^n *> [0;0;0;1;0]^^m *> 0inf.

Lemma RC0_Incs k n m:
  sideRLs tm (hRL^^(n+1)) (RC0 k n (2+m)) (RC1 (2+n+k) m).
Proof.
  unfold RC0,RC1.
  gen k.
  induction n; intros.
  - esx.
  - replace (S n+1) with (1+(n+1)) by lia.
    eapply sideRLs_trans_add.
    2: applys_eq (IHn (S k)); flia.
    esx.
Qed.

Lemma RC1_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n m) (RC1 (m+n) 0).
Proof.
  gen n.
  induction m; intros.
  - esx.
  - eapply sideRLs_trans_add with (n1:=1%nat).
    2: applys_eq (IHm (S n)); flia.
    unfold RC1; esx.
Qed.


Definition RC2 n m := [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Lemma RC2_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n 0) (RC2 n m).
Proof.
  unfold RC1,RC2.
  sideRLs_ind m.
Qed.

Definition S '(k,n,m) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RC0 0 n (2+m).

Lemma Rst k n m:
  dh <* d1^^k {{{ (hL,L) }}} RC2 (1+n) (2+m) -->*
  S (k,n,m).
Proof.
  unfold S,RC0,RC2.
  es.
Qed.

Lemma RIncs n m k:
  sideRLs tm (hRL^^((n+1)+m+k)) (RC0 0 n (2+m)) (RC2 (2+m+n) k).
Proof.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: apply RC0_Incs.
  1: apply RC1_Incs.
  applys_eq RC2_Incs; flia.
Qed.

Lemma BigStep k n m:
  n+m+2<=(2^k-1)*2 ->
  S (k,n,m) -->+
  S (1+k,1+n+m,(2^k-1)*2-(n+m+2)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-(n+m+2)) as a.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2+1) with ((n+1)+m+(2+a)) by lia.
    apply RIncs.
  - replace (2+m+n) with (1+(1+n+m)) by lia.
    follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n,m) => n+m+2<=(2^k-1)*2).
  2: cbn; lia.
  intros [[k n] m] HP.
  eexists (_,_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM27.


Module TM28.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA0RA_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0;0]).
Notation hL := (B,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Definition RC0 k n m := [1;0;0;1;0]^^k *> [1;1;0] *> [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Definition RC1 n m := [1;0;0;1;0]^^n *> [0;0;0;1;0]^^m *> 0inf.

Lemma RC0_Incs k n m:
  sideRLs tm (hRL^^(n+1)) (RC0 k n (2+m)) (RC1 (2+n+k) m).
Proof.
  unfold RC0,RC1.
  gen k.
  induction n; intros.
  - esx.
  - replace (S n+1) with (1+(n+1)) by lia.
    eapply sideRLs_trans_add.
    2: applys_eq (IHn (S k)); flia.
    esx.
Qed.

Lemma RC1_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n m) (RC1 (m+n) 0).
Proof.
  gen n.
  induction m; intros.
  - esx.
  - eapply sideRLs_trans_add with (n1:=1%nat).
    2: applys_eq (IHm (S n)); flia.
    unfold RC1; esx.
Qed.


Definition RC2 n m := [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Lemma RC2_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n 0) (RC2 n m).
Proof.
  unfold RC1,RC2.
  sideRLs_ind m.
Qed.

Definition S '(k,n,m) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RC0 0 n (2+m).

Lemma Rst k n m:
  dh <* d1^^k {{{ (hL,L) }}} RC2 (1+n) (2+m) -->*
  S (k,n,m).
Proof.
  unfold S,RC0,RC2.
  es.
Qed.

Lemma RIncs n m k:
  sideRLs tm (hRL^^((n+1)+m+k)) (RC0 0 n (2+m)) (RC2 (2+m+n) k).
Proof.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: apply RC0_Incs.
  1: apply RC1_Incs.
  applys_eq RC2_Incs; flia.
Qed.

Lemma BigStep k n m:
  n+m+2<=(2^k-1)*2 ->
  S (k,n,m) -->+
  S (1+k,1+n+m,(2^k-1)*2-(n+m+2)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-(n+m+2)) as a.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2+1) with ((n+1)+m+(2+a)) by lia.
    apply RIncs.
  - replace (2+m+n) with (1+(1+n+m)) by lia.
    follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n,m) => n+m+2<=(2^k-1)*2).
  2: cbn; lia.
  intros [[k n] m] HP.
  eexists (_,_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM28.


Module TM29.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA0LD_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[0;0]).
Notation hL := (B,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[0;0;1;0].
Notation d1 := <[1;0;1;0].
Notation dh := (0inf <* d1).

Lemma LIncs n:
  sideRLs tm' (hLR^^((2^n-1)*2)) (dh <* d0^^n <* d1) (dh <* d1^^(1+n)).
Proof.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Mul2.
  all: ss.
  all: ss.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  all: ss.
  esx.
Qed.

Definition RC0 k n m := [1;0;0;1;0]^^k *> [1;1;0] *> [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Definition RC1 n m := [1;0;0;1;0]^^n *> [0;0;0;1;0]^^m *> 0inf.

Lemma RC0_Incs k n m:
  sideRLs tm (hRL^^(n+1)) (RC0 k n (2+m)) (RC1 (2+n+k) m).
Proof.
  unfold RC0,RC1.
  gen k.
  induction n; intros.
  - esx.
  - replace (S n+1) with (1+(n+1)) by lia.
    eapply sideRLs_trans_add.
    2: applys_eq (IHn (S k)); flia.
    esx.
Qed.

Lemma RC1_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n m) (RC1 (m+n) 0).
Proof.
  gen n.
  induction m; intros.
  - esx.
  - eapply sideRLs_trans_add with (n1:=1%nat).
    2: applys_eq (IHm (S n)); flia.
    unfold RC1; esx.
Qed.


Definition RC2 n m := [1;0;0;1;0]^^n *> [1;0;0;0;0]^^m *> 0inf.

Lemma RC2_Incs n m:
  sideRLs tm (hRL^^m) (RC1 n 0) (RC2 n m).
Proof.
  unfold RC1,RC2.
  sideRLs_ind m.
Qed.

Definition S '(k,n,m) :=
  dh <* d0^^k <* d1 {{{ (hR,R) }}} RC0 0 n (2+m).

Lemma Rst k n m:
  dh <* d1^^k {{{ (hL,L) }}} RC2 (1+n) (2+m) -->*
  S (k,n,m).
Proof.
  unfold S,RC0,RC2.
  es.
Qed.

Lemma RIncs n m k:
  sideRLs tm (hRL^^((n+1)+m+k)) (RC0 0 n (2+m)) (RC2 (2+m+n) k).
Proof.
  eapply sideRLs_trans_add.
  1: eapply sideRLs_trans_add.
  1: apply RC0_Incs.
  1: apply RC1_Incs.
  applys_eq RC2_Incs; flia.
Qed.

Lemma BigStep k n m:
  n+m+2<=(2^k-1)*2 ->
  S (k,n,m) -->+
  S (1+k,1+n+m,(2^k-1)*2-(n+m+2)).
Proof.
  intros Hn.
  remember ((2^k-1)*2-(n+m+2)) as a.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((2^k-1)*2+1) with ((n+1)+m+(2+a)) by lia.
    apply RIncs.
  - replace (2+m+n) with (1+(1+n+m)) by lia.
    follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(2,0,1)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n,m) => n+m+2<=(2^k-1)*2).
  2: cbn; lia.
  intros [[k n] m] HP.
  eexists (_,_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM29.


Module TM30.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC1RE_1RD1LF_1RB---_0RF0RA_0LA0RB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[1]).
Notation hL := (F,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[1;0;1;1].
Notation d1 := <[1;0;0;0].
Notation dh0 := (0inf <* <[0;1;1]).
Notation dh1 := (0inf <* <[0;0;0]).

Lemma LIncs n:
  sideRLs tm' (hLR^^((4^n*4-1))) (dh0 <* d0^^n) (dh1 <* d1^^n).
Proof.
  induction n.
  1: esx.
  remember (4^n*4-1) as k.
  replace (4^S n*4-1) with (k*4+3) by (cbn in *; lia).
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 n m :=
  [0;1;1]^^n *> [1;0;1]^^m *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(n)) (RC0 0 (n+m)) (RC0 n m).
Proof.
  unfold RC0.
  gen m.
  induction n; intros.
  - esx.
  - specialize (IHn (S m)).
    eapply sideRLs_trans_S.
    1: applys_eq IHn; flia.
    esx.
Qed.

Definition RC1 m :=
  [0;1] *> [1;0;1]^^m *> 0inf.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(1+m)) (RC0 (1+n) 0) (RC1 (1+m+n)).
Proof.
  unfold RC0,RC1.
  sideRLs_ind m.
Qed.

Definition S '(k,n) :=
  dh0 <* d0^^k {{{ (hR,R) }}} RC0 0 (1+n).

Lemma Rst k n:
  dh1 <* d1^^k {{{ (hL,L) }}} RC1 (1+n) -->*
  S (1+k,n).
Proof.
  unfold S,RC0,RC1.
  es.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^((1+n)+(1+m))) (RC0 0 (1+n)) (RC1 (1+m+n)).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (RIncs0 (1+n) 0); flia.
  1: apply RIncs1.
Qed.

Lemma BigStep k n:
  n+2<=(4^k*4) ->
  S (k,n) -->+
  S (1+k,4^k*4-2).
Proof.
  intros Hn.
  remember (4^k*4-2-n) as a.
  unfold S.
  epose proof (sideRLs_concat (LIncs _)) as I1.
  eapply progress_evstep_trans.
  - apply I1.
    rewrite lrcons_lpow1'.
    replace ((4^k*4-1)+1) with ((1+n)+(1+a)) by lia.
    apply RIncs.
  - replace (1+a+n) with (1+(a+n)) by lia.
    follow Rst.
    unfold S.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S(1,2)%nat).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,n) => n+2<=(4^k*4)).
  2: cbn; lia.
  intros [k n] HP.
  eexists (_,_); split.
  1: apply BigStep; lia.
  rewrite Nat.pow_add_r by lia.
  lia.
Qed.

End TM30.


