From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.


Open Scope list.

Lemma lrcons_lpow1' h1 h2 n:
  lrcons h1 ([(h2, h1)] ^^ n) h2 = [(h1, h2)] ^^ (n+1).
Proof.
  applys_eq lrcons_lpow1; flia.
Qed.

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

Lemma sideRLs_wall tm h n l l' w:
  segRLs tm h h w w ->
  sideRLs tm (h^^n) l l' ->
  sideRLs tm (h^^n) (l<*w) (l'<*w).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  apply segRLs_wall'',H.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.



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


Module TM31.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RE_0RA0LD_1LB0RE_1RC0LA_0RD---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[1;0]).
Notation hL := (D,[0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[1;0;1;0;0;0].
Notation d1 := <[1;0;1;0;1;1].
Notation d2 := <[1;0;1;0;1;0].
Notation dh0 := (0inf <* <[1;1]).
Notation dh1 := (0inf <* <[1;0]).

Lemma LIncs n:
  sideRLs tm' (hLR^^(3^n*2-1)) (dh0<*d0^^n) (dh1<*d2^^n).
Proof.
  induction n.
  1: esx.
  cbn[lpow].
  do 2 rewrite Str_app_assoc.
  replace (3^S n*2-1) with ((3^n*2-1)*3+2) by (cbn[Nat.pow]; lia).
  eapply segRLs_sideRLs_concat.
  2: apply IHn.
  apply segRLs_addmul''; esx.
Qed.

Definition RC0 a b := [1;0;1;0;0]^^a *> [1;0;0] *> [1;0;1;0;0]^^b *> 0inf.

Lemma RIncs0 a b:
  sideRLs tm (hRL^^(b*2)) (RC0 a b) (RC0 (a+b) 0).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  gen a.
  induction b; intros.
  1: esx.
  replace (S b) with (1+b) by lia.
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (1+a)); flia.
  esx.
Qed.

Definition RC n := [1;0;1;0;0]^^n *> 0inf.

Lemma RIncs1 k n:
  sideRLs tm (hRL^^(k*2)) (RC n) (RC (k+n)).
Proof.
  unfold RC.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^(n*2+(1+m*2))) (RC0 0 n) (RC (m+(n+1))).
Proof.
  eapply sideRLs_trans_add.
  1: apply RIncs0.
  eapply sideRLs_trans_add.
  2: apply RIncs1.
  unfold RC0,RC.
  esx.
Qed.

Definition S1 l a b :=
  l <* <[1;0;1;1;0]^^a {{{ (hL,L) }}} RC0 0 b.

Lemma Inc1 l a b:
  S1 l (2+a) b -->*
  S1 l a (3+b).
Proof.
  unfold S1,RC0.
  es.
Qed.

Lemma Incs1 l a b:
  S1 l (a*2) b -->*
  S1 l 0 (a*3+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Definition S' '(a,b) := dh1 <* d2^^a {{{ (hL,L) }}} RC b.

Lemma BigStep a b c:
  (3^(1+a)*2-1 = (b*3+0)*2+(1+c*2)) ->
  S' (a,1+b*2) -->+
  S' (1+a,c+b*3+1).
Proof.
  intros Hc.
  unfold S',RC.
  mid10 (S1 (dh0<*d0^^(1+a)) (b*2) 0).
  1: unfold S1,RC0; es.
  follow Incs1.
  unfold S1.
  epose proof (RIncs (b*3+0) c) as I1.
  rewrite <-Hc in I1.
  epose proof (sideRLs_concat_1L I1 (LIncs (1+a))) as I.
  follow I.
  unfold RC.
  finish.
Qed.

Definition S0 n := S' (n,3^n).

Lemma pow3_mod2 n:
  3^n mod 2 = 1%nat.
Proof.
  induction n; cbn[Nat.pow]; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 O).
  1: esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold S0.
  cbn[Nat.pow].
  pose proof (pow3_mod2 i).
  applys_eq (BigStep i (3^i/2) (3^i/2*3+2));
  repeat rewrite Nat.pow_add_r; flia.
Qed.

End TM31.


Module TM32.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RD_1LB1RA_0RC1LE_---0LF_0LD1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[1;1]).
Notation hL := (F,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[1;1;0;1].
Notation d1 := <[1;1;1;1].
Notation dx := <[1;1;0;1;1;1;1].
Notation w0 := (d0 <+ dx).
Notation w1 := (d1 <+ dx).
Notation dh := (0inf <* <[1;1]).

Notation "l <| r" := (l <{{F}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l {{A}}> r) (at level 30).

Definition LOv l l' := forall r, l <| r -->* l' |> r.

Fixpoint LC0 ls n d :=
match ls with
| (a,b)::t =>
  LC0 t n d <* w0^^b <* d <* w1^^a <* d0 <* w1 <* dx
| [] => dh <* d^^n <* d0 <* w0 <* dx
end.

Fixpoint LC1 ls n d :=
match ls with
| (a,b)::t =>
  LC1 t n d <* w1^^b <* w0^^a <* d <* w0 <* w1
| [] => dh <* d^^n <* d1 <* w1 <* dx
end.

Lemma LC0_Ov ls n:
  LOv (LC0 ls n d1) (LC1 ls (1+n) d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LC1_Ov ls n:
  LOv (LC1 ls n d1) (LC0 ls n d0 <* d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LIncs_d0 n l l':
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+1)) (l<*d0) (l'<*d1).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_addmul''; esx.
Qed.

Lemma LIncs_d0s n l:
  sideRLs tm' (hLR^^(2^n-1)) (l<*d0^^n) (l<*d1^^n).
Proof.
  induction n.
  - esx.
  - cbn[Nat.pow].
    apply LIncs_d0 in IHn.
    applys_eq IHn; flia.
Qed.

Lemma wall3 n l l' a b c d e f:
  sideRLs tm' (hLR^^n) (l<*(a<+b<+c)) (l'<*(d<+e<+f)) ->
  sideRLs tm' (hLR^^n) (l<*a<*b<*c) (l'<*d<*e<*f).
Proof.
  st.
  tauto.
Qed.

Lemma LIncs0 ls n:
  sideRLs tm' (hLR^^(2^(length ls+n)-1)) (LC0 ls n d0) (LC0 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC0].
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+n)-1) with ((2^(length ls+n)-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Lemma LIncs1 ls n:
  sideRLs tm' (hLR^^(2^(length ls+n)-1)) (LC1 ls n d0) (LC1 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC1].
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+n)-1) with ((2^(length ls+n)-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Notation d1' := [0;1;0;1].
Notation w0' := [0;1;0;1;0;1;0;0;1;0;1].
Notation w1' := [0;1;0;1;0;0;1;0;1;0;1].

Definition RC3 n := w0'^^n *> [0;1;0;1;0;0;1;0;1] *> 0inf.
Definition RC0 n m := w0'^^n *> d1' *> w1'^^m *> [0;0;1;0;1] *> 0inf.

Definition RC1 k n := w1'^^k *> w0'^^n *> d1' *> w0' *> [0;1] *> 0inf.
Definition RC2 k n m := w1'^^k *> w0'^^n *> d1' *> w0' *> w1'^^m *> [0;1;0;0;1] *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(m*3)) (RC3 n) (RC0 n (m*2)).
Proof.
  unfold RC0,RC3.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma RIncs2 k n m:
  sideRLs tm (hRL^^(1+m*3)) (RC1 k n) (RC2 k n (m*2)).
Proof.
  unfold RC1,RC2.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma LC0_Ov_1 ls n n0 n1:
  LC0 ls n d1 <| RC0 n0 n1 -->*
  LC1 ls (1+n) d0 <| RC1 n0 n1.
Proof.
  unfold RC0,RC1.
  es; er.
  follow LC0_Ov.
  es.
Qed.

Lemma lpow_unrotate_11 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Local Ltac ES_v2.rw_unrotate_0 ::=
  rewrite lpow_unrotate_11.

Lemma LC1_Ov_1 ls n n0 n1 n2:
  LC1 ls n d1 <| RC2 n0 n1 (1+n2) -->+
  LC0 ((n1,n0)::ls) n d0 <| RC3 n2.
Proof.
  unfold RC2,RC3.
  es; er.
  follow LC1_Ov.
  do 3 (er; sr).
  es_v2.
Qed.

Lemma pow4_mod3 i:
  2^(i*2) mod 3 = 1%nat.
Proof.
  induction i; cbn - [Nat.modulo]; lia.
Qed.

Definition S' '(ls,n,n0,n1) :=
  LC0 ls n d1 <| RC0 n0 n1.

Lemma init:
  c0 -->*
  S' ([(3,O)],3,3,10).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n,n0,n1) => ((length ls)+n) mod 2 = O /\ (length ls)+n >= 2).
  2: cbn; lia.
  intros [[[ls n] n0] n1] HP.
  eexists (_,_,_,_); split.
  - unfold S'.
    follow LC0_Ov_1.
    epose proof (LIncs1 ls (1+n)) as I1.
    remember (length ls) as len.
    replace ((len+(1+n))) with (S((len+n)/2*2)) in I1 by lia.
    cbn[Nat.pow] in I1.
    pose proof (pow4_mod3 ((len+n)/2)) as Hm.
    remember (2 * 2 ^ ((len + n) / 2 * 2) - 1) as v1.
    replace v1 with (1+v1/3*3) in I1 by lia.
    epose proof (sideRLs_concat_1L (RIncs2 _ _ _) I1) as I.
    follow I.
    unfold to_DH_config.
    epose proof (Nat.pow_le_mono_r 2 2 ((len+n)/2*2)).
    replace (v1/3*2) with (1+(v1/3*2-1)) by lia.
    follow10 LC1_Ov_1.
    epose proof (LIncs0 ((n1,n0)::ls) (1+n)) as I2.
    cbn[length] in I2.
    replace (S(length ls)+(1+n)) with (S(S(((len+n)/2)*2))) in I2 by lia.
    cbn[Nat.pow] in I2.
    remember (2 * (2 * 2 ^ ((len + n) / 2 * 2)) - 1) as v2.
    replace v2 with (v2/3*3) in I2 by lia.
    epose proof (sideRLs_concat_1L (RIncs0 _ _) I2) as I'.
    unfold to_DH_config in I'.
    follow I'.
    subst.
    finish.
  - cbn[length]; lia.
Qed.

End TM32.


Module TM33.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA1RD_1RB0LD_0RA1LE_---0LF_0LD1LB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,<[1;1]).
Notation hL := (F,[0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[1;1;0;1].
Notation d1 := <[1;1;1;1].
Notation dx := <[1;1;0;1;1;1;1].
Notation w0 := (d0 <+ dx).
Notation w1 := (d1 <+ dx).
Notation dh := (0inf <* <[1;1]).

Notation "l <| r" := (l <{{F}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l {{C}}> r) (at level 30).

Definition LOv l l' := forall r, l <| r -->* l' |> r.

Fixpoint LC0 ls n d :=
match ls with
| (a,b)::t =>
  LC0 t n d <* w0^^b <* d <* w1^^a <* d0 <* w1 <* dx
| [] => dh <* d^^n <* d0^^2 <* w1 <* dx <* w0^^3 <* dx <* w1^^2 <* d0 <* w1 <* dx
end.

Fixpoint LC1 ls n d :=
match ls with
| (a,b)::t =>
  LC1 t n d <* w1^^b <* w0^^a <* d <* w0 <* w1
| [] => dh <* d^^n <* d0 <* d1 <* w0 <* w1^^4 <* dx^^2 <* w0 <* d <* w0 <* w1
end.

Lemma LC0_Ov ls n:
  LOv (LC0 ls n d1) (LC1 ls n d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LC1_Ov ls n:
  LOv (LC1 ls n d1) (LC0 ls (1+n) d0 <* d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LIncs_d0 n l l':
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+1)) (l<*d0) (l'<*d1).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_addmul''; esx.
Qed.

Lemma LIncs_d0s n l:
  sideRLs tm' (hLR^^(2^n-1)) (l<*d0^^n) (l<*d1^^n).
Proof.
  induction n.
  - esx.
  - cbn[Nat.pow].
    apply LIncs_d0 in IHn.
    applys_eq IHn; flia.
Qed.

Lemma wall3 n l l' a b c d e f:
  sideRLs tm' (hLR^^n) (l<*(a<+b<+c)) (l'<*(d<+e<+f)) ->
  sideRLs tm' (hLR^^n) (l<*a<*b<*c) (l'<*d<*e<*f).
Proof.
  st.
  tauto.
Qed.

Lemma LIncs0 ls n:
  sideRLs tm' (hLR^^(2^(length ls+n)-1)) (LC0 ls n d0) (LC0 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC0].
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    apply wall3.
    apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+n)-1) with ((2^(length ls+n)-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Lemma LIncs1 ls n:
  sideRLs tm' (hLR^^(2^(length ls+(1+n))-1)) (LC1 ls n d0) (LC1 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC1].
  - apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    cbn[Nat.add].
    cbn[Nat.pow].
    replace (2*2^n-1) with ((2^n-1)*2+1) by lia.
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply wall3.
    apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+(1+n))-1) with ((2^(length ls+(1+n))-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Notation d1' := [0;1;0;1].
Notation w0' := [0;1;0;1;0;1;0;0;1;0;1].
Notation w1' := [0;1;0;1;0;0;1;0;1;0;1].

Definition RC3 n := w0'^^n *> [0;1;0;1;0;0;1;0;1] *> 0inf.
Definition RC0 n m := w0'^^n *> d1' *> w1'^^m *> [0;0;1;0;1] *> 0inf.

Definition RC1 k n := w1'^^k *> w0'^^n *> d1' *> w0' *> [0;1] *> 0inf.
Definition RC2 k n m := w1'^^k *> w0'^^n *> d1' *> w0' *> w1'^^m *> [0;1;0;0;1] *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(m*3)) (RC3 n) (RC0 n (m*2)).
Proof.
  unfold RC0,RC3.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma RIncs2 k n m:
  sideRLs tm (hRL^^(1+m*3)) (RC1 k n) (RC2 k n (m*2)).
Proof.
  unfold RC1,RC2.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma LC0_Ov_1 ls n n0 n1:
  LC0 ls n d1 <| RC0 n0 n1 -->*
  LC1 ls n d0 <| RC1 n0 n1.
Proof.
  unfold RC0,RC1.
  es; er.
  follow LC0_Ov.
  es.
Qed.

Lemma lpow_unrotate_11 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Local Ltac ES_v2.rw_unrotate_0 ::=
  rewrite lpow_unrotate_11.

Lemma LC1_Ov_1 ls n n0 n1 n2:
  LC1 ls n d1 <| RC2 n0 n1 (1+n2) -->+
  LC0 ((n1,n0)::ls) (1+n) d0 <| RC3 n2.
Proof.
  unfold RC2,RC3.
  es; er.
  follow LC1_Ov.
  do 3 (er; sr).
  es_v2.
Qed.

Lemma pow4_mod3 i:
  2^(i*2) mod 3 = 1%nat.
Proof.
  induction i; cbn - [Nat.modulo]; lia.
Qed.

Definition S' '(ls,n,n0,n1) :=
  LC0 ls n d1 <| RC0 n0 n1.

Lemma init:
  c0 -->*
  S' ([],4,3,10).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n,n0,n1) => ((length ls)+n) mod 2 = O /\ (length ls)+n >= 2).
  2: cbn; lia.
  intros [[[ls n] n0] n1] HP.
  eexists (_,_,_,_); split.
  - unfold S'.
    follow LC0_Ov_1.
    epose proof (LIncs1 ls n) as I1.
    remember (length ls) as len.
    replace ((len+(1+n))) with (S((len+n)/2*2)) in I1 by lia.
    cbn[Nat.pow] in I1.
    pose proof (pow4_mod3 ((len+n)/2)) as Hm.
    remember (2 * 2 ^ ((len + n) / 2 * 2) - 1) as v1.
    replace v1 with (1+v1/3*3) in I1 by lia.
    epose proof (sideRLs_concat_1L (RIncs2 _ _ _) I1) as I.
    follow I.
    unfold to_DH_config.
    epose proof (Nat.pow_le_mono_r 2 2 ((len+n)/2*2)).
    replace (v1/3*2) with (1+(v1/3*2-1)) by lia.
    follow10 LC1_Ov_1.
    epose proof (LIncs0 ((n1,n0)::ls) (1+n)) as I2.
    cbn[length] in I2.
    replace (S(length ls)+(1+n)) with (S(S(((len+n)/2)*2))) in I2 by lia.
    cbn[Nat.pow] in I2.
    remember (2 * (2 * 2 ^ ((len + n) / 2 * 2)) - 1) as v2.
    replace v2 with (v2/3*3) in I2 by lia.
    epose proof (sideRLs_concat_1L (RIncs0 _ _) I2) as I'.
    unfold to_DH_config in I'.
    follow I'.
    subst.
    finish.
  - cbn[length]; lia.
Qed.

End TM33.


Module TM34.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RC_0LE0LD_0LB0RD_1RA1RE_0RB---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,<[1;1;0]).
Notation hL := (C,[1;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := <[1;1;0;0].
Notation d1 := <[1;1;1;1].
Notation dx := <[1;1;0;0;1;1;1].
Notation w0 := (d0 <+ dx).
Notation w1 := (d1 <+ dx).
Notation dh := (0inf <* <[1;1]).

Notation "l <| r" := (l <{{C}} [1;0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{C}}> r) (at level 30).

Definition LOv l l' := forall r, l <| r -->* l' |> r.

Fixpoint LC0 ls n d :=
match ls with
| (a,b)::t =>
  LC0 t n d <* w0^^b <* d <* w1^^a <* d0 <* w1 <* dx
| [] => dh <* d^^n <* d0 <* w0 <* dx
end.

Fixpoint LC1 ls n d :=
match ls with
| (a,b)::t =>
  LC1 t n d <* w1^^b <* w0^^a <* d <* w0 <* w1
| [] => dh <* d^^n <* d1 <* w1 <* dx
end.

Local Ltac use_shift_rule ::= use_shift_rule'.

Lemma LC0_Ov ls n:
  LOv (LC0 ls n d1) (LC1 ls (1+n) d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LC1_Ov ls n:
  LOv (LC1 ls n d1) (LC0 ls n d0 <* d0).
Proof.
  unfold LOv.
  induction ls as [|[a b] ls]; cbn[LC0]; cbn[LC1].
  - es.
  - es; er.
    follow.
    es.
Qed.

Lemma LIncs_d0 n l l':
  sideRLs tm' (hLR^^n) l l' ->
  sideRLs tm' (hLR^^(n*2+1)) (l<*d0) (l'<*d1).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  eapply segRLs_addmul''; esx.
Qed.

Lemma LIncs_d0s n l:
  sideRLs tm' (hLR^^(2^n-1)) (l<*d0^^n) (l<*d1^^n).
Proof.
  induction n.
  - esx.
  - cbn[Nat.pow].
    apply LIncs_d0 in IHn.
    applys_eq IHn; flia.
Qed.

Lemma wall3 n l l' a b c d e f:
  sideRLs tm' (hLR^^n) (l<*(a<+b<+c)) (l'<*(d<+e<+f)) ->
  sideRLs tm' (hLR^^n) (l<*a<*b<*c) (l'<*d<*e<*f).
Proof.
  st.
  tauto.
Qed.

Lemma LIncs0 ls n:
  sideRLs tm' (hLR^^(2^(length ls+n)-1)) (LC0 ls n d0) (LC0 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC0].
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+n)-1) with ((2^(length ls+n)-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Lemma LIncs1 ls n:
  sideRLs tm' (hLR^^(2^(length ls+n)-1)) (LC1 ls n d0) (LC1 ls n d1).
Proof.
  induction ls as [|[a b] ls]; cbn[length]; cbn[LC1].
  - apply wall3.
    apply sideRLs_wall.
    1: esx.
    apply LIncs_d0s.
  - apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    replace (2^(S(length ls)+n)-1) with ((2^(length ls+n)-1)*2+1) by (cbn; lia).
    apply LIncs_d0.
    apply sideRLs_wall.
    1: esx.
    apply sideRLs_wall.
    1: esx.
    apply IHls.
Qed.

Notation d1' := [0;1;0;1].
Notation w0' := [0;1;0;1;0;1;0;0;1;0;1].
Notation w1' := [0;1;0;1;0;0;1;0;1;0;1].

Definition RC3 n := w0'^^n *> [0;1;0;1;0;0;1;0;1] *> 0inf.
Definition RC0 n m := w0'^^n *> d1' *> w1'^^m *> [0;0;1;0;1] *> 0inf.

Definition RC1 k n := w1'^^k *> w0'^^n *> d1' *> w0' *> [0;1] *> 0inf.
Definition RC2 k n m := w1'^^k *> w0'^^n *> d1' *> w0' *> w1'^^m *> [0;1;0;0;1] *> 0inf.

Lemma RIncs0 n m:
  sideRLs tm (hRL^^(m*3)) (RC3 n) (RC0 n (m*2)).
Proof.
  unfold RC0,RC3.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma RIncs2 k n m:
  sideRLs tm (hRL^^(1+m*3)) (RC1 k n) (RC2 k n (m*2)).
Proof.
  unfold RC1,RC2.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind m.
Qed.

Lemma LC0_Ov_1 ls n n0 n1:
  LC0 ls n d1 <| RC0 n0 n1 -->*
  LC1 ls (1+n) d0 <| RC1 n0 n1.
Proof.
  unfold RC0,RC1.
  es; er.
  follow LC0_Ov.
  es.
Qed.

Lemma lpow_unrotate_11 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Local Ltac ES_v2.rw_unrotate_0 ::=
  rewrite lpow_unrotate_11.

Lemma LC1_Ov_1 ls n n0 n1 n2:
  LC1 ls n d1 <| RC2 n0 n1 (1+n2) -->+
  LC0 ((n1,n0)::ls) n d0 <| RC3 n2.
Proof.
  unfold RC2,RC3.
  es; er.
  follow LC1_Ov.
  do 3 (er; sr).
  es_v2.
Qed.

Lemma pow4_mod3 i:
  2^(i*2) mod 3 = 1%nat.
Proof.
  induction i; cbn - [Nat.modulo]; lia.
Qed.

Definition S' '(ls,n,n0,n1) :=
  LC0 ls n d1 <| RC0 n0 n1.

Lemma init:
  c0 -->*
  S' ([(3,O)],3,3,10).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n,n0,n1) => ((length ls)+n) mod 2 = O /\ (length ls)+n >= 2).
  2: cbn; lia.
  intros [[[ls n] n0] n1] HP.
  eexists (_,_,_,_); split.
  - unfold S'.
    follow LC0_Ov_1.
    epose proof (LIncs1 ls (1+n)) as I1.
    remember (length ls) as len.
    replace ((len+(1+n))) with (S((len+n)/2*2)) in I1 by lia.
    cbn[Nat.pow] in I1.
    pose proof (pow4_mod3 ((len+n)/2)) as Hm.
    remember (2 * 2 ^ ((len + n) / 2 * 2) - 1) as v1.
    replace v1 with (1+v1/3*3) in I1 by lia.
    epose proof (sideRLs_concat_1L (RIncs2 _ _ _) I1) as I.
    follow I.
    unfold to_DH_config.
    epose proof (Nat.pow_le_mono_r 2 2 ((len+n)/2*2)).
    replace (v1/3*2) with (1+(v1/3*2-1)) by lia.
    follow10 LC1_Ov_1.
    epose proof (LIncs0 ((n1,n0)::ls) (1+n)) as I2.
    cbn[length] in I2.
    replace (S(length ls)+(1+n)) with (S(S(((len+n)/2)*2))) in I2 by lia.
    cbn[Nat.pow] in I2.
    remember (2 * (2 * 2 ^ ((len + n) / 2 * 2)) - 1) as v2.
    replace v2 with (v2/3*3) in I2 by lia.
    epose proof (sideRLs_concat_1L (RIncs0 _ _) I2) as I'.
    unfold to_DH_config in I'.
    follow I'.
    subst.
    finish.
  - cbn[length]; lia.
Qed.

End TM34.


Module TM35.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LB0RC_0RD1RC_1LE0LA_1LD---_1LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (C,<[1;0]).
Notation hR := (C,[1]).
Notation hL := (F,[]).
Notation hRL := [(hR,hL)].
Notation hLR' := [(hL,hR')].
Notation hLR := [(hL,hR)].
Notation w0 := <[1;0].
Notation w1 := <[1].

Definition tm' := flip tm.

Definition RC n m := [1]^^n *> [0;0] *> [1;1]^^m *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC n m) (RC 0 (n+m)).
Proof.
  unfold RC.
  gen m.
  induction n; intros.
  1: esx.
  replace (S n) with (1+n) by lia.
  eapply sideRLs_trans_add.
  2: applys_eq (IHn (S m)); flia.
  esx.
Qed.

Definition LC i := 0inf <* w0^^i.

Lemma pow2_ge i:
  2^i >= i+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma LIncs i:
  sideRLs tm' (hLR^^i++hLR'++hLR^^(2^i*2-2-i)) (LC i) (LC i).
Proof.
  induction i.
  1: esx.
  pose proof (pow2_ge i).
  cbn[Nat.pow].
  remember (2^i*2-2-i) as j.
  replace (2*2^i*2-2-S i) with (j+(i+1+j)) by lia.
  rewrite lpow_add.
  change (LC (S i)) with (w0*>LC i).
  do 2 rewrite app_assoc.
  eapply sideRLs_trans.
  2:{
    eapply @segRLs_sideRLs_concat with (w1:=w1).
    2: apply IHi.
    do 2 rewrite lpow_add.
    rewrite <-app_assoc.
    eapply segRLs_trans.
    1: apply segRLs_wall''; esx.
    eapply segRLs_trans.
    2: apply segRLs_wall''; esx.
    esx.
  }
  eapply segRLs_sideRLs_concat.
  2: apply IHi.
  replace (S i) with (i+1) by lia.
  rewrite lpow_add.
  do 2 rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  rewrite app_assoc.
  eapply segRLs_trans.
  2: apply segRLs_wall''; esx.
  esx.
Qed.

Lemma LIncs' i:
  sideRLs tm' (hLR^^(2^i*2-1)) (LC i <* w1) (LC (S i)).
Proof.
  change (LC (S i)) with (w0*>LC i).
  epose proof (LIncs i) as I1.
  epose proof (pow2_ge i).
  remember (2^i*2-2-i) as j.
  replace (2^i*2-1) with (i+1+j) by lia.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_sideRLs_concat.
  2: apply I1.
  eapply segRLs_trans.
  1: apply segRLs_wall''; esx.
  eapply segRLs_trans.
  2: apply segRLs_wall''; esx.
  esx.
Qed.

Definition S' i := LC i <* w1 {{{ (hR,R) }}} RC (2^i*2-1) 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: esx.
  eapply progress_nonhalt_simple.
  intros i.
  exists (S i).
  unfold S'.
  epose proof (sideRLs_concat_1 (RIncs _ _) (LIncs' _)) as I1.
  follow I1. clear I1.
  cbn[Nat.pow].
  remember (2^i*2-1) as v1.
  replace (2*2^i*2-1) with (v1*2+1) by lia.
  unfold LC,RC.
  es.
Qed.

End TM35.


Module TM36.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (B,<[0;0]).
Notation hR := (A,<[1;0]).
Notation hR' := (D,<[1;0;0;0]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation ld := [1;0;1;0].
Notation lh := (0inf<*<[1;0]).
Notation hD := [((D,<[0;0]),hL)].
Notation m0 := [1;0;1;0;0;1;0].
Definition hX(a b:bool) := [((if a then A else C,if b then <[0;0;1;1;1] else <[1;0;1;1;1]),hL)].
Definition w(a:bool) := if a then [1;0;0;1;0] else [1;0;0;0;0].
Definition hXs a b n := hX a b ++ hD^^n.

Lemma hX_w a b n c:
  segRLs tm (hXs a b (1+n)) (hXs (negb c) a n) (w c) (w b).
Proof.
  destruct a,b,c;
  unfold hXs,negb,hX,w.
  all:
  rewrite lpow_add,app_assoc;
  eapply segRLs_trans;
  [|apply segRLs_wall''; esc];
  esc.
Qed.

Lemma hX_rh a b n:
  sideRLs tm (hXs a b n) 0inf ((if b then (w false)^^2 else (w true))*>(w false)^^n*>0inf).
Proof.
  destruct a,b;
  unfold hXs,hX,w.
  all:
  eapply sideRLs_trans; [esc|];
  sideRLs_ind n.
Qed.

Close Scope sym.

Lemma LIncs k:
  segRLs tm h' (h'++h^^(2^k-1)) (ld^^k) (ld^^k).
Proof.
  induction k.
  1: esc.
  cbn[Nat.pow].
  replace (S k) with (k+1) by lia.
  rewrite lpow_add.
  eapply segRLs_concat.
  1: apply IHk.
  replace (2*2^k-1) with (1+(2^k-1)*2) by lia.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  1: esx.
  am 1 2 (2^k-1) 0 0.
Qed.

Lemma m0_Ov n a:
  segRLs tm (h'++h^^(1+n)) (hXs (negb a) false (1+n*2)) (m0++(w a)) (ld++m0).
Proof.
  unfold hXs.
  do 2 rewrite lpow_add,app_assoc.
  destruct a.
  all:
  eapply segRLs_trans;
  [|rewrite lpow_mul; eapply segRLs_wall''; esc]; esc.
Qed.

Open Scope sym.

Inductive RC: nat->side->Prop :=
| RC_O:
  RC 0 0inf
| RC_S n c r:
  RC n r ->
  RC (S n) (w c*>r)
.

Lemma RC_lpow c n:
  RC n (w c^^n*>0inf).
Proof.
  induction n.
  1: ec.
  st; ec; trivial.
Qed.

Local Opaque w.

Lemma RIncs a b m n r:
  n<=m ->
  RC n r ->
  exists n' r',
  sideRLs tm (hXs a b m) r r' /\
  RC n' r' /\
  m+1<=n'<=m+2.
Proof.
  gen a b m r.
  induction n; intros.
  - inverts H0.
    destruct b; (do 3 ec; [apply hX_rh|ec]).
    1: st; ec; ec; apply RC_lpow.
    2: ec; apply RC_lpow.
    all: lia.
  - inverts H0.
    destruct m.
    1: lia.
    eapply IHn with (m:=m) in H2.
    2: lia.
    destruct H2 as [n' [r' [I1 [I2 I3]]]].
    do 3 ec.
    1: eapply segRLs_sideRLs_concat.
    1: apply hX_w.
    1: apply I1.
    split.
    ec; apply I2.
    lia.
Qed.

Lemma Incs k n r:
  RC n r ->
  2<=1+n<=2^k*2-2/\1<=k ->
  exists n' r',
  sideRLs tm h' (ld^^k*>m0*>r) (ld^^(k+1)*>m0*>r') /\
  RC n' r' /\
  2^k*2-2<=n'<=2^k*2-1.
Proof.
  intros.
  destruct n; [lia|].
  inverts H.
  assert (2<=2^k) by (destruct k; cbn[Nat.pow]; lia).
  eapply RIncs in H2.
  2: shelve.
  destruct H2 as [n' [r' [I1 [I2 I3]]]].
  do 3 ec.
  - rewrite lpow_add,Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: apply LIncs.
    do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (m0_Ov (2^k-2) c); flia. 
    apply I1.
  - split.
    1: apply I2.
    lia.
  Unshelve.
  1: lia.
Qed.

Definition S' '(k,r) := lh {{{ (hR',R) }}} ld^^k *> m0 *> r.

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR',R) }}} r.
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,w false^^3*>0inf)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,r) => exists n, RC n r /\ 2^k-1<=1+n<=2^k /\ 2<=k).
  2:{
    ec; ec.
    1: apply RC_lpow.
    lia.
  }
  intros [k r] [n [I1 [I2 I3]]].
  assert (I4:2^2<=2^k) by (apply Nat.pow_le_mono_r; lia).
  eapply Incs with (k:=k) in I1.
  2: lia.
  destruct I1 as [n' [r' [I5 [I6 I7]]]].
  eapply sideRLs_1 in I5.
  eexists (_,_); ec.
  - unfold S'.
    follow10 I5.
    apply LRst.
  - ec; ec.
    1: apply I6.
    rewrite Nat.pow_add_r; lia.
Qed.

End TM36.


Module TM37.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (A,<[0;0]).
Notation hR := (D,<[1;0]).
Notation hR' := (C,<[1;0;0;0]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation ld := [1;0;1;0].
Notation lh := (0inf<*<[1;0]).
Notation hD := [((C,<[0;0]),hL)].
Notation m0 := [1;0;1;0;0;1;0].
Definition hX(a b:bool) := [((if a then D else B,if b then <[0;0;1;1;1] else <[1;0;1;1;1]),hL)].
Definition w(a:bool) := if a then [1;0;0;1;0] else [1;0;0;0;0].
Definition hXs a b n := hX a b ++ hD^^n.

Lemma hX_w a b n c:
  segRLs tm (hXs a b (1+n)) (hXs (negb c) a n) (w c) (w b).
Proof.
  destruct a,b,c;
  unfold hXs,negb,hX,w.
  all:
  rewrite lpow_add,app_assoc;
  eapply segRLs_trans;
  [|apply segRLs_wall''; esc];
  esc.
Qed.

Lemma hX_rh a b n:
  sideRLs tm (hXs a b n) 0inf ((if b then (w false)^^2 else (w true))*>(w false)^^n*>0inf).
Proof.
  destruct a,b;
  unfold hXs,hX,w.
  all:
  eapply sideRLs_trans; [esc|];
  sideRLs_ind n.
Qed.

Close Scope sym.

Lemma LIncs k:
  segRLs tm h' (h'++h^^(2^k-1)) (ld^^k) (ld^^k).
Proof.
  induction k.
  1: esc.
  cbn[Nat.pow].
  replace (S k) with (k+1) by lia.
  rewrite lpow_add.
  eapply segRLs_concat.
  1: apply IHk.
  replace (2*2^k-1) with (1+(2^k-1)*2) by lia.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  1: esx.
  am 1 2 (2^k-1) 0 0.
Qed.

Lemma m0_Ov n a:
  segRLs tm (h'++h^^(1+n)) (hXs (negb a) false (1+n*2)) (m0++(w a)) (ld++m0).
Proof.
  unfold hXs.
  do 2 rewrite lpow_add,app_assoc.
  destruct a.
  all:
  eapply segRLs_trans;
  [|rewrite lpow_mul; eapply segRLs_wall''; esc]; esc.
Qed.

Open Scope sym.

Inductive RC: nat->side->Prop :=
| RC_O:
  RC 0 0inf
| RC_S n c r:
  RC n r ->
  RC (S n) (w c*>r)
.

Lemma RC_lpow c n:
  RC n (w c^^n*>0inf).
Proof.
  induction n.
  1: ec.
  st; ec; trivial.
Qed.

Local Opaque w.

Lemma RIncs a b m n r:
  n<=m ->
  RC n r ->
  exists n' r',
  sideRLs tm (hXs a b m) r r' /\
  RC n' r' /\
  m+1<=n'<=m+2.
Proof.
  gen a b m r.
  induction n; intros.
  - inverts H0.
    destruct b; (do 3 ec; [apply hX_rh|ec]).
    1: st; ec; ec; apply RC_lpow.
    2: ec; apply RC_lpow.
    all: lia.
  - inverts H0.
    destruct m.
    1: lia.
    eapply IHn with (m:=m) in H2.
    2: lia.
    destruct H2 as [n' [r' [I1 [I2 I3]]]].
    do 3 ec.
    1: eapply segRLs_sideRLs_concat.
    1: apply hX_w.
    1: apply I1.
    split.
    ec; apply I2.
    lia.
Qed.

Lemma Incs k n r:
  RC n r ->
  2<=1+n<=2^k*2-2/\1<=k ->
  exists n' r',
  sideRLs tm h' (ld^^k*>m0*>r) (ld^^(k+1)*>m0*>r') /\
  RC n' r' /\
  2^k*2-2<=n'<=2^k*2-1.
Proof.
  intros.
  destruct n; [lia|].
  inverts H.
  assert (2<=2^k) by (destruct k; cbn[Nat.pow]; lia).
  eapply RIncs in H2.
  2: shelve.
  destruct H2 as [n' [r' [I1 [I2 I3]]]].
  do 3 ec.
  - rewrite lpow_add,Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: apply LIncs.
    do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    1: applys_eq (m0_Ov (2^k-2) c); flia. 
    apply I1.
  - split.
    1: apply I2.
    lia.
  Unshelve.
  1: lia.
Qed.

Definition S' '(k,r) := lh {{{ (hR',R) }}} ld^^k *> m0 *> r.

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hR',R) }}} r.
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,w true*>w false*>0inf)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(k,r) => exists n, RC n r /\ 2^k-1<=1+n<=2^k /\ 2<=k).
  2:{
    ec; ec.
    1: do 3 ec.
    lia.
  }
  intros [k r] [n [I1 [I2 I3]]].
  assert (I4:2^2<=2^k) by (apply Nat.pow_le_mono_r; lia).
  eapply Incs with (k:=k) in I1.
  2: lia.
  destruct I1 as [n' [r' [I5 [I6 I7]]]].
  eapply sideRLs_1 in I5.
  eexists (_,_); ec.
  - unfold S'.
    follow10 I5.
    apply LRst.
  - ec; ec.
    1: apply I6.
    rewrite Nat.pow_add_r; lia.
Qed.

End TM37.

