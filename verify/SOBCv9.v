From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal ES_v3 DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac sideRLs_ind k :=
  induction k;
  [ try esx |
    eapply sideRLs_trans_S;
    [ eassumption | ];
    try esx ].

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1LC0RE_1LA1LD_1RE0RF_1RA1RA_---0LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[1]).
Notation hR' := (A,<[1;1;1]).
Notation hR'' := (A,<[]).
Notation hL := (D,[1]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation h'' := [(hR'',hL)].
Notation w := [1;0;0].
Notation w' := [0;1;0].
Notation d := [1;0;1;0;1;0].
Notation lh0 := (0inf<*<[1;1]).
Notation lh1 := (0inf<*<[1;1;1;1;1]).
Notation lh2 := (0inf<*<[1;0;1; 1;0;1;1;1;1]).
Notation lh2' := (0inf<*<[1;0;1; 1;1;1;1;1;1]).

Lemma w'_Incs k:
  2<=k ->
  segRLs tm (h^^k) (h^^(k-1)) w' w.
Proof.
  intro H.
  applys_eq (segRLs_addmul_v2 1 1 (k-2) 2 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (d^^n) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: applys_eq (IHn (k*2)); flia.
    applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
    1,2: flia.
    1,2: esc.
Qed.

Lemma w's_Incs k n:
  k<n ->
  sideRLs tm (h^^n) (w'^^k *> 0inf) (w^^n *> 0inf).
Proof.
  gen n.
  induction k; intros.
  - cbn. clear.
    sideRLs_ind n.
  - destruct n; [lia|].
    rewrite (lpow_S _ w').
    rewrite (lpow_S _ w).
    do 2 rewrite Str_app_assoc.
    cat.
    2: apply IHk; lia.
    applys_eq (w'_Incs); flia.
Qed.

Fixpoint RC ls m :=
match ls with
| [] => w^^m *> 0inf
| a::ls => d^^(a+1) *> w *> RC ls m
end.

Fixpoint RC' ls m :=
match ls with
| [] => w'^^m *> 0inf
| a::ls => d^^(a+1) *> w' *> RC' ls m
end.

Lemma RC_shift ls m:
  RC ls (S m) = [1;0] *> RC' ls m.
Proof.
  induction ls; cbn.
  - simpl_rotate; trivial.
  - rewrite IHls.
    simpl_rotate; trivial.
Qed.

Lemma LRst0 ls m:
  lh0 {{{ (hL,L) }}} RC ls (S m) -->*
  lh1 {{{ (hR,R) }}} RC' ls m.
Proof.
  rewrite RC_shift.
  er.
Qed.

Lemma LRst1 ls m:
  lh1 {{{ (hL,L) }}} RC ls (S m) -->*
  lh2 {{{ (hR,R) }}} RC' ls m.
Proof.
  rewrite RC_shift.
  er.
Qed.

Lemma lh2_Incs:
  sideRLs (flip tm) [(hL,hR)] lh2 lh2'.
Proof.
  esc.
Qed.

Lemma LRst2 a ls m:
  lh2' {{{ (hL,L) }}} RC (a::ls) m -->*
  lh0 {{{ (hR',R) }}} RC (1+a::ls) m.
Proof.
  er.
Qed.

Fixpoint cnt k ls :=
match ls with
| [] => k
| a::ls => cnt (k*2^a*2-1) ls
end.

Lemma RIncs k ls m:
  let k' := (cnt k ls) in
  m<k' ->
  k<>O ->
  sideRLs tm (h^^k) (RC' ls m) (RC ls k').
Proof.
  gen k.
  induction ls; intros; cbn[RC RC' cnt] in *.
  - apply w's_Incs,H.
  - cat1 d_Incs.
    rewrite Nat.pow_add_r.
    cat.
    1: apply w'_Incs; lia.
    subst k'.
    applys_eq IHls.
    1,3: flia.
    applys_eq H; flia.
Qed.

Notation d'' := [0;1;0;1;0;1].

Lemma d''_Incs k n:
  segRLs tm (h''++h^^k) (h''++h^^((k+1)*2^n-1)) (d''^^n) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: applys_eq (IHn (1+k*2)); flia.
    rewrite lpow_add,app_assoc.
    tr.
    2: apply (d_Incs k 1).
    esc.
Qed.

Notation d'0 := [0;1;0;1;0;0].

Lemma d'0_Incs k:
  segRLs tm (h''++h^^k) (h'++h^^k) d'0 w. 
Proof.
  tr.
  1: esx.
  apply segRLs_wall''; esc.
Qed.

Lemma d101_Incs k:
  segRLs tm (h'++h^^k) (h''++h^^(k*2)) [1;0;1] d.
Proof.
  tr.
  1: esx.
  apply (d_Incs k 1).
Qed.

Lemma w2_Incs k n:
  segRLs tm (h''++h^^k) (h''++h^^(k*2^n)) (w^^(n*2)) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply @segRLs_concat with (w1:=w^^2) (w2:=d) (w3:=w^^(n*2)).
    2: applys_eq (IHn (k*2)); flia.
    tr.
    1: esx.
    apply (d_Incs k 1).
Qed.

Lemma w_Incs' k:
  segRLs tm (h'++h^^k) (h''++h^^(k*2)) w d.
Proof.
  tr.
  1: esx.
  apply (d_Incs k 1).
Qed.

Lemma RD_Incs' k a r r':
  sideRLs tm (h'++h^^((k*2+1)*2^a-1)) r r' ->
  sideRLs tm (h'++h^^k) (d^^(a+1)*>w*>r) (d^^(a+1)*>w*>r').
Proof.
  intros H.
  assert (I1:sideRLs tm (h'++h^^k) ([1;0;1]*>d''^^a*>d'0*>r) (d*>d^^a*>w*>r')). 
  2: applys_eq I1; st; simpl_rotate; trivial.
  cat1 d101_Incs.
  cat1 d''_Incs.
  cat1 d'0_Incs.
  apply H.
Qed.

Lemma rh_Incs' k:
  sideRLs tm (h''++h^^k) 0inf (w^^(1+k)*>0inf).
Proof.
  tr.
  1: esx.
  sideRLs_ind k.
Qed.

Lemma RD_Incs'_1 k b c
  (Hc: c = k*2^b*2):
  sideRLs tm (h'++h^^k) (w^^(1+b*2)*>0inf) (d^^(b+1)*>w*>w^^c*>0inf).
Proof.
  assert (I1:sideRLs tm (h'++h^^k) (w*>w^^(b*2)*>0inf) (d*>d^^b*>w^^(1+c)*>0inf)). 
  2: applys_eq I1; st; simpl_rotate; trivial.
  cat1 w_Incs'.
  cat1 w2_Incs.
  applys_eq rh_Incs'; flia.
Qed.

Fixpoint cnt' k ls :=
match ls with
| [] => k
| a::ls => cnt' ((k*2+1)*2^a-1) ls
end.

Lemma RIncs'_1 k b ls:
  sideRLs tm (h'++h^^k) (RC ls (1+b*2)) (RC (ls++[b]) ((cnt' k ls)*2^b*2)).
Proof.
  gen k.
  induction ls; intros; cbn[cnt' RC app].
  - apply RD_Incs'_1; lia.
  - apply RD_Incs',IHls.
Qed.

Inductive Tp :=
| tp0 | tp1 | tp2.

Definition S' '(tp,a,ls,n) :=
  match tp with
  | tp0 => lh0
  | tp1 => lh1
  | tp2 => lh2'
  end {{{ (hL,L) }}} RC (a::ls) n.

Lemma BigStep0 a ls n:
  1 <= n <= cnt 1 (a::ls) ->
  S' (tp0,a,ls,n) -->+
  S' (tp1,a,ls,cnt 1 (a::ls)).
Proof.
  intros Hn.
  unfold S'.
  replace n with (S(n-1)) by lia.
  follow LRst0.
  unshelve epose proof (RIncs 1 (a::ls) (n-1) _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  apply I1.
Qed.

Lemma BigStep1 a ls n:
  1 <= n <= cnt 2 (a::ls) ->
  S' (tp1,a,ls,n) -->+
  S' (tp2,a,ls,cnt 2 (a::ls)).
Proof.
  intros Hn.
  unfold S'.
  replace n with (S(n-1)) by lia.
  follow LRst1.
  unshelve epose proof (RIncs 2 (a::ls) (n-1) _ _) as I1.
  1,2: lia.
  apply (sideRLs_concat lh2_Incs I1).
Qed.

Lemma BigStep2 a ls n:
  S' (tp2,a,ls,1+n*2) -->+
  S' (tp0,1+a,ls++[n],(cnt' 0 (1+a::ls))*2^n*2).
Proof.
  unfold S'.
  follow LRst2.
  epose proof (RIncs'_1 0 n (1+a::ls)) as I1.
  eapply sideRLs_1 in I1.
  apply I1.
Qed.

Lemma init:
  c0 -->*
  S' (tp1,1,[0;2],39)%nat.
Proof.
  esx.
Qed.

Lemma cnt_le k' k ls:
  k'<=k ->
  cnt k' ls <= cnt k ls.
Proof.
  gen k' k.
  induction ls; cbn; intros.
  - lia.
  - apply IHls.
    nia.
Qed.

Lemma cnt_odd k ls:
  k mod 2 <> O ->
  (cnt k ls) mod 2 <> O.
Proof.
  gen k.
  induction ls; cbn[cnt]; intros.
  - lia.
  - apply IHls.
    nia.
Qed.

Lemma cnt'_le k' k ls a0:
  k'<k ->
  cnt' k' ls * 2 ^ a0 * 2 <= cnt k (ls ++ [a0]).
Proof.
  gen k' k.
  induction ls; cbn; intros.
  - nia.
  - apply IHls.
    nia.
Qed.

Lemma cnt'_ne0 k ls:
  k<>O ->
  cnt' k ls <> O.
Proof.
  gen k.
  induction ls; cbn; intros.
  - lia.
  - apply IHls.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(tp,a,ls,n) =>
  match tp with
  | tp0 => 1<=n<=cnt 1 (a::ls)
  | tp1 => 1<=n<=cnt 2 (a::ls)
  | tp2 => n mod 2 <> O
  end).
  2: cbn[cnt]; lia.
  intros [[[[] a] ls] n] HP.
  - eexists; split.
    1: apply BigStep0,HP.
    cbn match.
    split; [lia|apply cnt_le; lia].
  - eexists; split.
    1: apply BigStep1,HP.
    cbn match.
    cbn[cnt].
    apply cnt_odd; lia.
  - destruct (mod2 n); [lia|subst].
    eexists; split.
    1: apply BigStep2.
    cbn match.
    split.
    + cbn[cnt'].
      unshelve epose proof (cnt'_ne0 ((0*2+1)*2^(1+a)-1) ls _).
      2: lia.
      cbn; lia.
    + apply cnt'_le; lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1RC1RE_1LD0RA_1LB1LE_1RA0RF_---0LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[1]).
Notation hR' := (B,<[1;1;1]).
Notation hR'' := (B,<[]).
Notation hL := (E,[1]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation h'' := [(hR'',hL)].
Notation w := [1;0;0].
Notation w' := [0;1;0].
Notation d := [1;0;1;0;1;0].
Notation lh0 := (0inf<*<[1;1]).
Notation lh1 := (0inf<*<[1;1;1;1;1]).
Notation lh2 := (0inf<*<[1;0;1; 1;0;1;1;1;1]).
Notation lh2' := (0inf<*<[1;0;1; 1;1;1;1;1;1]).

Lemma w'_Incs k:
  2<=k ->
  segRLs tm (h^^k) (h^^(k-1)) w' w.
Proof.
  intro H.
  applys_eq (segRLs_addmul_v2 1 1 (k-2) 2 1); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma d_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (d^^n) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: applys_eq (IHn (k*2)); flia.
    applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
    1,2: flia.
    1,2: esc.
Qed.

Lemma w's_Incs k n:
  k<n ->
  sideRLs tm (h^^n) (w'^^k *> 0inf) (w^^n *> 0inf).
Proof.
  gen n.
  induction k; intros.
  - cbn. clear.
    sideRLs_ind n.
  - destruct n; [lia|].
    rewrite (lpow_S _ w').
    rewrite (lpow_S _ w).
    do 2 rewrite Str_app_assoc.
    cat.
    2: apply IHk; lia.
    applys_eq (w'_Incs); flia.
Qed.

Fixpoint RC ls m :=
match ls with
| [] => w^^m *> 0inf
| a::ls => d^^(a+1) *> w *> RC ls m
end.

Fixpoint RC' ls m :=
match ls with
| [] => w'^^m *> 0inf
| a::ls => d^^(a+1) *> w' *> RC' ls m
end.

Lemma RC_shift ls m:
  RC ls (S m) = [1;0] *> RC' ls m.
Proof.
  induction ls; cbn.
  - simpl_rotate; trivial.
  - rewrite IHls.
    simpl_rotate; trivial.
Qed.

Lemma LRst0 ls m:
  lh0 {{{ (hL,L) }}} RC ls (S m) -->*
  lh1 {{{ (hR,R) }}} RC' ls m.
Proof.
  rewrite RC_shift.
  er.
Qed.

Lemma LRst1 ls m:
  lh1 {{{ (hL,L) }}} RC ls (S m) -->*
  lh2 {{{ (hR,R) }}} RC' ls m.
Proof.
  rewrite RC_shift.
  er.
Qed.

Lemma lh2_Incs:
  sideRLs (flip tm) [(hL,hR)] lh2 lh2'.
Proof.
  esc.
Qed.

Lemma LRst2 a ls m:
  lh2' {{{ (hL,L) }}} RC (a::ls) m -->*
  lh0 {{{ (hR',R) }}} RC (1+a::ls) m.
Proof.
  er.
Qed.

Fixpoint cnt k ls :=
match ls with
| [] => k
| a::ls => cnt (k*2^a*2-1) ls
end.

Lemma RIncs k ls m:
  let k' := (cnt k ls) in
  m<k' ->
  k<>O ->
  sideRLs tm (h^^k) (RC' ls m) (RC ls k').
Proof.
  gen k.
  induction ls; intros; cbn[RC RC' cnt] in *.
  - apply w's_Incs,H.
  - cat1 d_Incs.
    rewrite Nat.pow_add_r.
    cat.
    1: apply w'_Incs; lia.
    subst k'.
    applys_eq IHls.
    1,3: flia.
    applys_eq H; flia.
Qed.

Notation d'' := [0;1;0;1;0;1].

Lemma d''_Incs k n:
  segRLs tm (h''++h^^k) (h''++h^^((k+1)*2^n-1)) (d''^^n) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: applys_eq (IHn (1+k*2)); flia.
    rewrite lpow_add,app_assoc.
    tr.
    2: apply (d_Incs k 1).
    esc.
Qed.

Notation d'0 := [0;1;0;1;0;0].

Lemma d'0_Incs k:
  segRLs tm (h''++h^^k) (h'++h^^k) d'0 w. 
Proof.
  tr.
  1: esx.
  apply segRLs_wall''; esc.
Qed.

Lemma d101_Incs k:
  segRLs tm (h'++h^^k) (h''++h^^(k*2)) [1;0;1] d.
Proof.
  tr.
  1: esx.
  apply (d_Incs k 1).
Qed.

Lemma w2_Incs k n:
  segRLs tm (h''++h^^k) (h''++h^^(k*2^n)) (w^^(n*2)) (d^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply @segRLs_concat with (w1:=w^^2) (w2:=d) (w3:=w^^(n*2)).
    2: applys_eq (IHn (k*2)); flia.
    tr.
    1: esx.
    apply (d_Incs k 1).
Qed.

Lemma w_Incs' k:
  segRLs tm (h'++h^^k) (h''++h^^(k*2)) w d.
Proof.
  tr.
  1: esx.
  apply (d_Incs k 1).
Qed.

Lemma RD_Incs' k a r r':
  sideRLs tm (h'++h^^((k*2+1)*2^a-1)) r r' ->
  sideRLs tm (h'++h^^k) (d^^(a+1)*>w*>r) (d^^(a+1)*>w*>r').
Proof.
  intros H.
  assert (I1:sideRLs tm (h'++h^^k) ([1;0;1]*>d''^^a*>d'0*>r) (d*>d^^a*>w*>r')). 
  2: applys_eq I1; st; simpl_rotate; trivial.
  cat1 d101_Incs.
  cat1 d''_Incs.
  cat1 d'0_Incs.
  apply H.
Qed.

Lemma rh_Incs' k:
  sideRLs tm (h''++h^^k) 0inf (w^^(1+k)*>0inf).
Proof.
  tr.
  1: esx.
  sideRLs_ind k.
Qed.

Lemma RD_Incs'_1 k b c
  (Hc: c = k*2^b*2):
  sideRLs tm (h'++h^^k) (w^^(1+b*2)*>0inf) (d^^(b+1)*>w*>w^^c*>0inf).
Proof.
  assert (I1:sideRLs tm (h'++h^^k) (w*>w^^(b*2)*>0inf) (d*>d^^b*>w^^(1+c)*>0inf)). 
  2: applys_eq I1; st; simpl_rotate; trivial.
  cat1 w_Incs'.
  cat1 w2_Incs.
  applys_eq rh_Incs'; flia.
Qed.

Fixpoint cnt' k ls :=
match ls with
| [] => k
| a::ls => cnt' ((k*2+1)*2^a-1) ls
end.

Lemma RIncs'_1 k b ls:
  sideRLs tm (h'++h^^k) (RC ls (1+b*2)) (RC (ls++[b]) ((cnt' k ls)*2^b*2)).
Proof.
  gen k.
  induction ls; intros; cbn[cnt' RC app].
  - apply RD_Incs'_1; lia.
  - apply RD_Incs',IHls.
Qed.

Inductive Tp :=
| tp0 | tp1 | tp2.

Definition S' '(tp,a,ls,n) :=
  match tp with
  | tp0 => lh0
  | tp1 => lh1
  | tp2 => lh2'
  end {{{ (hL,L) }}} RC (a::ls) n.

Lemma BigStep0 a ls n:
  1 <= n <= cnt 1 (a::ls) ->
  S' (tp0,a,ls,n) -->+
  S' (tp1,a,ls,cnt 1 (a::ls)).
Proof.
  intros Hn.
  unfold S'.
  replace n with (S(n-1)) by lia.
  follow LRst0.
  unshelve epose proof (RIncs 1 (a::ls) (n-1) _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  apply I1.
Qed.

Lemma BigStep1 a ls n:
  1 <= n <= cnt 2 (a::ls) ->
  S' (tp1,a,ls,n) -->+
  S' (tp2,a,ls,cnt 2 (a::ls)).
Proof.
  intros Hn.
  unfold S'.
  replace n with (S(n-1)) by lia.
  follow LRst1.
  unshelve epose proof (RIncs 2 (a::ls) (n-1) _ _) as I1.
  1,2: lia.
  apply (sideRLs_concat lh2_Incs I1).
Qed.

Lemma BigStep2 a ls n:
  S' (tp2,a,ls,1+n*2) -->+
  S' (tp0,1+a,ls++[n],(cnt' 0 (1+a::ls))*2^n*2).
Proof.
  unfold S'.
  follow LRst2.
  epose proof (RIncs'_1 0 n (1+a::ls)) as I1.
  eapply sideRLs_1 in I1.
  apply I1.
Qed.

Lemma init:
  c0 -->*
  S' (tp1,1,[1],11)%nat.
Proof.
  esx.
Qed.

Lemma cnt_le k' k ls:
  k'<=k ->
  cnt k' ls <= cnt k ls.
Proof.
  gen k' k.
  induction ls; cbn; intros.
  - lia.
  - apply IHls.
    nia.
Qed.

Lemma cnt_odd k ls:
  k mod 2 <> O ->
  (cnt k ls) mod 2 <> O.
Proof.
  gen k.
  induction ls; cbn[cnt]; intros.
  - lia.
  - apply IHls.
    nia.
Qed.

Lemma cnt'_le k' k ls a0:
  k'<k ->
  cnt' k' ls * 2 ^ a0 * 2 <= cnt k (ls ++ [a0]).
Proof.
  gen k' k.
  induction ls; cbn; intros.
  - nia.
  - apply IHls.
    nia.
Qed.

Lemma cnt'_ne0 k ls:
  k<>O ->
  cnt' k ls <> O.
Proof.
  gen k.
  induction ls; cbn; intros.
  - lia.
  - apply IHls.
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(tp,a,ls,n) =>
  match tp with
  | tp0 => 1<=n<=cnt 1 (a::ls)
  | tp1 => 1<=n<=cnt 2 (a::ls)
  | tp2 => n mod 2 <> O
  end).
  2: cbn[cnt]; lia.
  intros [[[[] a] ls] n] HP.
  - eexists; split.
    1: apply BigStep0,HP.
    cbn match.
    split; [lia|apply cnt_le; lia].
  - eexists; split.
    1: apply BigStep1,HP.
    cbn match.
    cbn[cnt].
    apply cnt_odd; lia.
  - destruct (mod2 n); [lia|subst].
    eexists; split.
    1: apply BigStep2.
    cbn match.
    split.
    + cbn[cnt'].
      unshelve epose proof (cnt'_ne0 ((0*2+1)*2^(1+a)-1) ls _).
      2: lia.
      cbn; lia.
    + apply cnt'_le; lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RA_---0LD_0LE0LB_1RF1RB_1RE1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hL := (D,[0;1]).
Notation hR := (A,<[1;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d0 := <[1;0;1;0;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation w := [0;1].
Notation lh0 := (0inf<*<[1;1;1]).
Notation lh1 := (0inf<*<[1;1;1;1;0;1;1]).

Lemma LIncs l n:
  sideRLs (flip tm) (hLR^^(2^n-1)) (l<*d0^^n) (l<*d1^^n).
Proof.
  eapply segRLs_sideRLs_concat.
  1: eapply BC.Incs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
  esx.
Qed.

Lemma RIncs k n:
  sideRLs tm (hRL^^k) (w^^n*>0inf) (w^^(k+n)*>0inf).
Proof.
  sideRLs_ind k.
Qed.

Definition S0 l a b :=
  l <* d0^^a {{{ (hL,L) }}} w^^b *> 0inf.

Definition S1 l a b :=
  l <* d1^^a {{{ (hL,L) }}} w^^b *> 0inf.

Lemma S0_Incs l a b:
  S0 l a b -->*
  S1 l a ((2^a-1)+b).
Proof.
  unfold S0,S1.
  eapply sideRLs_concat_1L.
  1: apply RIncs.
  apply LIncs.
Qed.

Lemma S1_d1 l a b:
  S1 (l<*d1) a b -->*
  S1 l (a+1) b.
Proof.
  unfold S1.
  es.
Qed.

Notation lh2 := (0inf<*<[1]^^8<*<[0;1;1]).

Definition S2 l a b c :=
  l <* d0^^a <* <[1;0;1] <* <[1]^^(b*14) <* <[0;1;1] {{E}}> [1;0]^^c *> 0inf.

Ltac es_v3_pre ::= 
  unfold c0,q0,tape0,s0,S0,S1,S2,to_DH_config.

Lemma init:
  c0 -->*
  S0 (lh0<*d1) 20 2.
Proof.
  es'.
Qed.

Lemma S1_Ov0 a b:
  S1 lh0 a b -->*
  S2 lh0 a 0 b.
Proof.
  es' a b.
Qed.

Lemma S1_Ov1 a b:
  S1 lh1 (1+a) b -->*
  S2 lh2 a 0 b.
Proof.
  es' a b.
Qed.

Lemma S1_Ov1' a b:
  1<=a ->
  S1 lh1 a b -->*
  S2 lh2 (a-1) 0 b.
Proof.
  intros.
  applys_eq (S1_Ov1 (a-1) b); flia.
Qed.

Lemma S2_Inc l a b c:
  S2 l (1+a) b (4+c) -->*
  S2 l a (1+b) c.
Proof.
  es' a b c & l.
Qed.

Lemma S2_Incs n l a b c:
  S2 l (n+a) b (n*4+c) -->*
  S2 l a (n+b) c.
Proof.
  gen a b c.
  ind n S2_Inc.
Qed.

Lemma S2_Incs' l a b c:
  a*4<=c ->
  S2 l a b c -->*
  S2 l 0 (a+b) (c-a*4).
Proof.
  intros.
  applys_eq (S2_Incs a l 0 b (c-a*4)); flia.
Qed.

Lemma S2_Ov0_0 b c:
  S2 lh0 0 (b*3) (7+c) -->*
  S2 lh0 (1+b*7) 1 c.
Proof.
  unfold S2.
  es' b c.
Qed.

Lemma S2_Ov0_0' b c:
  b mod 3 = O ->
  7<=c ->
  S2 lh0 0 b c -->*
  S2 lh0 (1+b/3*7) 1 (c-7).
Proof.
  intros.
  applys_eq (S2_Ov0_0 (b/3) (c-7)); flia.
Qed.

Lemma S2_Ov0_1 b c:
  S2 lh0 0 (1+b*3) (4+c) -->*
  S0 lh1 (4+b*7) (2+c).
Proof.
  es' b c.
Qed.

Lemma S2_Ov0_1' b c:
  b mod 3 = 1%nat ->
  4<=c ->
  S2 lh0 0 b c -->*
  S0 lh1 (4+b/3*7) (c-2).
Proof.
  intros.
  applys_eq (S2_Ov0_1 (b/3) (c-4)); flia.
Qed.

Lemma S2_Ov0_2 b c:
  halts tm (S2 lh0 0 (2+b*3) (7+c)).
Proof.
  es' b c.
Qed.

Lemma S2_Ov0_2' b c:
  b mod 3 = 2 ->
  7<=c ->
  halts tm (S2 lh0 0 b c).
Proof.
  intros.
  applys_eq (S2_Ov0_2 (b/3) (c-7)); flia.
Qed.

Lemma S2_Ov2_1 b c:
  S2 lh2 0 (1+b*3) (6+c) -->*
  S0 lh1 (6+b*7) (2+c).
Proof.
  es' b c.
Qed.

Lemma S2_Ov2_1' b c:
  b mod 3 = 1%nat ->
  6<=c ->
  S2 lh2 0 b c -->*
  S0 lh1 (6+b/3*7) (c-4).
Proof.
  intros.
  applys_eq (S2_Ov2_1 (b/3) (c-6)); flia.
Qed.

Lemma S2_Ov2_0 b c:
  S2 lh2 0 (b*3) (9+c) -->*
  S2 lh0 (3+b*7) 1 c.
Proof.
  es' b c.
Qed.

Lemma S2_Ov2_0' b c:
  b mod 3 = O ->
  9 <=c ->
  S2 lh2 0 b c -->*
  S2 lh0 (3+b/3*7) 1 (c-9).
Proof.
  intros.
  applys_eq (S2_Ov2_0 (b/3) (c-9)); flia.
Qed.

Inductive LH := LH0 | LH1 | LH2.
Inductive Config :=
| cfg0(l:LH)(a b:N)
| cfg1(l:LH)(a b:N)
| cfg2(l:LH)(a b c:N).

Definition to_lh x :=
match x with
| LH0 => lh0
| LH1 => lh1
| LH2 => lh2
end.

Definition to_Config x :=
match x with
| cfg0 l a b => S0 (to_lh l) (N.to_nat a) (N.to_nat b)
| cfg1 l a b => S1 (to_lh l) (N.to_nat a) (N.to_nat b)
| cfg2 l a b c => S2 (to_lh l) (N.to_nat a) (N.to_nat b) (N.to_nat c)
end.

Definition mstep x :=
match x with
| cfg0 l a b => cfg1 l a (2^a-1+b)
| cfg1 LH0 a b => cfg2 LH0 a 0 b
| cfg1 LH1 a b =>
  if N.leb 1 a then
    cfg2 LH2 (a-1) 0 b
  else x
| cfg2 l a b c =>
  if N.eqb a 0 then
    if N.eqb (b mod 3) 0 then
      match l with
      | LH0 => if N.leb 7 c then cfg2 LH0 (1+b/3*7) 1 (c-7) else x
      | LH2 => if N.leb 9 c then cfg2 LH0 (3+b/3*7) 1 (c-9) else x
      | _ => x
      end
    else if N.eqb (b mod 3) 1 then
      match l with
      | LH0 => if N.leb 4 c then cfg0 LH1 (4+b/3*7) (c-2) else x
      | LH2 => if N.leb 6 c then cfg0 LH1 (6+b/3*7) (c-4) else x
      | _ => x
      end
    else x
  else if N.leb (a*4) c then
    cfg2 l 0 (a+b) (c-a*4)
  else x
| _ => x
end.

Fixpoint msteps x T :=
match T with
| O => x
| S T => mstep (msteps x T)
end.

Ltac rw2 :=
  rewrite Nnat.N2Nat.inj_add ||
  rewrite Nnat.N2Nat.inj_sub ||
  rewrite Nnat.N2Nat.inj_mul ||
  rewrite Nnat.N2Nat.inj_div ||
  rewrite Nnat.N2Nat.inj_mod ||
  rewrite Nnat.N2Nat.inj_pow.

Ltac rw1 :=
  repeat (
  rw2 ||
  match goal with
  | |- _ -->* match if N.leb ?a ?b then _ else _ with _ => _ end => destruct (N.leb_spec a b)
  | |- _ -->* match if N.eqb ?a ?b then _ else _ with _ => _ end => destruct (N.eqb_spec a b)
  end ||
  apply evstep_refl
  ).

Lemma mstep_spec x:
  to_Config x -->* to_Config (mstep x).
Proof.
  unfold mstep,to_Config,to_lh.
  destruct x as [l a b|[] a b|[] a b c]; rw1.
  - apply S0_Incs.
  - apply S1_Ov0.
  - apply S1_Ov1'; lia.
  - subst a.
    apply S2_Ov0_0'; lia.
  - subst a.
    apply S2_Ov0_1'; lia.
  - apply S2_Incs'; lia.
  - apply S2_Incs'; lia.
  - subst a.
    apply S2_Ov2_0'; lia.
  - subst a.
    apply S2_Ov2_1'; lia.
  - apply S2_Incs'; lia.
Qed.

Lemma msteps_spec x x' T:
  msteps x T = x' ->
  to_Config x -->* to_Config x'.
Proof.
  gen x x'.
  induction T; cbn[msteps]; intros.
  1: subst; finish.
  follow IHT.
  follow mstep_spec.
  rewrite H.
  finish.
Qed.


Lemma halt:
  halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
    follow init.
    follow S0_Incs.
    follow S1_d1.
    mid (to_Config (cfg1 LH0 (20+1) (2^20-1+2))).
    1: unfold to_Config,to_lh; repeat rw2; finish.
    apply msteps_spec with (T:=30).
    vm_compute; reflexivity.
  }
  unfold to_Config,to_lh.
  eapply S2_Ov0_2'; lia.
Qed.

End TM3.

