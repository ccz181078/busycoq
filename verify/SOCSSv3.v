From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal ES_v3.
From BusyCoq Require Import DivModCases.
Require Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac cat :=
  eapply segRLs_sideRLs_concat ||
  eapply segRLs_concat.

Ltac tr :=
  eapply sideRLs_trans ||
  eapply segRLs_trans.

Ltac cat1 H :=
  cat; [apply H|].

Ltac wal := apply segRLs_wall''; esc.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LF_1RA0LA_1LC1RE_1RD0RA_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf <* <[1;1;1;1;1;0;1;1]).
Notation ld := [1;1;1;1;1;1].
Notation w1 := [1;1;1;1;1;1;1;1;0;1;1;1].
Notation w2 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1].
Notation w3 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;0].
Notation rd1 := [1;1;1;1;1;0].
Notation rh := ([1;1;1;1;1;1;1;1;1]*>0inf).

Notation hRx := (E,[]).
Notation hRy := (E,<[1;1;1]).
Notation hR := (D,<[0;1]).
Notation hL := (A,[0;1]).
Notation hL' := (B,[1;0]).

Notation hx := [(hRx,hL)].
Notation hy := [(hRy,hL)].
Notation h := [(hR,hL)].
Notation h' := [(hR,hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  ut; es' & r.
Qed.

Inductive LD := Ld | W1 | W2.

Fixpoint LC ls :=
match ls with
| x::t => LC t ++
  match x with
  | Ld => ld
  | W1 => w1
  | W2 => w2
  end
| [] => []
end.

Fixpoint sz ls :=
match ls with
| x::t => match x with Ld => 1 | _ => O end + sz t
| [] => O
end.

Lemma ld_Incs' k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma w1_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w1 w1.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma w2_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w2 w2.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma LIncs ls:
  segRLs tm hx (hx++h^^(2^(sz ls)-1)) (LC ls) (LC ls).
Proof.
  induction ls as [|[] ls]; cbn[sz LC].
  1: esc.
  all: rewrite Nat.pow_add_r; cat1 IHls.
  - applys_eq ld_Incs; flia.
  - applys_eq w1_Incs; flia.
  - applys_eq w2_Incs; flia.
Qed.

Lemma w3_Incs k:
  segRLs tm (hx++h^^k) (hy++h^^(1+k)) w3 w2.
Proof.
  rewrite lpow_add,app_assoc.
  tr; [|wal].
  esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (hy++h^^k) (hy++h^^(k*2)) rd1 ld.
Proof.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma LIncs' ls n:
  segRLs tm hx (hy++h^^(2^(n+sz ls))) (LC ls ++ w3 ++ rd1^^n) (LC ([Ld]^^n++W2::ls)).
Proof.
  induction n.
  - cat1 (LIncs ls).
    rewrite Nat.add_0_l.
    applys_eq w3_Incs; flia.
  - eassert (I1:_).
    { eapply segRLs_concat.
      1: apply IHn.
      apply rd1_Incs. }
    applys_eq I1.
    1: cbn; flia.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    repeat rewrite <-app_assoc; trivial.
Qed.

Lemma rd1_Incs' k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RIncs k:
  sideRLs tm (h'^^(2^k*2)) (rd1^^k*>rh) (rd1^^(S k)*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow lpow].
    repeat rewrite Str_app_assoc.
    cat.
    2: apply IHk.
    applys_eq rd1_Incs'; flia.
Qed.

Lemma RIncs' k:
  sideRLs tm (h'^^(2^k*2-2)) rh (rd1^^k*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow].
    replace (2*2^k*2-2) with (2^k*2-2+2^k*2) by lia.
    rewrite lpow_add.
    tr.
    1: apply IHk.
    apply RIncs.
Qed.

Lemma w3_Incs' k:
  segRLs tm (h^^k) (h'^^(k*2)) w3 w3.
Proof.
  induction k.
  1: esc.
  cbn[Nat.mul Nat.add lpow].
  rewrite app_assoc.
  tr.
  2: apply IHk.
  esc.
Qed.

Lemma RIncs'' k:
  sideRLs tm (hy++h^^(2^k)) (rd1^^2*>rh) (w3*>rd1^^k*>rh).
Proof.
  replace (2^k) with (1+(2^k-1)) by lia.
  rewrite lpow_add,app_assoc.
  eapply @sideRLs_trans with (r2:=w3*>rh).
  1: esc.
  cat1 w3_Incs'.
  applys_eq (RIncs' k); flia.
Qed.

Definition S' '(ls,n) :=
  lh {{{ (hRx,R) }}} ((LC ls ++ w3 ++ rd1^^n)*>rh).

Lemma LC_app a b:
  LC (a++b) = LC b ++ LC a.
Proof.
  induction a; cbn.
  - rewrite app_nil_r; trivial.
  - rewrite IHa,app_assoc; trivial.
Qed.

Lemma BigStep ls n:
  2<=n ->
  S' (ls,n) -->+
  S' (([Ld]^^(n-2)++W2::ls)++[Ld],n-2+sz ls).
Proof.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (LIncs' ls (n-2)).
    apply RIncs''.
  }
  eapply sideRLs_1 in I1.
  unfold S'.
  intros Hn.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc in *.
  rewrite lpow_add' in I1.
  rewrite Nat.sub_add in I1 by lia.
  follow10 I1.
  follow LRst.
  rewrite (LC_app _ [Ld]),Str_app_assoc.
  rewrite lpow_add'.
  finish.
Qed.

Lemma sz_Lds n ls:
  sz ([Ld]^^n++W2::ls) = n + sz ls.
Proof.
  induction n; cbn; lia.
Qed.

Lemma sz_Ld ls:
  sz (ls++[Ld]) = sz ls + 1.
Proof.
  induction ls; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([Ld;W1;Ld;Ld;Ld;W1;Ld;Ld;Ld],6)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => 2 <= sz ls /\ 2<=n).
  2: cbn; lia.
  intros [ls n] HP.
  eexists; split.
  1: apply BigStep,HP.
  cbn match.
  rewrite sz_Ld,sz_Lds.
  lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LC_1RA0LF_---1LD_1RE0RF_1LB1RD_1LA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf <* <[1;1;1;1;1;1]).
Notation ld := [1;1;1;1;1;1].
Notation w1 := [1;1;1;1;1;1;1;1;0;1;1;1].
Notation w2 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1].
Notation w3 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;0].
Notation rd1 := [1;1;1;1;1;0].
Notation rh := ([1;1;1;1;1;1;1;1;1]*>0inf).

Notation hRx := (D,[]).
Notation hRy := (D,<[1;1;1]).
Notation hR := (E,<[0;1]).
Notation hL := (F,[0;1]).
Notation hL' := (A,[1;0]).

Notation hx := [(hRx,hL)].
Notation hy := [(hRy,hL)].
Notation h := [(hR,hL)].
Notation h' := [(hR,hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  ut; es' & r.
Qed.

Inductive LD := Ld | W1 | W2.

Fixpoint LC ls :=
match ls with
| x::t => LC t ++
  match x with
  | Ld => ld
  | W1 => w1
  | W2 => w2
  end
| [] => []
end.

Fixpoint sz ls :=
match ls with
| x::t => match x with Ld => 1 | _ => O end + sz t
| [] => O
end.

Lemma ld_Incs' k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma w1_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w1 w1.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma w2_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w2 w2.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma LIncs ls:
  segRLs tm hx (hx++h^^(2^(sz ls)-1)) (LC ls) (LC ls).
Proof.
  induction ls as [|[] ls]; cbn[sz LC].
  1: esc.
  all: rewrite Nat.pow_add_r; cat1 IHls.
  - applys_eq ld_Incs; flia.
  - applys_eq w1_Incs; flia.
  - applys_eq w2_Incs; flia.
Qed.

Lemma w3_Incs k:
  segRLs tm (hx++h^^k) (hy++h^^(1+k)) w3 w2.
Proof.
  rewrite lpow_add,app_assoc.
  tr; [|wal].
  esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (hy++h^^k) (hy++h^^(k*2)) rd1 ld.
Proof.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma LIncs' ls n:
  segRLs tm hx (hy++h^^(2^(n+sz ls))) (LC ls ++ w3 ++ rd1^^n) (LC ([Ld]^^n++W2::ls)).
Proof.
  induction n.
  - cat1 (LIncs ls).
    rewrite Nat.add_0_l.
    applys_eq w3_Incs; flia.
  - eassert (I1:_).
    { eapply segRLs_concat.
      1: apply IHn.
      apply rd1_Incs. }
    applys_eq I1.
    1: cbn; flia.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    repeat rewrite <-app_assoc; trivial.
Qed.

Lemma rd1_Incs' k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RIncs k:
  sideRLs tm (h'^^(2^k*2)) (rd1^^k*>rh) (rd1^^(S k)*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow lpow].
    repeat rewrite Str_app_assoc.
    cat.
    2: apply IHk.
    applys_eq rd1_Incs'; flia.
Qed.

Lemma RIncs' k:
  sideRLs tm (h'^^(2^k*2-2)) rh (rd1^^k*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow].
    replace (2*2^k*2-2) with (2^k*2-2+2^k*2) by lia.
    rewrite lpow_add.
    tr.
    1: apply IHk.
    apply RIncs.
Qed.

Lemma w3_Incs' k:
  segRLs tm (h^^k) (h'^^(k*2)) w3 w3.
Proof.
  induction k.
  1: esc.
  cbn[Nat.mul Nat.add lpow].
  rewrite app_assoc.
  tr.
  2: apply IHk.
  esc.
Qed.

Lemma RIncs'' k:
  sideRLs tm (hy++h^^(2^k)) (rd1^^2*>rh) (w3*>rd1^^k*>rh).
Proof.
  replace (2^k) with (1+(2^k-1)) by lia.
  rewrite lpow_add,app_assoc.
  eapply @sideRLs_trans with (r2:=w3*>rh).
  1: esc.
  cat1 w3_Incs'.
  applys_eq (RIncs' k); flia.
Qed.

Definition S' '(ls,n) :=
  lh {{{ (hRx,R) }}} ((LC ls ++ w3 ++ rd1^^n)*>rh).

Lemma LC_app a b:
  LC (a++b) = LC b ++ LC a.
Proof.
  induction a; cbn.
  - rewrite app_nil_r; trivial.
  - rewrite IHa,app_assoc; trivial.
Qed.

Lemma BigStep ls n:
  2<=n ->
  S' (ls,n) -->+
  S' (([Ld]^^(n-2)++W2::ls)++[Ld],n-2+sz ls).
Proof.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (LIncs' ls (n-2)).
    apply RIncs''.
  }
  eapply sideRLs_1 in I1.
  unfold S'.
  intros Hn.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc in *.
  rewrite lpow_add' in I1.
  rewrite Nat.sub_add in I1 by lia.
  follow10 I1.
  follow LRst.
  rewrite (LC_app _ [Ld]),Str_app_assoc.
  rewrite lpow_add'.
  finish.
Qed.

Lemma sz_Lds n ls:
  sz ([Ld]^^n++W2::ls) = n + sz ls.
Proof.
  induction n; cbn; lia.
Qed.

Lemma sz_Ld ls:
  sz (ls++[Ld]) = sz ls + 1.
Proof.
  induction ls; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([Ld;W1;Ld;Ld;Ld;W1;Ld;Ld;Ld],6)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => 2 <= sz ls /\ 2<=n).
  2: cbn; lia.
  intros [ls n] HP.
  eexists; split.
  1: apply BigStep,HP.
  cbn match.
  rewrite sz_Ld,sz_Lds.
  lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0LC_1LA1RD_1LB1RE_1RD0RC_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf <* <[1;1;1;1;1;0;1;1]).
Notation ld := [1;1;1;1;1;1].
Notation w1 := [1;1;1;1;1;1;1;1;0;1;1;1].
Notation w2 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1].
Notation w3 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;0].
Notation rd1 := [1;1;1;1;1;0].
Notation rh := ([1;1;1;1;1;1;1;1;1]*>0inf).

Notation hRx := (E,[]).
Notation hRy := (E,<[1;1;1]).
Notation hR := (D,<[0;1]).
Notation hL := (C,[0;1]).
Notation hL' := (A,[1;0]).

Notation hx := [(hRx,hL)].
Notation hy := [(hRy,hL)].
Notation h := [(hR,hL)].
Notation h' := [(hR,hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  ut; es' & r.
Qed.

Inductive LD := Ld | W1 | W2.

Fixpoint LC ls :=
match ls with
| x::t => LC t ++
  match x with
  | Ld => ld
  | W1 => w1
  | W2 => w2
  end
| [] => []
end.

Fixpoint sz ls :=
match ls with
| x::t => match x with Ld => 1 | _ => O end + sz t
| [] => O
end.

Lemma ld_Incs' k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma w1_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w1 w1.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma w2_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w2 w2.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma LIncs ls:
  segRLs tm hx (hx++h^^(2^(sz ls)-1)) (LC ls) (LC ls).
Proof.
  induction ls as [|[] ls]; cbn[sz LC].
  1: esc.
  all: rewrite Nat.pow_add_r; cat1 IHls.
  - applys_eq ld_Incs; flia.
  - applys_eq w1_Incs; flia.
  - applys_eq w2_Incs; flia.
Qed.

Lemma w3_Incs k:
  segRLs tm (hx++h^^k) (hy++h^^(1+k)) w3 w2.
Proof.
  rewrite lpow_add,app_assoc.
  tr; [|wal].
  esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (hy++h^^k) (hy++h^^(k*2)) rd1 ld.
Proof.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma LIncs' ls n:
  segRLs tm hx (hy++h^^(2^(n+sz ls))) (LC ls ++ w3 ++ rd1^^n) (LC ([Ld]^^n++W2::ls)).
Proof.
  induction n.
  - cat1 (LIncs ls).
    rewrite Nat.add_0_l.
    applys_eq w3_Incs; flia.
  - eassert (I1:_).
    { eapply segRLs_concat.
      1: apply IHn.
      apply rd1_Incs. }
    applys_eq I1.
    1: cbn; flia.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    repeat rewrite <-app_assoc; trivial.
Qed.

Lemma rd1_Incs' k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RIncs k:
  sideRLs tm (h'^^(2^k*2)) (rd1^^k*>rh) (rd1^^(S k)*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow lpow].
    repeat rewrite Str_app_assoc.
    cat.
    2: apply IHk.
    applys_eq rd1_Incs'; flia.
Qed.

Lemma RIncs' k:
  sideRLs tm (h'^^(2^k*2-2)) rh (rd1^^k*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow].
    replace (2*2^k*2-2) with (2^k*2-2+2^k*2) by lia.
    rewrite lpow_add.
    tr.
    1: apply IHk.
    apply RIncs.
Qed.

Lemma w3_Incs' k:
  segRLs tm (h^^k) (h'^^(k*2)) w3 w3.
Proof.
  induction k.
  1: esc.
  cbn[Nat.mul Nat.add lpow].
  rewrite app_assoc.
  tr.
  2: apply IHk.
  esc.
Qed.

Lemma RIncs'' k:
  sideRLs tm (hy++h^^(2^k)) (rd1^^2*>rh) (w3*>rd1^^k*>rh).
Proof.
  replace (2^k) with (1+(2^k-1)) by lia.
  rewrite lpow_add,app_assoc.
  eapply @sideRLs_trans with (r2:=w3*>rh).
  1: esc.
  cat1 w3_Incs'.
  applys_eq (RIncs' k); flia.
Qed.

Definition S' '(ls,n) :=
  lh {{{ (hRx,R) }}} ((LC ls ++ w3 ++ rd1^^n)*>rh).

Lemma LC_app a b:
  LC (a++b) = LC b ++ LC a.
Proof.
  induction a; cbn.
  - rewrite app_nil_r; trivial.
  - rewrite IHa,app_assoc; trivial.
Qed.

Lemma BigStep ls n:
  2<=n ->
  S' (ls,n) -->+
  S' (([Ld]^^(n-2)++W2::ls)++[Ld],n-2+sz ls).
Proof.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (LIncs' ls (n-2)).
    apply RIncs''.
  }
  eapply sideRLs_1 in I1.
  unfold S'.
  intros Hn.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc in *.
  rewrite lpow_add' in I1.
  rewrite Nat.sub_add in I1 by lia.
  follow10 I1.
  follow LRst.
  rewrite (LC_app _ [Ld]),Str_app_assoc.
  rewrite lpow_add'.
  finish.
Qed.

Lemma sz_Lds n ls:
  sz ([Ld]^^n++W2::ls) = n + sz ls.
Proof.
  induction n; cbn; lia.
Qed.

Lemma sz_Ld ls:
  sz (ls++[Ld]) = sz ls + 1.
Proof.
  induction ls; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([Ld;Ld;Ld;W1;Ld;Ld;Ld;W2;Ld;Ld;Ld;Ld],9)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => 2 <= sz ls /\ 2<=n).
  2: cbn; lia.
  intros [ls n] HP.
  eexists; split.
  1: apply BigStep,HP.
  cbn match.
  rewrite sz_Ld,sz_Lds.
  lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RA_1RE0LD_1LE1RB_1LC0LF_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf <* <[1;1;1;1;1;1]).
Notation ld := [1;1;1;1;1;1].
Notation w1 := [1;1;1;1;1;1;1;1;0;1;1;1].
Notation w2 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1].
Notation w3 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;0].
Notation w4 := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;0;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1].
Notation rd1 := [1;1;1;1;1;0].
Notation rh := ([1;1;1;1;1;1;1;1;1]*>0inf).

Notation hRx := (A,[]).
Notation hRy := (A,<[1;1;1]).
Notation hR := (B,<[0;1]).
Notation hL := (D,[0;1]).
Notation hL' := (E,[1;0]).

Notation hx := [(hRx,hL)].
Notation hy := [(hRy,hL)].
Notation h := [(hR,hL)].
Notation h' := [(hR,hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  ut; es' & r.
Qed.

Inductive LD := Ld | W1 | W2 | W4.

Fixpoint LC ls :=
match ls with
| x::t => LC t ++
  match x with
  | Ld => ld
  | W1 => w1
  | W2 => w2
  | W4 => w4
  end
| [] => []
end.

Fixpoint sz ls :=
match ls with
| x::t => match x with Ld => 1 | _ => O end + sz t
| [] => O
end.

Lemma ld_Incs' k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma ld_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma w1_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w1 w1.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma w2_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w2 w2.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma w4_Incs k:
  segRLs tm (hx++h^^k) (hx++h^^k) w4 w4.
Proof.
  tr; [|wal].
  esc.
Qed.

Lemma LIncs ls:
  segRLs tm hx (hx++h^^(2^(sz ls)-1)) (LC ls) (LC ls).
Proof.
  induction ls as [|[] ls]; cbn[sz LC].
  1: esc.
  all: rewrite Nat.pow_add_r; cat1 IHls.
  - applys_eq ld_Incs; flia.
  - applys_eq w1_Incs; flia.
  - applys_eq w2_Incs; flia.
  - applys_eq w4_Incs; flia.
Qed.

Lemma w3_Incs k:
  segRLs tm (hx++h^^k) (hy++h^^(1+k)) w3 w2.
Proof.
  rewrite lpow_add,app_assoc.
  tr; [|wal].
  esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (hy++h^^k) (hy++h^^(k*2)) rd1 ld.
Proof.
  tr.
  2: apply ld_Incs'.
  esc.
Qed.

Lemma LIncs' ls n:
  segRLs tm hx (hy++h^^(2^(n+sz ls))) (LC ls ++ w3 ++ rd1^^n) (LC ([Ld]^^n++W2::ls)).
Proof.
  induction n.
  - cat1 (LIncs ls).
    rewrite Nat.add_0_l.
    applys_eq w3_Incs; flia.
  - eassert (I1:_).
    { eapply segRLs_concat.
      1: apply IHn.
      apply rd1_Incs. }
    applys_eq I1.
    1: cbn; flia.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    repeat rewrite <-app_assoc; trivial.
Qed.

Lemma rd1_Incs' k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma RIncs k:
  sideRLs tm (h'^^(2^k*2)) (rd1^^k*>rh) (rd1^^(S k)*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow lpow].
    repeat rewrite Str_app_assoc.
    cat.
    2: apply IHk.
    applys_eq rd1_Incs'; flia.
Qed.

Lemma RIncs' k:
  sideRLs tm (h'^^(2^k*2-2)) rh (rd1^^k*>rh).
Proof.
  induction k.
  - esc.
  - cbn[Nat.pow].
    replace (2*2^k*2-2) with (2^k*2-2+2^k*2) by lia.
    rewrite lpow_add.
    tr.
    1: apply IHk.
    apply RIncs.
Qed.

Lemma w3_Incs' k:
  segRLs tm (h^^k) (h'^^(k*2)) w3 w3.
Proof.
  induction k.
  1: esc.
  cbn[Nat.mul Nat.add lpow].
  rewrite app_assoc.
  tr.
  2: apply IHk.
  esc.
Qed.

Lemma RIncs'' k:
  sideRLs tm (hy++h^^(2^k)) (rd1^^2*>rh) (w3*>rd1^^k*>rh).
Proof.
  replace (2^k) with (1+(2^k-1)) by lia.
  rewrite lpow_add,app_assoc.
  eapply @sideRLs_trans with (r2:=w3*>rh).
  1: esc.
  cat1 w3_Incs'.
  applys_eq (RIncs' k); flia.
Qed.

Definition S' '(ls,n) :=
  lh {{{ (hRx,R) }}} ((LC ls ++ w3 ++ rd1^^n)*>rh).

Lemma LC_app a b:
  LC (a++b) = LC b ++ LC a.
Proof.
  induction a; cbn.
  - rewrite app_nil_r; trivial.
  - rewrite IHa,app_assoc; trivial.
Qed.

Lemma BigStep ls n:
  2<=n ->
  S' (ls,n) -->+
  S' (([Ld]^^(n-2)++W2::ls)++[Ld],n-2+sz ls).
Proof.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (LIncs' ls (n-2)).
    apply RIncs''.
  }
  eapply sideRLs_1 in I1.
  unfold S'.
  intros Hn.
  rewrite lpow_add.
  repeat rewrite Str_app_assoc in *.
  rewrite lpow_add' in I1.
  rewrite Nat.sub_add in I1 by lia.
  follow10 I1.
  follow LRst.
  rewrite (LC_app _ [Ld]),Str_app_assoc.
  rewrite lpow_add'.
  finish.
Qed.

Lemma sz_Lds n ls:
  sz ([Ld]^^n++W2::ls) = n + sz ls.
Proof.
  induction n; cbn; lia.
Qed.

Lemma sz_Ld ls:
  sz (ls++[Ld]) = sz ls + 1.
Proof.
  induction ls; cbn; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([Ld;Ld;Ld;W1;Ld;Ld;Ld;W4;Ld;Ld;Ld;Ld],9)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => 2 <= sz ls /\ 2<=n).
  2: cbn; lia.
  intros [ls n] HP.
  eexists; split.
  1: apply BigStep,HP.
  cbn match.
  rewrite sz_Ld,sz_Lds.
  lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC---_1RD0RA_0LA0LC_1RF0LE_1RD1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf<*<[1;0;1]).
Notation ld := [1;0;0].
Notation ld' := [0;1;0].
Notation lr := [0].
Notation rd0 := [0;0].
Notation rd1 := [1;0].
Notation rl := [0;1;0;0].
Notation hR := (D,<[0;1]).
Notation hRx := (C,<[0]).
Notation hL := (E,[0;0]).
Notation hR' := (F,<[]).
Notation hL' := (E,[]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation h' := [(hR',hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  er.
Qed.

Notation rd110 := (rd1++rd1++rd0).

Definition RC0 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC0' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC1'_0 a c d e :=
  ld^^a *> ld'^^c *> rd0 *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.

Lemma LRst0 a b c d e:
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->*
  lh {{{ (hRx,R) }}} RC0' (1+a) b c d e.
Proof.
  ut; er.
Qed.

Lemma LRst1 a b c d e:
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hRx,R) }}} RC1' (1+a) b (1+c) d e.
Proof.
  ut; er.
Qed.

Lemma LRst1_0 a c d e:
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hRx,R) }}} RC1'_0 (1+a) (2+c) d e.
Proof.
  ut; er.
Qed.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[Nat.pow lpow].
    cat1 ld_Incs.
    applys_eq (IHn (k*2)); flia.
Qed.


Lemma ld_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma lds_OvIncs' k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    cat1 IHn.
    applys_eq ld_OvIncs; flia.
Qed.

Lemma lds_OvIncs n:
  segRLs tm hx (hx++h^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  applys_eq (lds_OvIncs' 0 n); flia.
Qed.

Lemma ld'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld' ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma ld's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld'^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    do 2 rewrite lpow_add.
    cat1 IHn.
    applys_eq ld'_OvIncs; flia.
Qed.

Lemma rd0_OvIncs k:
  segRLs tm (hx++h^^k) (h'^^(k+1)) rd0 lr.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma rd0_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd0s_Incs k n:
  segRLs tm (h'^^(k*2^n)) (h'^^k) (rd0^^n) (rd0^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: apply IHn.
    applys_eq rd0_Incs; flia.
Qed.

Lemma rd110_Incs k:
  segRLs tm (h'^^(k*8)) (h'^^k) rd110 rd110.
Proof.
  applys_eq (segRLs_addmul_v2 8 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110s_Incs k n:
  segRLs tm (h'^^(k*2^(n*3))) (h'^^k) (rd110^^n) (rd110^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul].
    cat.
    2: apply IHn.
    rewrite Nat.pow_add_r.
    applys_eq rd110_Incs; flia.
Qed.


Lemma lr_Incs k:
  segRLs tm (h^^k) (h'^^k) lr lr.
Proof.
  wal.
Qed.

Lemma rl_Incs k:
  segRLs tm (h'^^k) (h^^k) rl rl.
Proof.
  wal.
Qed.

Lemma RIncs1 a b c d e:
  b+1<=a ->
  b+d+e*3+1=a+c ->
  sideRLs tm hx (RC0' a b c d e) (RC1 a b c d e).
Proof.
  intros Ha Ha'.
  unfold RC0',RC1.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b-1+1+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b-1+c) with (0+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma RIncs0 a b c d e:
  b<=a ->
  a+c = b+d+e*3+4 ->
  sideRLs tm hx (RC1' a b c d e) (RC0 a b c d (e+1)).
Proof.
  intros Ha Ha'.
  unfold RC1',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b+c) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-lpow_add'.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step0 a b c d e:
  b<=a ->
  b+d+e*3=a+c ->
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->+
  lh {{{ (hL,L) }}} RC1 (1+a) b c d e.
Proof.
  intros Ha Ha'.
  follow LRst0.
  unshelve epose proof (RIncs1 (1+a) b c d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow10 I1.
  finish.
Qed.

Lemma Step1 a b c d e:
  b<=1+a ->
  b+d+e*3+2=a+c ->
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hL,L) }}} RC0 (1+a) b (1+c) d (e+1).
Proof.
  intros Ha Ha'.
  follow LRst1.
  unshelve epose proof (RIncs0 (1+a) b (1+c) d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2 d e :=
  ld^^(d+e*3+4) *> lr *> rl *> lr *> rd0^^d *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs1_0 a c d e:
  d+e*3+1=a+c ->
  sideRLs tm hx (RC1'_0 (1+a) (2+c) d e) (RC2 d e).
Proof.
  intros Ha.
  unfold RC1'_0,RC2.
  replace (d+e*3+4) with (1+a+(2+c)) by lia.
  rewrite <-(lpow_add' _ (1+a) (2+c)).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (1+a+(2+c)) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-lpow_add'.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step1_0 a c d e:
  d+e*3+1=a+c ->
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hL,L) }}} RC2 d e.
Proof.
  intros Ha'.
  follow LRst1_0.
  unshelve epose proof (RIncs1_0 a c d e _) as I1.
  1: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2' d e :=
  ld^^(d+e*3+5) *> rd0 *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma LRst2 d e:
  lh {{{ (hL,L) }}} RC2 d e -->*
  lh {{{ (hRx,R) }}} RC2' d e.
Proof.
  ut; es.
Qed.

Definition RC3 d e :=
  ld^^(d+e*3+5) *> lr *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma RIncs2 d e:
  sideRLs tm hx (RC2' d e) (RC3 d e).
Proof.
  unfold RC2',RC3.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+5) with (0+(e+1)*3+(1+d)+1) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Definition RC3' d e :=
  ld^^(d+e*3+6) *> ld'^^1 *> rd0 *> rd0^^d *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma LRst3 d e:
  lh {{{ (hL,L) }}} RC3 d e -->*
  lh {{{ (hRx,R) }}} RC3' d e.
Proof.
  ut; es.
Qed.

Definition RC4 d e :=
  ld^^(d+e*3+6+1) *> lr *> rd0^^d *> rd110^^(e+1+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs3 d e:
  sideRLs tm hx (RC3' d e) (RC4 d e).
Proof.
  unfold RC3',RC4.
  rewrite <-(lpow_add' _ (_+6) 1).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+6+1) with (4+(e+1)*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-(lpow_add' _ (e+1)).
  cat1 rd110s_Incs.
  esc.
Qed.

Notation rd110' := (ld++ld').

Definition RC4' d e :=
  ld^^(d+e*3+9) *> rd0 *> rd0^^d *> ld' *> rd110'^^(e+1) *> ld^^1 *> rd0 *> rl *> lr *> 0inf.

Lemma LRst4 d e:
  lh {{{ (hL,L) }}} RC4 (1+d) e -->*
  lh {{{ (hRx,R) }}} RC4' d e.
Proof.
  ut; es' d e.
Qed.

Lemma rd110'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(3+k*4)) rd110' (ld^^2).
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  1: esx.
  applys_eq (segRLs_addmul_v2 1 4 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^(n*2)-1)) (rd110'^^n) (ld^^(n*2)).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow Nat.mul lpow].
    rewrite lpow_add.
    cat1 rd110'_OvIncs.
    applys_eq (IHn (3+k*4)).
    rewrite Nat.pow_add_r.
    flia.
Qed.

Lemma ld'_OvIncs' k:
  segRLs tm (h'^^(k+1)) (hx++h^^k) ld' rl.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma RIncs_0inf n:
  sideRLs tm (h'^^(2^n)) 0inf (rd0^^n*>rd1*>0inf).
Proof.
  eapply sideRLs_trans_add with (n1:=O) (n2:=2^n) (w3:=rd0^^n*>rd0*>0inf).
  - st.
    rewrite lpow_all0 by solve_const0_eq.
    esc.
  - replace (2^n) with (1*2^n) by lia.
    cat1 rd0s_Incs.
    esc.
Qed.

Lemma RIncs4 d e:
  sideRLs tm hx (RC4' d e) (RC0 (d+e*3+9) d ((e+1)*2+1) (11+e*5) 0).
Proof.
  unfold RC4',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+9) with (9+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-(Nat.sub_add 1 (2^(9+e*3))) by lia.
  cat1 ld'_OvIncs'.
  rewrite <-(lpow_add' _ (_*2) 1).
  cat1 rd110's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 lds_OvIncs'.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  change (rd110^^0*>rd0*>rd1*>0inf) with (rd0^^1*>rd1*>0inf).
  rewrite lpow_add'.
  applys_eq RIncs_0inf; flia.
Qed.

Definition S' '(a,b,c,d,e) :=
  lh {{{ (hL,L) }}} RC0 a b (1+c) (1+d) e.

Definition P '(a,b,c,d,e) :=
  b<=a /\
  b+d+e*3+1=a+c.

Ltac follow10 H := eapply progress_evstep_trans; [apply H; try lia|].

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\
  P x'.
Proof.
  destruct x as [[[[a b] c] d] e].
  unfold P.
  intros HP.
  destruct b.
  - eexists (d+e*3+9,d,(e+1)*2,10+e*5,O); split.
    + follow10 Step0.
      follow Step1_0.
      1: lia.
      follow LRst2.
      epose proof (RIncs2 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst3.
      epose proof (RIncs3 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst4.
      epose proof (RIncs4 d e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      unfold S'.
      finish.
    + lia.
  - eexists (_,_,_,_,_); split.
    + follow10 Step0.
      follow Step1.
      1,2: lia.
      finish.
    + lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (13,4,0,5,1)%nat).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  - exact (fun x => closed x).
  - cbn; lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1RD_0LC0LE_1RF1LD_1RA0LD_1RB0RC_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf<*<[1;0;1]).
Notation ld := [1;0;0].
Notation ld' := [0;1;0].
Notation lr := [0].
Notation rd0 := [0;0].
Notation rd1 := [1;0].
Notation rl := [0;1;0;0].
Notation hR := (B,<[0;1]).
Notation hRx := (E,<[0]).
Notation hL := (D,[0;0]).
Notation hR' := (A,<[]).
Notation hL' := (D,[]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation h' := [(hR',hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  er.
Qed.

Notation rd110 := (rd1++rd1++rd0).

Definition RC0 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC0' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC1'_0 a c d e :=
  ld^^a *> ld'^^c *> rd0 *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.

Lemma LRst0 a b c d e:
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->*
  lh {{{ (hRx,R) }}} RC0' (1+a) b c d e.
Proof.
  ut; er.
Qed.

Lemma LRst1 a b c d e:
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hRx,R) }}} RC1' (1+a) b (1+c) d e.
Proof.
  ut; er.
Qed.

Lemma LRst1_0 a c d e:
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hRx,R) }}} RC1'_0 (1+a) (2+c) d e.
Proof.
  ut; er.
Qed.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[Nat.pow lpow].
    cat1 ld_Incs.
    applys_eq (IHn (k*2)); flia.
Qed.


Lemma ld_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma lds_OvIncs' k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    cat1 IHn.
    applys_eq ld_OvIncs; flia.
Qed.

Lemma lds_OvIncs n:
  segRLs tm hx (hx++h^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  applys_eq (lds_OvIncs' 0 n); flia.
Qed.

Lemma ld'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld' ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma ld's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld'^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    do 2 rewrite lpow_add.
    cat1 IHn.
    applys_eq ld'_OvIncs; flia.
Qed.

Lemma rd0_OvIncs k:
  segRLs tm (hx++h^^k) (h'^^(k+1)) rd0 lr.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma rd0_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd0s_Incs k n:
  segRLs tm (h'^^(k*2^n)) (h'^^k) (rd0^^n) (rd0^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: apply IHn.
    applys_eq rd0_Incs; flia.
Qed.

Lemma rd110_Incs k:
  segRLs tm (h'^^(k*8)) (h'^^k) rd110 rd110.
Proof.
  applys_eq (segRLs_addmul_v2 8 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110s_Incs k n:
  segRLs tm (h'^^(k*2^(n*3))) (h'^^k) (rd110^^n) (rd110^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul].
    cat.
    2: apply IHn.
    rewrite Nat.pow_add_r.
    applys_eq rd110_Incs; flia.
Qed.


Lemma lr_Incs k:
  segRLs tm (h^^k) (h'^^k) lr lr.
Proof.
  wal.
Qed.

Lemma rl_Incs k:
  segRLs tm (h'^^k) (h^^k) rl rl.
Proof.
  wal.
Qed.

Lemma RIncs1 a b c d e:
  b+1<=a ->
  b+d+e*3+1=a+c ->
  sideRLs tm hx (RC0' a b c d e) (RC1 a b c d e).
Proof.
  intros Ha Ha'.
  unfold RC0',RC1.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b-1+1+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b-1+c) with (0+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma RIncs0 a b c d e:
  b<=a ->
  a+c = b+d+e*3+4 ->
  sideRLs tm hx (RC1' a b c d e) (RC0 a b c d (e+1)).
Proof.
  intros Ha Ha'.
  unfold RC1',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b+c) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-lpow_add'.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step0 a b c d e:
  b<=a ->
  b+d+e*3=a+c ->
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->+
  lh {{{ (hL,L) }}} RC1 (1+a) b c d e.
Proof.
  intros Ha Ha'.
  follow LRst0.
  unshelve epose proof (RIncs1 (1+a) b c d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow10 I1.
  finish.
Qed.

Lemma Step1 a b c d e:
  b<=1+a ->
  b+d+e*3+2=a+c ->
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hL,L) }}} RC0 (1+a) b (1+c) d (e+1).
Proof.
  intros Ha Ha'.
  follow LRst1.
  unshelve epose proof (RIncs0 (1+a) b (1+c) d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2 d e :=
  ld^^(d+e*3+4) *> lr *> rl *> lr *> rd0^^d *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs1_0 a c d e:
  d+e*3+1=a+c ->
  sideRLs tm hx (RC1'_0 (1+a) (2+c) d e) (RC2 d e).
Proof.
  intros Ha.
  unfold RC1'_0,RC2.
  replace (d+e*3+4) with (1+a+(2+c)) by lia.
  rewrite <-(lpow_add' _ (1+a) (2+c)).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (1+a+(2+c)) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-lpow_add'.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step1_0 a c d e:
  d+e*3+1=a+c ->
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hL,L) }}} RC2 d e.
Proof.
  intros Ha'.
  follow LRst1_0.
  unshelve epose proof (RIncs1_0 a c d e _) as I1.
  1: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2' d e :=
  ld^^(d+e*3+5) *> rd0 *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma LRst2 d e:
  lh {{{ (hL,L) }}} RC2 d e -->*
  lh {{{ (hRx,R) }}} RC2' d e.
Proof.
  ut; es.
Qed.

Definition RC3 d e :=
  ld^^(d+e*3+5) *> lr *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma RIncs2 d e:
  sideRLs tm hx (RC2' d e) (RC3 d e).
Proof.
  unfold RC2',RC3.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+5) with (0+(e+1)*3+(1+d)+1) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Definition RC3' d e :=
  ld^^(d+e*3+6) *> ld'^^1 *> rd0 *> rd0^^d *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma LRst3 d e:
  lh {{{ (hL,L) }}} RC3 d e -->*
  lh {{{ (hRx,R) }}} RC3' d e.
Proof.
  ut; es.
Qed.

Definition RC4 d e :=
  ld^^(d+e*3+6+1) *> lr *> rd0^^d *> rd110^^(e+1+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs3 d e:
  sideRLs tm hx (RC3' d e) (RC4 d e).
Proof.
  unfold RC3',RC4.
  rewrite <-(lpow_add' _ (_+6) 1).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+6+1) with (4+(e+1)*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-(lpow_add' _ (e+1)).
  cat1 rd110s_Incs.
  esc.
Qed.

Notation rd110' := (ld++ld').

Definition RC4' d e :=
  ld^^(d+e*3+9) *> rd0 *> rd0^^d *> ld' *> rd110'^^(e+1) *> ld^^1 *> rd0 *> rl *> lr *> 0inf.

Lemma LRst4 d e:
  lh {{{ (hL,L) }}} RC4 (1+d) e -->*
  lh {{{ (hRx,R) }}} RC4' d e.
Proof.
  ut; es' d e.
Qed.

Lemma rd110'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(3+k*4)) rd110' (ld^^2).
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  1: esx.
  applys_eq (segRLs_addmul_v2 1 4 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^(n*2)-1)) (rd110'^^n) (ld^^(n*2)).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow Nat.mul lpow].
    rewrite lpow_add.
    cat1 rd110'_OvIncs.
    applys_eq (IHn (3+k*4)).
    rewrite Nat.pow_add_r.
    flia.
Qed.

Lemma ld'_OvIncs' k:
  segRLs tm (h'^^(k+1)) (hx++h^^k) ld' rl.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma RIncs_0inf n:
  sideRLs tm (h'^^(2^n)) 0inf (rd0^^n*>rd1*>0inf).
Proof.
  eapply sideRLs_trans_add with (n1:=O) (n2:=2^n) (w3:=rd0^^n*>rd0*>0inf).
  - st.
    rewrite lpow_all0 by solve_const0_eq.
    esc.
  - replace (2^n) with (1*2^n) by lia.
    cat1 rd0s_Incs.
    esc.
Qed.

Lemma RIncs4 d e:
  sideRLs tm hx (RC4' d e) (RC0 (d+e*3+9) d ((e+1)*2+1) (11+e*5) 0).
Proof.
  unfold RC4',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+9) with (9+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-(Nat.sub_add 1 (2^(9+e*3))) by lia.
  cat1 ld'_OvIncs'.
  rewrite <-(lpow_add' _ (_*2) 1).
  cat1 rd110's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 lds_OvIncs'.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  change (rd110^^0*>rd0*>rd1*>0inf) with (rd0^^1*>rd1*>0inf).
  rewrite lpow_add'.
  applys_eq RIncs_0inf; flia.
Qed.

Definition S' '(a,b,c,d,e) :=
  lh {{{ (hL,L) }}} RC0 a b (1+c) (1+d) e.

Definition P '(a,b,c,d,e) :=
  b<=a /\
  b+d+e*3+1=a+c.

Ltac follow10 H := eapply progress_evstep_trans; [apply H; try lia|].

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\
  P x'.
Proof.
  destruct x as [[[[a b] c] d] e].
  unfold P.
  intros HP.
  destruct b.
  - eexists (d+e*3+9,d,(e+1)*2,10+e*5,O); split.
    + follow10 Step0.
      follow Step1_0.
      1: lia.
      follow LRst2.
      epose proof (RIncs2 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst3.
      epose proof (RIncs3 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst4.
      epose proof (RIncs4 d e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      unfold S'.
      finish.
    + lia.
  - eexists (_,_,_,_,_); split.
    + follow10 Step0.
      follow Step1.
      1,2: lia.
      finish.
    + lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,0,0,5,0)%nat).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  - exact (fun x => closed x).
  - cbn; lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1RA_0LD0LE_1RF1LA_1RC0RD_0RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh := (0inf<*<[1;0;1]).
Notation ld := [1;0;0].
Notation ld' := [0;1;0].
Notation lr := [0].
Notation rd0 := [0;0].
Notation rd1 := [1;0].
Notation rl := [0;1;0;0].
Notation hR := (C,<[0;1]).
Notation hRx := (E,<[0]).
Notation hL := (A,[0;0]).
Notation hR' := (B,<[]).
Notation hL' := (A,[]).
Notation h := [(hR,hL)].
Notation hx := [(hRx,hL)].
Notation h' := [(hR',hL')].

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh {{{ (hRx,R) }}} ld *> r.
Proof.
  er.
Qed.

Notation rd110 := (rd1++rd1++rd0).

Definition RC0 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1 a b c d e :=
  ld^^a *> lr *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC0' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rd1 *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd0 *> rd1 *> 0inf.
Definition RC1' a b c d e :=
  ld^^a *> rd0 *> rd0^^b *> rl *> ld^^c *> lr *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.
Definition RC1'_0 a c d e :=
  ld^^a *> ld'^^c *> rd0 *> rl *> lr *> rd0^^d *> rd110^^e *> rd1 *> rd1 *> 0inf.

Lemma LRst0 a b c d e:
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->*
  lh {{{ (hRx,R) }}} RC0' (1+a) b c d e.
Proof.
  ut; er.
Qed.

Lemma LRst1 a b c d e:
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hRx,R) }}} RC1' (1+a) b (1+c) d e.
Proof.
  ut; er.
Qed.

Lemma LRst1_0 a c d e:
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hRx,R) }}} RC1'_0 (1+a) (2+c) d e.
Proof.
  ut; er.
Qed.

Lemma ld_Incs k:
  segRLs tm (h^^k) (h^^(k*2)) ld ld.
Proof.
  applys_eq (segRLs_addmul_v2 1 2 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma lds_Incs k n:
  segRLs tm (h^^k) (h^^(k*2^n)) (ld^^n) (ld^^n).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[Nat.pow lpow].
    cat1 ld_Incs.
    applys_eq (IHn (k*2)); flia.
Qed.


Lemma ld_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma lds_OvIncs' k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    cat1 IHn.
    applys_eq ld_OvIncs; flia.
Qed.

Lemma lds_OvIncs n:
  segRLs tm hx (hx++h^^(2^n-1)) (ld^^n) (ld^^n).
Proof.
  applys_eq (lds_OvIncs' 0 n); flia.
Qed.

Lemma ld'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(1+k*2)) ld' ld.
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  2: apply ld_Incs.
  esc.
Qed.

Lemma ld's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^n-1)) (ld'^^n) (ld^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow].
    replace (S n) with (n+1) by lia.
    do 2 rewrite lpow_add.
    cat1 IHn.
    applys_eq ld'_OvIncs; flia.
Qed.

Lemma rd0_OvIncs k:
  segRLs tm (hx++h^^k) (h'^^(k+1)) rd0 lr.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma rd0_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd0 rd0.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd1_Incs k:
  segRLs tm (h'^^(k*2)) (h'^^k) rd1 rd1.
Proof.
  applys_eq (segRLs_addmul_v2 2 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd0s_Incs k n:
  segRLs tm (h'^^(k*2^n)) (h'^^k) (rd0^^n) (rd0^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    cat.
    2: apply IHn.
    applys_eq rd0_Incs; flia.
Qed.

Lemma rd110_Incs k:
  segRLs tm (h'^^(k*8)) (h'^^k) rd110 rd110.
Proof.
  applys_eq (segRLs_addmul_v2 8 1 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110s_Incs k n:
  segRLs tm (h'^^(k*2^(n*3))) (h'^^k) (rd110^^n) (rd110^^n).
Proof.
  induction n.
  - rewrite Nat.mul_1_r.
    apply segRLs_nil.
  - cbn[lpow Nat.mul].
    cat.
    2: apply IHn.
    rewrite Nat.pow_add_r.
    applys_eq rd110_Incs; flia.
Qed.


Lemma lr_Incs k:
  segRLs tm (h^^k) (h'^^k) lr lr.
Proof.
  wal.
Qed.

Lemma rl_Incs k:
  segRLs tm (h'^^k) (h^^k) rl rl.
Proof.
  wal.
Qed.

Lemma RIncs1 a b c d e:
  b+1<=a ->
  b+d+e*3+1=a+c ->
  sideRLs tm hx (RC0' a b c d e) (RC1 a b c d e).
Proof.
  intros Ha Ha'.
  unfold RC0',RC1.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b-1+1+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b-1+c) with (0+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma RIncs0 a b c d e:
  b<=a ->
  a+c = b+d+e*3+4 ->
  sideRLs tm hx (RC1' a b c d e) (RC0 a b c d (e+1)).
Proof.
  intros Ha Ha'.
  unfold RC1',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace a with (a-b+b) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  cat1 rl_Incs.
  cat1 lds_Incs.
  rewrite <-Nat.pow_add_r.
  cat1 lr_Incs.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (a-b+c) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-lpow_add'.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step0 a b c d e:
  b<=a ->
  b+d+e*3=a+c ->
  lh {{{ (hL,L) }}} RC0 a b (1+c) d e -->+
  lh {{{ (hL,L) }}} RC1 (1+a) b c d e.
Proof.
  intros Ha Ha'.
  follow LRst0.
  unshelve epose proof (RIncs1 (1+a) b c d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow10 I1.
  finish.
Qed.

Lemma Step1 a b c d e:
  b<=1+a ->
  b+d+e*3+2=a+c ->
  lh {{{ (hL,L) }}} RC1 a (1+b) c d e -->*
  lh {{{ (hL,L) }}} RC0 (1+a) b (1+c) d (e+1).
Proof.
  intros Ha Ha'.
  follow LRst1.
  unshelve epose proof (RIncs0 (1+a) b (1+c) d e _ _) as I1.
  1,2: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2 d e :=
  ld^^(d+e*3+4) *> lr *> rl *> lr *> rd0^^d *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs1_0 a c d e:
  d+e*3+1=a+c ->
  sideRLs tm hx (RC1'_0 (1+a) (2+c) d e) (RC2 d e).
Proof.
  intros Ha.
  unfold RC1'_0,RC2.
  replace (d+e*3+4) with (1+a+(2+c)) by lia.
  rewrite <-(lpow_add' _ (1+a) (2+c)).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  replace (1+a+(2+c)) with (4+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-lpow_add'.
  cat1 rd110s_Incs.
  esc.
Qed.

Lemma Step1_0 a c d e:
  d+e*3+1=a+c ->
  lh {{{ (hL,L) }}} RC1 a 0 c d e -->*
  lh {{{ (hL,L) }}} RC2 d e.
Proof.
  intros Ha'.
  follow LRst1_0.
  unshelve epose proof (RIncs1_0 a c d e _) as I1.
  1: lia.
  eapply sideRLs_1 in I1.
  follow100 I1.
  finish.
Qed.

Definition RC2' d e :=
  ld^^(d+e*3+5) *> rd0 *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd0 *> rd1 *> 0inf.

Lemma LRst2 d e:
  lh {{{ (hL,L) }}} RC2 d e -->*
  lh {{{ (hRx,R) }}} RC2' d e.
Proof.
  ut; es.
Qed.

Definition RC3 d e :=
  ld^^(d+e*3+5) *> lr *> rd1 *> rd0^^(1+d) *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma RIncs2 d e:
  sideRLs tm hx (RC2' d e) (RC3 d e).
Proof.
  unfold RC2',RC3.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+5) with (0+(e+1)*3+(1+d)+1) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd1_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  cat1 rd110s_Incs.
  esc.
Qed.

Definition RC3' d e :=
  ld^^(d+e*3+6) *> ld'^^1 *> rd0 *> rd0^^d *> rd110^^(e+1) *> rd1 *> rd1 *> 0inf.

Lemma LRst3 d e:
  lh {{{ (hL,L) }}} RC3 d e -->*
  lh {{{ (hRx,R) }}} RC3' d e.
Proof.
  ut; es.
Qed.

Definition RC4 d e :=
  ld^^(d+e*3+6+1) *> lr *> rd0^^d *> rd110^^(e+1+1) *> rd0 *> rd1 *> 0inf.

Lemma RIncs3 d e:
  sideRLs tm hx (RC3' d e) (RC4 d e).
Proof.
  unfold RC3',RC4.
  rewrite <-(lpow_add' _ (_+6) 1).
  cat1 lds_OvIncs.
  cat1 ld's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+6+1) with (4+(e+1)*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite Nat.pow_add_r.
  rewrite <-(lpow_add' _ (e+1)).
  cat1 rd110s_Incs.
  esc.
Qed.

Notation rd110' := (ld++ld').

Definition RC4' d e :=
  ld^^(d+e*3+9) *> rd0 *> rd0^^d *> ld' *> rd110'^^(e+1) *> ld^^1 *> rd0 *> rl *> lr *> 0inf.

Lemma LRst4 d e:
  lh {{{ (hL,L) }}} RC4 (1+d) e -->*
  lh {{{ (hRx,R) }}} RC4' d e.
Proof.
  ut; es' d e.
Qed.

Lemma rd110'_OvIncs k:
  segRLs tm (hx++h^^k) (hx++h^^(3+k*4)) rd110' (ld^^2).
Proof.
  rewrite lpow_add,app_assoc.
  tr.
  1: esx.
  applys_eq (segRLs_addmul_v2 1 4 k 0 0); unfold DH0.
  1,2: flia.
  1,2: esc.
Qed.

Lemma rd110's_OvIncs k n:
  segRLs tm (hx++h^^k) (hx++h^^((k+1)*2^(n*2)-1)) (rd110'^^n) (ld^^(n*2)).
Proof.
  gen k.
  induction n; intros.
  - rewrite Nat.mul_1_r,Nat.add_sub.
    apply segRLs_nil.
  - cbn[Nat.pow Nat.mul lpow].
    rewrite lpow_add.
    cat1 rd110'_OvIncs.
    applys_eq (IHn (3+k*4)).
    rewrite Nat.pow_add_r.
    flia.
Qed.

Lemma ld'_OvIncs' k:
  segRLs tm (h'^^(k+1)) (hx++h^^k) ld' rl.
Proof.
  rewrite Nat.add_comm,lpow_add.
  tr.
  1: esx.
  wal.
Qed.

Lemma RIncs_0inf n:
  sideRLs tm (h'^^(2^n)) 0inf (rd0^^n*>rd1*>0inf).
Proof.
  eapply sideRLs_trans_add with (n1:=O) (n2:=2^n) (w3:=rd0^^n*>rd0*>0inf).
  - st.
    rewrite lpow_all0 by solve_const0_eq.
    esc.
  - replace (2^n) with (1*2^n) by lia.
    cat1 rd0s_Incs.
    esc.
Qed.

Lemma RIncs4 d e:
  sideRLs tm hx (RC4' d e) (RC0 (d+e*3+9) d ((e+1)*2+1) (11+e*5) 0).
Proof.
  unfold RC4',RC0.
  cat1 lds_OvIncs.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  replace (d+e*3+9) with (9+e*3+d) by lia.
  rewrite Nat.pow_add_r.
  cat1 rd0s_Incs.
  rewrite <-(Nat.sub_add 1 (2^(9+e*3))) by lia.
  cat1 ld'_OvIncs'.
  rewrite <-(lpow_add' _ (_*2) 1).
  cat1 rd110's_OvIncs.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 lds_OvIncs'.
  rewrite Nat.sub_add by lia.
  rewrite <-Nat.pow_add_r.
  cat1 rd0_OvIncs.
  rewrite Nat.sub_add by lia.
  cat1 rl_Incs.
  cat1 lr_Incs.
  change (rd110^^0*>rd0*>rd1*>0inf) with (rd0^^1*>rd1*>0inf).
  rewrite lpow_add'.
  applys_eq RIncs_0inf; flia.
Qed.

Definition S' '(a,b,c,d,e) :=
  lh {{{ (hL,L) }}} RC0 a b (1+c) (1+d) e.

Definition P '(a,b,c,d,e) :=
  b<=a /\
  b+d+e*3+1=a+c.

Ltac follow10 H := eapply progress_evstep_trans; [apply H; try lia|].

Lemma closed x:
  P x ->
  exists x',
  S' x -->+ S' x' /\
  P x'.
Proof.
  destruct x as [[[[a b] c] d] e].
  unfold P.
  intros HP.
  destruct b.
  - eexists (d+e*3+9,d,(e+1)*2,10+e*5,O); split.
    + follow10 Step0.
      follow Step1_0.
      1: lia.
      follow LRst2.
      epose proof (RIncs2 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst3.
      epose proof (RIncs3 (1+d) e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      follow LRst4.
      epose proof (RIncs4 d e) as I1.
      eapply sideRLs_1 in I1.
      follow100 I1; clear I1.
      unfold S'.
      finish.
    + lia.
  - eexists (_,_,_,_,_); split.
    + follow10 Step0.
      follow Step1.
      1,2: lia.
      finish.
    + lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (9,0,2,10,0)%nat).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  - exact (fun x => closed x).
  - cbn; lia.
Qed.

End TM7.


