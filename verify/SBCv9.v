From BusyCoq Require Import Individual62.
Require Import ZifyNat ZifyN Lia.
Require Import ZArith.
Require Import List.
Require Import String.
From BusyCoq Require Import Longitudinal.

Open Scope list.

Import Eqb.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Definition Nsubge(a b:N) :=
(if b <=? a then Some (a-b) else None)%N.

Lemma Nsubge_spec a b c:
  Nsubge a b = Some c ->
  (a=c+b)%N.
Proof.
  unfold Nsubge.
  intros.
  destruct (N.leb_spec b a);
  inverts H; lia.
Qed.

Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Ltac ec := econstructor.
Ltac eex := repeat eexists.

Ltac des_if H :=
  cbn[if_None] in H;
  cbn[if_Some] in H;
  let E:=fresh "E" in
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  | ?a &&& _ = _ =>
    destruct a eqn:E
  end.

Ltac des_if' H := des_if H; [|inverts H].


Lemma segRLs_addmul_v3 a a' x b b' tm h h' w1 w2:
  segRLs tm (h^^b) (h'^^b') w1 w2 ->
  segRLs tm (h^^a) (h'^^a') w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h'^^(x*a'+b')) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ b').
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    do 2 rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LB_1RC1RD_0RA1RE_1RF0RD_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,<[0;0]).
Notation hL := (B,[0;0]).
Notation hR' := (E,<[1;0;1]).
Notation hL' := (B,[0;1;1]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR' := [(hL',hR')].


Definition LC a b := 0inf <* [1]^^a <* <[1;0]^^b.

Definition tm' := flip tm.

Lemma LInc a b r:
  LC a (1+b) {{{ (hL',L) }}} r -->*
  LC (4+a) b {{{ (hR',R) }}} r.
Proof.
  ut.
  esx.
Qed.

Lemma LIncs n a b:
  sideRLs tm' (hLR'^^n) (LC a (n+b)) (LC (n*4+a) b).
Proof.
  gen a b.
  induction n; intros.
  1: esx.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHn (4+a) b); flia.
  ut.
  esx.
Qed.

Lemma LOv a r:
  LC (1+a*2) 0 {{{ (hL',L) }}} [0;0] *> r -->*
  LC 3 (2+a) {{{ (hR',R) }}} [0] *> r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_101 a b r:
  LC a b {{{ (hL',L) }}} [1;0;1] *> r -->*
  LC (4+a) b {{{ (hL',L) }}} [1] *> r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_11 a b r:
  LC a b {{{ (hL',L) }}} [1;1] *> r -->*
  LC (4+a) b {{{ (hR',R) }}} r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_10 a b r r':
  sideRLs tm hRL r r' ->
  LC a (1+b) {{{ (hL',L) }}} [1;0] *> r -->*
  LC (4+a) b {{{ (hL',L) }}} [0;0] *> r'.
Proof.
  intros.
  eapply sideRLs_1 in H.
  ut.
  es; er.
  follow100 H.
  er.
Qed.

Lemma init:
  c0 -->*
  LC 3 2 {{{ (hL',L) }}} [0;0;0;1;1] *> 0inf.
Proof.
  esx.
Qed.

Inductive Tp :=
| t0 | t1.

Notation "x ~ 1" := (N.succ_double x) : N_scope.
Notation "x ~ 0" := (N.double x) : N_scope.

Fixpoint rest T r tp: option N :=
match T with
| O => None
| S T =>
match tp with
| t0 =>
  (skip_prefix [0;0;0;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [0;1;1;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>

  (skip_prefix [0;0;1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [0;1;1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>
  
  Some 0%N))))
| t1 =>
  (skip_prefix [1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some s)))) ||| (fun _ =>

  (skip_prefix [0;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [1;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>
  
  Some 0%N)))
end
end.


Fixpoint RIncs T k r tp: option side :=
match T with
| O => None
| S T =>
if (k=?0)%N then Some r else
let k2:=N.div2 k in
match tp with
| t0 =>
  if (k mod 2 =? 0)%N then
    (skip_prefix [0;0;0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;0;0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;1;1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;0;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;0;1;1]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;1;1;1]*>r))))) ||| (fun _ =>

    None))))
  else
    (skip_prefix [0;0;0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;1;1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;0] r &&& (fun r =>
    (RIncs T (k2+1)%N r t0 &&& (fun r =>
    Some ([0;0;0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;0;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;1;1;1]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;1] r &&& (fun r =>
    (RIncs T (k2+1)%N r t1 &&& (fun r =>
    Some ([0;0;1;1]*>r))))) ||| (fun _ =>

    None))))
| t1 =>
  (skip_prefix [1;1] r &&& (fun r =>
  RIncs T k r t1 &&& (fun r =>
  Some ([1;1]*>r)))) ||| (fun _ =>
  if (k mod 2 =? 0)%N then
    (skip_prefix [0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [1;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([1;0]*>r))))) ||| (fun _ =>

    None))
  else
    (skip_prefix [0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [1;0] r &&& (fun r =>
    (RIncs T (k2+1)%N r t0 &&& (fun r =>
    Some ([0;0]*>r))))) ||| (fun _ =>

    None))
  )
end
end.

Definition Tp_eval tp :=
match tp with
| t0 => hRL
| t1 => hRL'
end.

Local Opaque Str_app.

Lemma RIncs_spec T k r tp r':
  RIncs T k r tp = Some r' ->
  sideRLs tm ((Tp_eval tp)^^(N.to_nat k)) r r'.
Proof.
  gen k r tp r'.
  induction T; intros.
  1: inverts H.
  cbn[RIncs] in H.
  destruct (N.eqb_spec k 0).
  1: inverts H; subst; apply sideRLseq_O.
  destruct tp.
  {
    destruct (N.eqb_spec (k mod 2) 0).
    {
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      inverts H.
    }
    {
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      inverts H.
    }
  }
  des_if H.
  {
    inverts H.
    do 2 des_if' E.
    inverts E.
    apply skip_prefix_spec in E0; subst.
    eapply segRLs_sideRLs_concat.
    2: apply IHT,E1.
    apply segRLs_wall''; esc.
  }
  clear E.
  destruct (N.eqb_spec (k mod 2) 0).
  {
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    clear E.
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    inverts H.
  }
  {
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    clear E.
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    inverts H.
  }
Qed.

Local Transparent Str_app.

Inductive Config :=
| cfgL'(a b:N)(r:side)
| cfgR'(a b:N)(r:side).

Definition Config_eval x :=
match x with
| cfgL' a b r => LC (N.to_nat a) (N.to_nat b) {{{ (hL',L) }}} r
| cfgR' a b r => LC (N.to_nat a) (N.to_nat b) {{{ (hR',R) }}} r
end.

Definition maxT: nat := Eval vm_compute in 10000.
Definition maxT': nat := Eval vm_compute in 100000.

Fixpoint mstep x :=
match x with
| cfgR' a b r =>
  sideRLs_c tm hRL' r maxT' &&& (fun r =>
  Some (cfgL' a b r))
| cfgL' a b r =>
  (skip_prefix [1;0;1] r &&& (fun r =>
  Some (cfgL' (4+a) b ([1]*>r)))) ||| (fun _ =>

  (skip_prefix [1;1] r &&& (fun r =>
  Some (cfgR' (4+a) b r))) ||| (fun _ =>

  if (b=?0)%N then
    if (a mod 2 =? 1)%N then
      skip_prefix [0;0] r &&& (fun r =>
      Some (cfgR' 3 (2+a/2) ([0]*>r)))
    else
      None
  else
    rest maxT r t1 &&& (fun k =>
    if (k=?0)%N then
      Some (cfgR' (4+a) (b-1) r)
    else
      Some (N.min k b) &&& (fun k =>
      RIncs maxT k r t1 &&& (fun r =>
      Some (cfgL' (a+k*4) (b-k) r))))
  ))
end.

Local Opaque N.add maxT maxT'.

Lemma mstep_spec x x':
  mstep x = Some x' ->
  Config_eval x -->*
  Config_eval x'.
Proof.
  intros.
  destruct x; cbn[mstep] in H.
  - des_if H.
    { inverts H.
      des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      cbn[Config_eval].
      rewrite Nnat.N2Nat.inj_add.
      apply LRst_101. }
    clear E.
    des_if H.
    { inverts H.
      des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      cbn[Config_eval].
      rewrite Nnat.N2Nat.inj_add.
      apply LRst_11. }
    clear E.
    destruct (N.eqb_spec b 0).
    { subst.
      destruct (N.eqb_spec (a mod 2) 1)%N.
      2: inverts H.
      des_if' H.
      inverts H.
      apply skip_prefix_spec in E; subst.
      cbn[Config_eval].
      applys_eq (LOv (N.to_nat (a/2)) s); flia. }
    { des_if' H.
      cbn[if_Some] in H.
      destruct (N.eqb_spec n0 0).
      { subst.
        inverts H.
        cbn[Config_eval].
        applys_eq (LInc (N.to_nat a) (N.to_nat (b-1))); flia. }
      { des_if' H.
        inverts H.
        apply RIncs_spec in E0.
        cbn[Config_eval].
        eapply sideRLs_concat_1L.
        1: apply E0.
        remember (N.min n0 b) as n'.
        applys_eq (LIncs (N.to_nat n') (N.to_nat a) (N.to_nat (b-n'))); flia. }
    }
  - des_if' H.
    inverts H.
    eapply sideRLs_c_spec in E.
    2: reflexivity.
    eapply sideRLs_1 in E.
    cbn[Config_eval].
    follow100 E; finish.
Qed.

Fixpoint msteps T x :=
match T with
| O => Some x
| S T =>
  (mstep x &&& (fun x =>
  msteps T x)) ||| (fun _ => Some x)
end.

Lemma msteps_spec T x x':
  msteps T x = Some x' ->
  Config_eval x -->*
  Config_eval x'.
Proof.
  gen x.
  induction T; intros.
  - inverts H.
    finish.
  - cbn[msteps] in H.
    des_if' H.
    + inverts H.
      des_if' E.
      apply mstep_spec in E0.
      follow E0.
      auto.
    + finish.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: apply init.
  eapply halts_evstep.
  2: apply (msteps_spec 3000 (cfgL' 3 2 ([0;0;0;1;1]*>0inf))).
  2: time native_compute; reflexivity.
  match goal with
  | |- halts tm (Config_eval (cfgR' ?a ?b ?r)) =>
    generalize a;
    generalize b;
    intros
  end.
  unfold Config_eval,to_DH_config,LC.
  eapply halts_evstep.
  2: stepn' (3125%N).
  apply halted_halts.
  ec.
Time Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0LC---_1LD1LC_0LE0LD_1RE1RF_0RC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[0;0]).
Notation hL := (D,[0;0]).
Notation hR' := (A,<[1;0;1]).
Notation hL' := (D,[0;1;1]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL')].
Notation hLR' := [(hL',hR')].


Definition LC a b := 0inf <* [1]^^a <* <[1;0]^^b.

Definition tm' := flip tm.

Lemma LInc a b r:
  LC a (1+b) {{{ (hL',L) }}} r -->*
  LC (4+a) b {{{ (hR',R) }}} r.
Proof.
  ut.
  esx.
Qed.

Lemma LIncs n a b:
  sideRLs tm' (hLR'^^n) (LC a (n+b)) (LC (n*4+a) b).
Proof.
  gen a b.
  induction n; intros.
  1: esx.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHn (4+a) b); flia.
  ut.
  esx.
Qed.

Lemma LOv a r:
  LC (1+a*2) 0 {{{ (hL',L) }}} [0;0] *> r -->*
  LC 3 (2+a) {{{ (hR',R) }}} [0] *> r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_101 a b r:
  LC a b {{{ (hL',L) }}} [1;0;1] *> r -->*
  LC (4+a) b {{{ (hL',L) }}} [1] *> r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_11 a b r:
  LC a b {{{ (hL',L) }}} [1;1] *> r -->*
  LC (4+a) b {{{ (hR',R) }}} r.
Proof.
  ut.
  es.
Qed.

Lemma LRst_10 a b r r':
  sideRLs tm hRL r r' ->
  LC a (1+b) {{{ (hL',L) }}} [1;0] *> r -->*
  LC (4+a) b {{{ (hL',L) }}} [0;0] *> r'.
Proof.
  intros.
  eapply sideRLs_1 in H.
  ut.
  es; er.
  follow100 H.
  er.
Qed.

Lemma init:
  c0 -->*
  LC 11 5 {{{ (hL',L) }}} [1;0] *> 0inf.
Proof.
  esx.
Qed.

Inductive Tp :=
| t0 | t1.

Notation "x ~ 1" := (N.succ_double x) : N_scope.
Notation "x ~ 0" := (N.double x) : N_scope.

Fixpoint rest T r tp: option N :=
match T with
| O => None
| S T =>
match tp with
| t0 =>
  (skip_prefix [0;0;0;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [0;1;1;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>

  (skip_prefix [0;0;1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [0;1;1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>
  
  Some 0%N))))
| t1 =>
  (skip_prefix [1;1] r &&& (fun r =>
  (rest T r t1 &&& (fun s =>
  Some s)))) ||| (fun _ =>

  (skip_prefix [0;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~1)%N)))) ||| (fun _ =>

  (skip_prefix [1;0] r &&& (fun r =>
  (rest T r t0 &&& (fun s =>
  Some (s~0)%N)))) ||| (fun _ =>
  
  Some 0%N)))
end
end.


Fixpoint RIncs T k r tp: option side :=
match T with
| O => None
| S T =>
if (k=?0)%N then Some r else
let k2:=N.div2 k in
match tp with
| t0 =>
  if (k mod 2 =? 0)%N then
    (skip_prefix [0;0;0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;0;0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;1;1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;0;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;0;1;1]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;1;1;1]*>r))))) ||| (fun _ =>

    None))))
  else
    (skip_prefix [0;0;0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;1;1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;0] r &&& (fun r =>
    (RIncs T (k2+1)%N r t0 &&& (fun r =>
    Some ([0;0;0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [0;0;1;1] r &&& (fun r =>
    (RIncs T (k2)%N r t1 &&& (fun r =>
    Some ([0;1;1;1]*>r))))) ||| (fun _ =>

    (skip_prefix [0;1;1;1] r &&& (fun r =>
    (RIncs T (k2+1)%N r t1 &&& (fun r =>
    Some ([0;0;1;1]*>r))))) ||| (fun _ =>

    None))))
| t1 =>
  (skip_prefix [1;1] r &&& (fun r =>
  RIncs T k r t1 &&& (fun r =>
  Some ([1;1]*>r)))) ||| (fun _ =>
  if (k mod 2 =? 0)%N then
    (skip_prefix [0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([0;0]*>r))))) ||| (fun _ =>

    (skip_prefix [1;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([1;0]*>r))))) ||| (fun _ =>

    None))
  else
    (skip_prefix [0;0] r &&& (fun r =>
    (RIncs T (k2)%N r t0 &&& (fun r =>
    Some ([1;0]*>r))))) ||| (fun _ =>

    (skip_prefix [1;0] r &&& (fun r =>
    (RIncs T (k2+1)%N r t0 &&& (fun r =>
    Some ([0;0]*>r))))) ||| (fun _ =>

    None))
  )
end
end.

Definition Tp_eval tp :=
match tp with
| t0 => hRL
| t1 => hRL'
end.

Local Opaque Str_app.

Lemma RIncs_spec T k r tp r':
  RIncs T k r tp = Some r' ->
  sideRLs tm ((Tp_eval tp)^^(N.to_nat k)) r r'.
Proof.
  gen k r tp r'.
  induction T; intros.
  1: inverts H.
  cbn[RIncs] in H.
  destruct (N.eqb_spec k 0).
  1: inverts H; subst; apply sideRLseq_O.
  destruct tp.
  {
    destruct (N.eqb_spec (k mod 2) 0).
    {
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      inverts H.
    }
    {
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      clear E.
      des_if H.
      {
        inverts H.
        do 2 des_if' E.
        inverts E.
        apply skip_prefix_spec in E0; subst.
        eapply segRLs_sideRLs_concat.
        2: apply IHT,E1.
        applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
        1,2: apply feq; [reflexivity|lia].
        1,2: esc.
      }
      inverts H.
    }
  }
  des_if H.
  {
    inverts H.
    do 2 des_if' E.
    inverts E.
    apply skip_prefix_spec in E0; subst.
    eapply segRLs_sideRLs_concat.
    2: apply IHT,E1.
    apply segRLs_wall''; esc.
  }
  clear E.
  destruct (N.eqb_spec (k mod 2) 0).
  {
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    clear E.
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 0 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    inverts H.
  }
  {
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 0).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    clear E.
    des_if H.
    {
      inverts H.
      do 2 des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      eapply segRLs_sideRLs_concat.
      2: apply IHT,E1.
      applys_eq (segRLs_addmul_v3 2 1 (N.to_nat (k/2)) 1 1).
      1,2: apply feq; [reflexivity|lia].
      1,2: esc.
    }
    inverts H.
  }
Qed.

Local Transparent Str_app.

Inductive Config :=
| cfgL'(a b:N)(r:side)
| cfgR'(a b:N)(r:side).

Definition Config_eval x :=
match x with
| cfgL' a b r => LC (N.to_nat a) (N.to_nat b) {{{ (hL',L) }}} r
| cfgR' a b r => LC (N.to_nat a) (N.to_nat b) {{{ (hR',R) }}} r
end.

Definition maxT: nat := Eval vm_compute in 10000.
Definition maxT': nat := 100000.

Fixpoint mstep x :=
match x with
| cfgR' a b r =>
  sideRLs_c tm hRL' r maxT' &&& (fun r =>
  Some (cfgL' a b r))
| cfgL' a b r =>
  (skip_prefix [1;0;1] r &&& (fun r =>
  Some (cfgL' (4+a) b ([1]*>r)))) ||| (fun _ =>

  (skip_prefix [1;1] r &&& (fun r =>
  Some (cfgR' (4+a) b r))) ||| (fun _ =>

  if (b=?0)%N then
    if (a mod 2 =? 1)%N then
      skip_prefix [0;0] r &&& (fun r =>
      Some (cfgR' 3 (2+a/2) ([0]*>r)))
    else
      None
  else
    rest maxT r t1 &&& (fun k =>
    if (k=?0)%N then
      Some (cfgR' (4+a) (b-1) r)
    else
      Some (N.min k b) &&& (fun k =>
      RIncs maxT k r t1 &&& (fun r =>
      Some (cfgL' (a+k*4) (b-k) r))))
  ))
end.

Local Opaque N.add maxT maxT'.

Lemma mstep_spec x x':
  mstep x = Some x' ->
  Config_eval x -->*
  Config_eval x'.
Proof.
  intros.
  destruct x; cbn[mstep] in H.
  - des_if H.
    { inverts H.
      des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      cbn[Config_eval].
      rewrite Nnat.N2Nat.inj_add.
      apply LRst_101. }
    clear E.
    des_if H.
    { inverts H.
      des_if' E.
      inverts E.
      apply skip_prefix_spec in E0; subst.
      cbn[Config_eval].
      rewrite Nnat.N2Nat.inj_add.
      apply LRst_11. }
    clear E.
    destruct (N.eqb_spec b 0).
    { subst.
      destruct (N.eqb_spec (a mod 2) 1)%N.
      2: inverts H.
      des_if' H.
      inverts H.
      apply skip_prefix_spec in E; subst.
      cbn[Config_eval].
      applys_eq (LOv (N.to_nat (a/2)) s); flia. }
    { des_if' H.
      cbn[if_Some] in H.
      destruct (N.eqb_spec n0 0).
      { subst.
        inverts H.
        cbn[Config_eval].
        applys_eq (LInc (N.to_nat a) (N.to_nat (b-1))); flia. }
      { des_if' H.
        inverts H.
        apply RIncs_spec in E0.
        cbn[Config_eval].
        eapply sideRLs_concat_1L.
        1: apply E0.
        remember (N.min n0 b) as n'.
        applys_eq (LIncs (N.to_nat n') (N.to_nat a) (N.to_nat (b-n'))); flia. }
    }
  - des_if' H.
    inverts H.
    eapply sideRLs_c_spec in E.
    2: reflexivity.
    eapply sideRLs_1 in E.
    cbn[Config_eval].
    follow100 E; finish.
Qed.

Fixpoint msteps T x :=
match T with
| O => Some x
| S T =>
  (mstep x &&& (fun x =>
  msteps T x)) ||| (fun _ => Some x)
end.

Lemma msteps_spec T x x':
  msteps T x = Some x' ->
  Config_eval x -->*
  Config_eval x'.
Proof.
  gen x.
  induction T; intros.
  - inverts H.
    finish.
  - cbn[msteps] in H.
    des_if' H.
    + inverts H.
      des_if' E.
      apply mstep_spec in E0.
      follow E0.
      auto.
    + finish.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: apply init.
  eapply halts_evstep.
  2: apply (msteps_spec 15000 (cfgL' 11 5 ([1;0]*>0inf))).
  2: time native_compute; reflexivity.
  match goal with
  | |- halts tm (Config_eval (cfgR' ?a ?b ?r)) =>
    generalize a;
    generalize b;
    intros
  end.
  unfold Config_eval,to_DH_config,LC.
  eapply halts_evstep.
  2: stepn' (13297%N).
  apply halted_halts.
  ec.
Time Qed.

End TM2.


