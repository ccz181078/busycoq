From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import List.
Require Import String.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import ES_v3.
From BusyCoq Require Import DivModCases.

Open Scope list.


Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0LD_---1LD_0RE1RD_1RA1RB_1LA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation h0 := [((E,[0]),(A,[]))].
Notation h1 := [((C,[1]),(F,[]))].
Notation hR := (D,[1]).
Notation hL := (F,[]).
Notation h2 := [(hR,hL)].
Notation h2' := [(hL,hR)].

Definition LC n := 0inf <* [1]^^n.

Lemma LIncs k n:
  sideRLs tm' (h2'^^k) (LC n) (LC (k*2+n)).
Proof.
  ut.
  sideRLs_ind k.
Qed.

Inductive M3 := p0|p1|p2.

Definition m3 n p :=
if Nat.even n then
match p with
| p0 => p1
| p1 => p2
| p2 => p0
end
else
match p with
| p0 => p2
| p1 => p0
| p2 => p1
end.

Fixpoint w3 n p :=
match n with
| O =>
  match p with
  | p0 => [1;0]
  | p1 => [1;0]
  | p2 => [1;1]
  end
| S n =>
  w3 n p ++ w3 n (m3 n p)
end.

Fixpoint w1 n :=
match n with
| O => [1;1]
| S n => w1 n ++ w1 n
end.

Fixpoint h3 n p: list (DH0*DH0) :=
match n with
| O =>
  match p with
  | p0 => h0
  | p1 => h0
  | p2 => h1
  end
| S n =>
  h3 n p ++ h3 n (m3 n p)
end.

Fixpoint h2s n: list (DH0*DH0) :=
match n with
| O => h2
| S n => h2s n ++ h2s n
end.

Fixpoint w3' n p :=
match n with
| O =>
  match p with
  | p0 => [0]
  | p1 => [0]
  | p2 => [1]
  end
| S n =>
  w3' n p ++ w3 n (m3 n p)
end.

Fixpoint eo n (a b:M3) :=
match n with
| O => a
| S n => eo n b a
end.

Lemma eo_spec n a b:
  eo n a b = if Nat.even n then a else b.
Proof.
  gen a b.
  induction n; intros.
  1: reflexivity.
  cbn[eo].
  rewrite IHn.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  destruct (Nat.even n); trivial.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (P0: segRLs tm
    (h3 n (eo n p1 p2))
    (h3 n (eo n p2 p1))
    (w3 n (eo n p1 p2))
    (w3 n (eo n p2 p1)))
  (P1: segRLs tm
    (h3 n (eo n p2 p1))
    (h2s n)
    (w3 n (eo n p2 p1))
    (w1 n))
  (P2: segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3 n p0)
    (w3 n p0))
  (P2': segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3' n p0)
    (w3' n p0))
  (P3: segRLs tm
    (h3 n p0)
    (h3 n p0)
    (w1 n)
    (w3 n (eo n p1 p2)))
  (P4: segRLs tm
    (h3 n p0) (h3 n (eo n p2 p1))
    (w3 n p0) (w3 n (eo n p2 p1)))
  (P6: segRLs tm
    (h3 n p2) (h3 n (eo n p1 p0))
    (w3 n p1) (w3 n (eo n p0 p2)))
  (P7: segRLs tm
    (h3 n p1) (h3 n (eo n p0 p2))
    (w3 n p2) (w3 n (eo n p1 p0)))
  (P5: segRLs tm
    (h2s n) (h2s n)
    (w1 n) (w1 n))
    :
  P n.

Ltac ec := econstructor.

Ltac stc :=
  eapply segRLs_trans;
  eapply segRLs_concat.

Ltac eo_cases n :=
  repeat rewrite eo_spec in *;
  unfold m3 in *;
  destruct (Nat.even n).

Lemma P_n n:
  P n.
Proof.
  induction n.
  {
    ec.
    all: esc.
  }
  inverts IHn.
  ec; cbn.
  all: eo_cases n; stc; eauto 1.
Qed.

Ltac use_shift_rule ::= use_shift_rule'.

Definition RC0 n :=
  ([0;1;0;1;1] *> [1;0;1;0;1;1]^^(1+n*2) *> 0inf).

Definition RC1 m n :=
  ([1;0;1;0;1;1]^^m *> [0;1;0;1;0;1; 1;1;1;1;1] *> [1; 0;1;0;1;0;1; 1;1;1;1;1]^^n *> [0;1;0;1;1] *> 0inf).

Ltac es_v3_pre ::= ut.

Lemma RIncs0 n m:
  sideRLs tm (h2^^2++(h0++h0++h1)^^(m*4)) (RC0 (m+n)) (RC1 (m*4) n).
Proof.
  eapply @sideRLs_trans with (r2:=RC1 0 (m+n)).
  1: es' m n.
  rewrite lpow_mul.
  gen n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHm (S n)); flia.
  es' m n.
Qed.

Definition RC2 n :=
  [1;0;1;0;1;1]^^n *> 0inf.

Lemma RIncs1 m n:
  sideRLs tm ((h0++h0++h1)^^(5+m)) (RC1 n 0) (RC2 (5+m+n)).
Proof.
  eapply sideRLs_trans_add with (w3:=RC2 (5+n)).
  1: es' n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: apply IHm.
  es' m n.
Qed.

Lemma P2''_n_0 n:
  segRLs tm
  (h2s (S (S n)))
  (((h2s n)++(h3 n p0))++((h3 n (eo n p1 p2))++(h3 n (eo n p2 p1))))
  (w3' (S n) p0++(w3 n (eo n p2 p1)))
  (w3' (S n) p0++(w3 n (eo n p2 p1))).
Proof.
  remember (S n) as n'.
  cbn.
  eapply segRLs_concat.
  - epose proof (P_n n') as HP; inverts HP.
    eapply segRLs_trans; eauto 1.
  - subst n'.
    cbn.
    epose proof (P_n n) as HP; inverts HP.
    eo_cases n;
    eapply segRLs_trans; eapply segRLs_trans; eauto 1.
Qed.

Fixpoint s3 {A} n (v0 v1 v2:list A) :=
match n with
| O => []
| S n => v0 ++ s3 n v1 v2 v0
end.

Lemma h2s_spec n:
  h2s n = h2^^(2^n).
Proof.
  induction n; cbn; trivial.
  rewrite Nat.add_0_r,lpow_add,IHn; trivial.
Qed.

Lemma s3_add {A} a b (v0 v1 v2:list A):
  s3 (a+b) v0 v1 v2 =
  match mod3 a with
  | mod3eq0 _ => s3 a v0 v1 v2 ++ s3 b v0 v1 v2
  | mod3eq1 _ => s3 a v0 v1 v2 ++ s3 b v1 v2 v0
  | mod3eq2 _ => s3 a v0 v1 v2 ++ s3 b v2 v0 v1
  end.
Proof.
  gen v0 v1 v2 b.
  induction a; intros; cbn; trivial.
  rewrite IHa.
  destruct (mod3 a); destruct (mod3 (S a)); solve[lia | rewrite <-app_assoc; trivial].
Qed.

Lemma pow2mod3 n:
  2^n mod 3 =
  if Nat.even n then 1%nat else 2.
Proof.
  induction n; trivial.
  cbn[Nat.pow].
  rewrite Nat.even_succ.
  unfold Nat.odd.
  eo_cases n; cbn[negb]; lia.
Qed.

Lemma h3_spec n p:
  h3 n p =
  match p with
  | p0 => s3 (2^n) h0 h0 h1
  | p1 => s3 (2^n) h0 h1 h0
  | p2 => s3 (2^n) h1 h0 h0
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow h3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3_spec n p:
  w3 n p =
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3'_spec n p:
  w3' n p =
  tl (
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end).
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3'].
    replace (2*2^n) with (2^n+2^n) by lia.
    rewrite w3_spec.
    repeat rewrite s3_add.
    rewrite IHn.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.

Lemma s3_spec {A} n (v0 v1 v2:list A):
  s3 (n*3) v0 v1 v2 = (v0++v1++v2)^^n.
Proof.
  induction n; cbn; trivial.
  rewrite IHn.
  repeat rewrite app_assoc; trivial.
Qed.

Lemma tl_lpow {A} (ls:list A) n:
  ls<>[] ->
  n<>O ->
  tl (ls^^n) = tl ls ++ (ls^^(n-1)).
Proof.
  intros.
  destruct n; [lia|].
  destruct ls; [congruence|].
  cbn; flia.
Qed.

Lemma P2''_n n:
  segRLs tm
  (h2^^(2^n*4))
  ((h2^^(2^n))++(h0++h0++h1)^^(2^n))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1)))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1))).
Proof.
  rewrite <-(tl_lpow ([1;0]++[1;0]++[1;1])); [|cbn; congruence|lia].
  do 2 rewrite <-s3_spec.
  replace (2^n*3) with (2^n+(2^n+2^n)) by lia.
  repeat rewrite s3_add.
  applys_eq (P2''_n_0 n);
  cbn[w3'];
  repeat rewrite h2s_spec;
  repeat rewrite <-app_assoc;
  repeat rewrite h3_spec;
  repeat rewrite w3_spec;
  repeat rewrite w3'_spec.
  - cbn[Nat.pow]; flia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); trivial; lia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.


Lemma Pa_n n:
  sideRLs tm (h2^^(2^n*8-2)) 0inf (RC0 (2^n-1)).
Proof.
  induction n using lt_wf_ind.
  (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*2^n*8-2) with ((2^n*8-2)+2^n*8) by lia.
  eapply sideRLs_trans_add.
  1: apply (H n); lia.
  unfold RC0.
  epose proof (P2''_n (S n)) as P2''.
  cbn[Nat.pow] in P2''.
  replace (1+(2*2^n-1)*2) with (2*2^n-1+2*2^n) by lia.
  rewrite (lpow_add _ _ (2*2^n)),Str_app_assoc.
  do 2 rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: applys_eq P2''; flia.
  do 2 (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*(2*(2*2^n))) with ((2^n*8-2+2)) by lia.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  1: apply (H n); lia.
  rewrite Nat.sub_add by lia.
  replace (2^n*8) with ((2^n-1)*4+(2^n*4+4)) by lia.
  rewrite lpow_add,app_assoc.
  replace ((2^n-1)*4+(2^n*4+4)) with (2^n*8) by lia.
  eapply sideRLs_trans.
  1: applys_eq (RIncs0 0 (2^n-1)); flia.
  applys_eq (RIncs1 (2^n*4-1) (2^n*4-4)); unfold RC2; flia.
Qed.

Lemma BigStep m n:
  LC m {{{ (hR,R) }}} 0inf -->*
  LC ((2^n*8-2)*2+m) {{{ (hR,R) }}} RC0 (2^n-1).
Proof.
  eapply sideRLs_concat_1.
  1: apply Pa_n.
  apply LIncs.
Qed.

Lemma pow2_lt n:
  n<2^n.
Proof.
  induction n; cbn[Nat.pow]; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_; split.
  - eapply evstep_trans.
    2: apply (BigStep 1 n).
    esx.
  - split.
    + unfold LC,RC0,to_DH_config.
      solve_sigma_score.
    + pose proof (pow2_lt n).
      lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB1LA_1LC0LA_1RD0LE_---1RE_0RF1RE_1RB1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation h0 := [((F,[0]),(B,[]))].
Notation h1 := [((D,[1]),(A,[]))].
Notation hR := (E,[1]).
Notation hL := (A,[]).
Notation h2 := [(hR,hL)].
Notation h2' := [(hL,hR)].

Definition LC n := 0inf <* [1]^^n.

Lemma LIncs k n:
  sideRLs tm' (h2'^^k) (LC n) (LC (k*2+n)).
Proof.
  ut.
  sideRLs_ind k.
Qed.

Inductive M3 := p0|p1|p2.

Definition m3 n p :=
if Nat.even n then
match p with
| p0 => p1
| p1 => p2
| p2 => p0
end
else
match p with
| p0 => p2
| p1 => p0
| p2 => p1
end.

Fixpoint w3 n p :=
match n with
| O =>
  match p with
  | p0 => [1;0]
  | p1 => [1;0]
  | p2 => [1;1]
  end
| S n =>
  w3 n p ++ w3 n (m3 n p)
end.

Fixpoint w1 n :=
match n with
| O => [1;1]
| S n => w1 n ++ w1 n
end.

Fixpoint h3 n p: list (DH0*DH0) :=
match n with
| O =>
  match p with
  | p0 => h0
  | p1 => h0
  | p2 => h1
  end
| S n =>
  h3 n p ++ h3 n (m3 n p)
end.

Fixpoint h2s n: list (DH0*DH0) :=
match n with
| O => h2
| S n => h2s n ++ h2s n
end.

Fixpoint w3' n p :=
match n with
| O =>
  match p with
  | p0 => [0]
  | p1 => [0]
  | p2 => [1]
  end
| S n =>
  w3' n p ++ w3 n (m3 n p)
end.

Fixpoint eo n (a b:M3) :=
match n with
| O => a
| S n => eo n b a
end.

Lemma eo_spec n a b:
  eo n a b = if Nat.even n then a else b.
Proof.
  gen a b.
  induction n; intros.
  1: reflexivity.
  cbn[eo].
  rewrite IHn.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  destruct (Nat.even n); trivial.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (P0: segRLs tm
    (h3 n (eo n p1 p2))
    (h3 n (eo n p2 p1))
    (w3 n (eo n p1 p2))
    (w3 n (eo n p2 p1)))
  (P1: segRLs tm
    (h3 n (eo n p2 p1))
    (h2s n)
    (w3 n (eo n p2 p1))
    (w1 n))
  (P2: segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3 n p0)
    (w3 n p0))
  (P2': segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3' n p0)
    (w3' n p0))
  (P3: segRLs tm
    (h3 n p0)
    (h3 n p0)
    (w1 n)
    (w3 n (eo n p1 p2)))
  (P4: segRLs tm
    (h3 n p0) (h3 n (eo n p2 p1))
    (w3 n p0) (w3 n (eo n p2 p1)))
  (P6: segRLs tm
    (h3 n p2) (h3 n (eo n p1 p0))
    (w3 n p1) (w3 n (eo n p0 p2)))
  (P7: segRLs tm
    (h3 n p1) (h3 n (eo n p0 p2))
    (w3 n p2) (w3 n (eo n p1 p0)))
  (P5: segRLs tm
    (h2s n) (h2s n)
    (w1 n) (w1 n))
    :
  P n.

Ltac ec := econstructor.

Ltac stc :=
  eapply segRLs_trans;
  eapply segRLs_concat.

Ltac eo_cases n :=
  repeat rewrite eo_spec in *;
  unfold m3 in *;
  destruct (Nat.even n).

Lemma P_n n:
  P n.
Proof.
  induction n.
  {
    ec.
    all: esc.
  }
  inverts IHn.
  ec; cbn.
  all: eo_cases n; stc; eauto 1.
Qed.

Ltac use_shift_rule ::= use_shift_rule'.

Definition RC0 n :=
  ([0;1;0;1;1] *> [1;0;1;0;1;1]^^(1+n*2) *> 0inf).

Definition RC1 m n :=
  ([1;0;1;0;1;1]^^m *> [0;1;0;1;0;1; 1;1;1;1;1] *> [1; 0;1;0;1;0;1; 1;1;1;1;1]^^n *> [0;1;0;1;1] *> 0inf).

Ltac es_v3_pre ::= ut.

Lemma RIncs0 n m:
  sideRLs tm (h2^^2++(h0++h0++h1)^^(m*4)) (RC0 (m+n)) (RC1 (m*4) n).
Proof.
  eapply @sideRLs_trans with (r2:=RC1 0 (m+n)).
  1: es' m n.
  rewrite lpow_mul.
  gen n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHm (S n)); flia.
  es' m n.
Qed.

Definition RC2 n :=
  [1;0;1;0;1;1]^^n *> 0inf.

Lemma RIncs1 m n:
  sideRLs tm ((h0++h0++h1)^^(5+m)) (RC1 n 0) (RC2 (5+m+n)).
Proof.
  eapply sideRLs_trans_add with (w3:=RC2 (5+n)).
  1: es' n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: apply IHm.
  es' m n.
Qed.

Lemma P2''_n_0 n:
  segRLs tm
  (h2s (S (S n)))
  (((h2s n)++(h3 n p0))++((h3 n (eo n p1 p2))++(h3 n (eo n p2 p1))))
  (w3' (S n) p0++(w3 n (eo n p2 p1)))
  (w3' (S n) p0++(w3 n (eo n p2 p1))).
Proof.
  remember (S n) as n'.
  cbn.
  eapply segRLs_concat.
  - epose proof (P_n n') as HP; inverts HP.
    eapply segRLs_trans; eauto 1.
  - subst n'.
    cbn.
    epose proof (P_n n) as HP; inverts HP.
    eo_cases n;
    eapply segRLs_trans; eapply segRLs_trans; eauto 1.
Qed.

Fixpoint s3 {A} n (v0 v1 v2:list A) :=
match n with
| O => []
| S n => v0 ++ s3 n v1 v2 v0
end.

Lemma h2s_spec n:
  h2s n = h2^^(2^n).
Proof.
  induction n; cbn; trivial.
  rewrite Nat.add_0_r,lpow_add,IHn; trivial.
Qed.

Lemma s3_add {A} a b (v0 v1 v2:list A):
  s3 (a+b) v0 v1 v2 =
  match mod3 a with
  | mod3eq0 _ => s3 a v0 v1 v2 ++ s3 b v0 v1 v2
  | mod3eq1 _ => s3 a v0 v1 v2 ++ s3 b v1 v2 v0
  | mod3eq2 _ => s3 a v0 v1 v2 ++ s3 b v2 v0 v1
  end.
Proof.
  gen v0 v1 v2 b.
  induction a; intros; cbn; trivial.
  rewrite IHa.
  destruct (mod3 a); destruct (mod3 (S a)); solve[lia | rewrite <-app_assoc; trivial].
Qed.

Lemma pow2mod3 n:
  2^n mod 3 =
  if Nat.even n then 1%nat else 2.
Proof.
  induction n; trivial.
  cbn[Nat.pow].
  rewrite Nat.even_succ.
  unfold Nat.odd.
  eo_cases n; cbn[negb]; lia.
Qed.

Lemma h3_spec n p:
  h3 n p =
  match p with
  | p0 => s3 (2^n) h0 h0 h1
  | p1 => s3 (2^n) h0 h1 h0
  | p2 => s3 (2^n) h1 h0 h0
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow h3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3_spec n p:
  w3 n p =
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3'_spec n p:
  w3' n p =
  tl (
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end).
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3'].
    replace (2*2^n) with (2^n+2^n) by lia.
    rewrite w3_spec.
    repeat rewrite s3_add.
    rewrite IHn.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.

Lemma s3_spec {A} n (v0 v1 v2:list A):
  s3 (n*3) v0 v1 v2 = (v0++v1++v2)^^n.
Proof.
  induction n; cbn; trivial.
  rewrite IHn.
  repeat rewrite app_assoc; trivial.
Qed.

Lemma tl_lpow {A} (ls:list A) n:
  ls<>[] ->
  n<>O ->
  tl (ls^^n) = tl ls ++ (ls^^(n-1)).
Proof.
  intros.
  destruct n; [lia|].
  destruct ls; [congruence|].
  cbn; flia.
Qed.

Lemma P2''_n n:
  segRLs tm
  (h2^^(2^n*4))
  ((h2^^(2^n))++(h0++h0++h1)^^(2^n))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1)))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1))).
Proof.
  rewrite <-(tl_lpow ([1;0]++[1;0]++[1;1])); [|cbn; congruence|lia].
  do 2 rewrite <-s3_spec.
  replace (2^n*3) with (2^n+(2^n+2^n)) by lia.
  repeat rewrite s3_add.
  applys_eq (P2''_n_0 n);
  cbn[w3'];
  repeat rewrite h2s_spec;
  repeat rewrite <-app_assoc;
  repeat rewrite h3_spec;
  repeat rewrite w3_spec;
  repeat rewrite w3'_spec.
  - cbn[Nat.pow]; flia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); trivial; lia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.


Lemma Pa_n n:
  sideRLs tm (h2^^(2^n*8-2)) 0inf (RC0 (2^n-1)).
Proof.
  induction n using lt_wf_ind.
  (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*2^n*8-2) with ((2^n*8-2)+2^n*8) by lia.
  eapply sideRLs_trans_add.
  1: apply (H n); lia.
  unfold RC0.
  epose proof (P2''_n (S n)) as P2''.
  cbn[Nat.pow] in P2''.
  replace (1+(2*2^n-1)*2) with (2*2^n-1+2*2^n) by lia.
  rewrite (lpow_add _ _ (2*2^n)),Str_app_assoc.
  do 2 rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: applys_eq P2''; flia.
  do 2 (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*(2*(2*2^n))) with ((2^n*8-2+2)) by lia.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  1: apply (H n); lia.
  rewrite Nat.sub_add by lia.
  replace (2^n*8) with ((2^n-1)*4+(2^n*4+4)) by lia.
  rewrite lpow_add,app_assoc.
  replace ((2^n-1)*4+(2^n*4+4)) with (2^n*8) by lia.
  eapply sideRLs_trans.
  1: applys_eq (RIncs0 0 (2^n-1)); flia.
  applys_eq (RIncs1 (2^n*4-1) (2^n*4-4)); unfold RC2; flia.
Qed.

Lemma BigStep m n:
  LC m {{{ (hR,R) }}} 0inf -->*
  LC ((2^n*8-2)*2+m) {{{ (hR,R) }}} RC0 (2^n-1).
Proof.
  eapply sideRLs_concat_1.
  1: apply Pa_n.
  apply LIncs.
Qed.

Lemma pow2_lt n:
  n<2^n.
Proof.
  induction n; cbn[Nat.pow]; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_; split.
  - eapply evstep_trans.
    2: apply (BigStep 2 n).
    esx.
  - split.
    + unfold LC,RC0,to_DH_config.
      solve_sigma_score.
    + pose proof (pow2_lt n).
      lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0LE_1RF0LD_0RA1RD_1LB1LE_---1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation h0 := [((A,[0]),(B,[]))].
Notation h1 := [((F,[1]),(E,[]))].
Notation hR := (D,[1]).
Notation hL := (E,[]).
Notation h2 := [(hR,hL)].
Notation h2' := [(hL,hR)].

Definition LC n := 0inf <* [1]^^n.

Lemma LIncs k n:
  sideRLs tm' (h2'^^k) (LC n) (LC (k*2+n)).
Proof.
  ut.
  sideRLs_ind k.
Qed.

Inductive M3 := p0|p1|p2.

Definition m3 n p :=
if Nat.even n then
match p with
| p0 => p1
| p1 => p2
| p2 => p0
end
else
match p with
| p0 => p2
| p1 => p0
| p2 => p1
end.

Fixpoint w3 n p :=
match n with
| O =>
  match p with
  | p0 => [1;0]
  | p1 => [1;0]
  | p2 => [1;1]
  end
| S n =>
  w3 n p ++ w3 n (m3 n p)
end.

Fixpoint w1 n :=
match n with
| O => [1;1]
| S n => w1 n ++ w1 n
end.

Fixpoint h3 n p: list (DH0*DH0) :=
match n with
| O =>
  match p with
  | p0 => h0
  | p1 => h0
  | p2 => h1
  end
| S n =>
  h3 n p ++ h3 n (m3 n p)
end.

Fixpoint h2s n: list (DH0*DH0) :=
match n with
| O => h2
| S n => h2s n ++ h2s n
end.

Fixpoint w3' n p :=
match n with
| O =>
  match p with
  | p0 => [0]
  | p1 => [0]
  | p2 => [1]
  end
| S n =>
  w3' n p ++ w3 n (m3 n p)
end.

Fixpoint eo n (a b:M3) :=
match n with
| O => a
| S n => eo n b a
end.

Lemma eo_spec n a b:
  eo n a b = if Nat.even n then a else b.
Proof.
  gen a b.
  induction n; intros.
  1: reflexivity.
  cbn[eo].
  rewrite IHn.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  destruct (Nat.even n); trivial.
Qed.

Inductive P: nat->Prop :=
| P_intro n
  (P0: segRLs tm
    (h3 n (eo n p1 p2))
    (h3 n (eo n p2 p1))
    (w3 n (eo n p1 p2))
    (w3 n (eo n p2 p1)))
  (P1: segRLs tm
    (h3 n (eo n p2 p1))
    (h2s n)
    (w3 n (eo n p2 p1))
    (w1 n))
  (P2: segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3 n p0)
    (w3 n p0))
  (P2': segRLs tm
    (h2s n)
    (h3 n (eo n p1 p2))
    (w3' n p0)
    (w3' n p0))
  (P3: segRLs tm
    (h3 n p0)
    (h3 n p0)
    (w1 n)
    (w3 n (eo n p1 p2)))
  (P4: segRLs tm
    (h3 n p0) (h3 n (eo n p2 p1))
    (w3 n p0) (w3 n (eo n p2 p1)))
  (P6: segRLs tm
    (h3 n p2) (h3 n (eo n p1 p0))
    (w3 n p1) (w3 n (eo n p0 p2)))
  (P7: segRLs tm
    (h3 n p1) (h3 n (eo n p0 p2))
    (w3 n p2) (w3 n (eo n p1 p0)))
  (P5: segRLs tm
    (h2s n) (h2s n)
    (w1 n) (w1 n))
    :
  P n.

Ltac ec := econstructor.

Ltac stc :=
  eapply segRLs_trans;
  eapply segRLs_concat.

Ltac eo_cases n :=
  repeat rewrite eo_spec in *;
  unfold m3 in *;
  destruct (Nat.even n).

Lemma P_n n:
  P n.
Proof.
  induction n.
  {
    ec.
    all: esc.
  }
  inverts IHn.
  ec; cbn.
  all: eo_cases n; stc; eauto 1.
Qed.

Ltac use_shift_rule ::= use_shift_rule'.

Definition RC0 n :=
  ([0;1;0;1;1] *> [1;0;1;0;1;1]^^(1+n*2) *> 0inf).

Definition RC1 m n :=
  ([1;0;1;0;1;1]^^m *> [0;1;0;1;0;1; 1;1;1;1;1] *> [1; 0;1;0;1;0;1; 1;1;1;1;1]^^n *> [0;1;0;1;1] *> 0inf).

Ltac es_v3_pre ::= ut.

Lemma RIncs0 n m:
  sideRLs tm (h2^^2++(h0++h0++h1)^^(m*4)) (RC0 (m+n)) (RC1 (m*4) n).
Proof.
  eapply @sideRLs_trans with (r2:=RC1 0 (m+n)).
  1: es' m n.
  rewrite lpow_mul.
  gen n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHm (S n)); flia.
  es' m n.
Qed.

Definition RC2 n :=
  [1;0;1;0;1;1]^^n *> 0inf.

Lemma RIncs1 m n:
  sideRLs tm ((h0++h0++h1)^^(5+m)) (RC1 n 0) (RC2 (5+m+n)).
Proof.
  eapply sideRLs_trans_add with (w3:=RC2 (5+n)).
  1: es' n.
  induction m; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: apply IHm.
  es' m n.
Qed.

Lemma P2''_n_0 n:
  segRLs tm
  (h2s (S (S n)))
  (((h2s n)++(h3 n p0))++((h3 n (eo n p1 p2))++(h3 n (eo n p2 p1))))
  (w3' (S n) p0++(w3 n (eo n p2 p1)))
  (w3' (S n) p0++(w3 n (eo n p2 p1))).
Proof.
  remember (S n) as n'.
  cbn.
  eapply segRLs_concat.
  - epose proof (P_n n') as HP; inverts HP.
    eapply segRLs_trans; eauto 1.
  - subst n'.
    cbn.
    epose proof (P_n n) as HP; inverts HP.
    eo_cases n;
    eapply segRLs_trans; eapply segRLs_trans; eauto 1.
Qed.

Fixpoint s3 {A} n (v0 v1 v2:list A) :=
match n with
| O => []
| S n => v0 ++ s3 n v1 v2 v0
end.

Lemma h2s_spec n:
  h2s n = h2^^(2^n).
Proof.
  induction n; cbn; trivial.
  rewrite Nat.add_0_r,lpow_add,IHn; trivial.
Qed.

Lemma s3_add {A} a b (v0 v1 v2:list A):
  s3 (a+b) v0 v1 v2 =
  match mod3 a with
  | mod3eq0 _ => s3 a v0 v1 v2 ++ s3 b v0 v1 v2
  | mod3eq1 _ => s3 a v0 v1 v2 ++ s3 b v1 v2 v0
  | mod3eq2 _ => s3 a v0 v1 v2 ++ s3 b v2 v0 v1
  end.
Proof.
  gen v0 v1 v2 b.
  induction a; intros; cbn; trivial.
  rewrite IHa.
  destruct (mod3 a); destruct (mod3 (S a)); solve[lia | rewrite <-app_assoc; trivial].
Qed.

Lemma pow2mod3 n:
  2^n mod 3 =
  if Nat.even n then 1%nat else 2.
Proof.
  induction n; trivial.
  cbn[Nat.pow].
  rewrite Nat.even_succ.
  unfold Nat.odd.
  eo_cases n; cbn[negb]; lia.
Qed.

Lemma h3_spec n p:
  h3 n p =
  match p with
  | p0 => s3 (2^n) h0 h0 h1
  | p1 => s3 (2^n) h0 h1 h0
  | p2 => s3 (2^n) h1 h0 h0
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow h3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3_spec n p:
  w3 n p =
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end.
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3].
    replace (2*2^n) with (2^n+2^n) by lia.
    do 2 rewrite IHn.
    repeat rewrite s3_add.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); solve[lia|trivial].
Qed.

Lemma w3'_spec n p:
  w3' n p =
  tl (
  match p with
  | p0 => s3 (2^n) [1;0] [1;0] [1;1]
  | p1 => s3 (2^n) [1;0] [1;1] [1;0]
  | p2 => s3 (2^n) [1;1] [1;0] [1;0]
  end).
Proof.
  gen p.
  induction n; intros.
  - destruct p; trivial.
  - cbn[Nat.pow w3'].
    replace (2*2^n) with (2^n+2^n) by lia.
    rewrite w3_spec.
    repeat rewrite s3_add.
    rewrite IHn.
    pose proof (pow2mod3 n).
    unfold m3;
    destruct p;
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.

Lemma s3_spec {A} n (v0 v1 v2:list A):
  s3 (n*3) v0 v1 v2 = (v0++v1++v2)^^n.
Proof.
  induction n; cbn; trivial.
  rewrite IHn.
  repeat rewrite app_assoc; trivial.
Qed.

Lemma tl_lpow {A} (ls:list A) n:
  ls<>[] ->
  n<>O ->
  tl (ls^^n) = tl ls ++ (ls^^(n-1)).
Proof.
  intros.
  destruct n; [lia|].
  destruct ls; [congruence|].
  cbn; flia.
Qed.

Lemma P2''_n n:
  segRLs tm
  (h2^^(2^n*4))
  ((h2^^(2^n))++(h0++h0++h1)^^(2^n))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1)))
  ([0;1;0;1;1] ++ ([1;0;1;0;1;1]^^(2^n-1))).
Proof.
  rewrite <-(tl_lpow ([1;0]++[1;0]++[1;1])); [|cbn; congruence|lia].
  do 2 rewrite <-s3_spec.
  replace (2^n*3) with (2^n+(2^n+2^n)) by lia.
  repeat rewrite s3_add.
  applys_eq (P2''_n_0 n);
  cbn[w3'];
  repeat rewrite h2s_spec;
  repeat rewrite <-app_assoc;
  repeat rewrite h3_spec;
  repeat rewrite w3_spec;
  repeat rewrite w3'_spec.
  - cbn[Nat.pow]; flia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); trivial; lia.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
  - pose proof (pow2mod3 n);
    eo_cases n;
    destruct (mod3 (2^n)); try lia.
    all: replace (2^n) with (S(2^n-1)) by lia; trivial.
Qed.


Lemma Pa_n n:
  sideRLs tm (h2^^(2^n*8-2)) 0inf (RC0 (2^n-1)).
Proof.
  induction n using lt_wf_ind.
  (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*2^n*8-2) with ((2^n*8-2)+2^n*8) by lia.
  eapply sideRLs_trans_add.
  1: apply (H n); lia.
  unfold RC0.
  epose proof (P2''_n (S n)) as P2''.
  cbn[Nat.pow] in P2''.
  replace (1+(2*2^n-1)*2) with (2*2^n-1+2*2^n) by lia.
  rewrite (lpow_add _ _ (2*2^n)),Str_app_assoc.
  do 2 rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: applys_eq P2''; flia.
  do 2 (destruct n; [esc|]).
  cbn[Nat.pow].
  replace (2*(2*(2*2^n))) with ((2^n*8-2+2)) by lia.
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans.
  1: apply (H n); lia.
  rewrite Nat.sub_add by lia.
  replace (2^n*8) with ((2^n-1)*4+(2^n*4+4)) by lia.
  rewrite lpow_add,app_assoc.
  replace ((2^n-1)*4+(2^n*4+4)) with (2^n*8) by lia.
  eapply sideRLs_trans.
  1: applys_eq (RIncs0 0 (2^n-1)); flia.
  applys_eq (RIncs1 (2^n*4-1) (2^n*4-4)); unfold RC2; flia.
Qed.

Lemma BigStep m n:
  LC m {{{ (hR,R) }}} 0inf -->*
  LC ((2^n*8-2)*2+m) {{{ (hR,R) }}} RC0 (2^n-1).
Proof.
  eapply sideRLs_concat_1.
  1: apply Pa_n.
  apply LIncs.
Qed.

Lemma pow2_lt n:
  n<2^n.
Proof.
  induction n; cbn[Nat.pow]; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_; split.
  - eapply evstep_trans.
    2: apply (BigStep 3 n).
    esx.
  - split.
    + unfold LC,RC0,to_DH_config.
      solve_sigma_score.
    + pose proof (pow2_lt n).
      lia.
Qed.

End TM3.

