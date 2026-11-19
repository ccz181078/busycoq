From BusyCoq Require Import Individual62 Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.

Open Scope list.

Lemma step_c_None tm c:
  step_c tm c = None ->
  halts tm c.
Proof.
  unfold step_c.
  intros.
  apply halted_halts.
  destruct c as [q [[l m] r]].
  destruct (tm (q,m)) as [[[o []]]|] eqn:E.
  1,2: inverts H.
  apply E.
Qed.



Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1LE_0RC1LD_1RD0RD_1LA1RC_1LF0LA_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation hR := (D,@nil Sym).
Notation hL := (E,@nil Sym).
Notation h := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation d0 := [1;1;1;1;0;1].
Notation d1 := [1;1;1;1;1;1].
Notation w := [1;0].

Fixpoint rw_r(T:nat)(r:side):side :=
match T with
| O => r
| S T =>
match r with
| 1>>0>>r => 1>>0>>rw_r T r
| 1>>1>>1>>1>>0>>1>>r => 1>>1>>1>>1>>1>>1>>rw_r T r
| 1>>1>>1>>1>>1>>1>>r => 1>>1>>1>>1>>1>>1>>rw_r T r
| _ => r
end
end.

Lemma LIncs n l:
  sideRLs (flip tm) (hLR^^n) (l<<0<<0<<1<<0) (l<<0<<0<<1<<0).
Proof.
  eapply sideRLs_wall; esx.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity).

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Close Scope sym.

Lemma rw_r_spec T r:
  exists n,
  sideRLs tm (h^^n) r (rw_r T r).
Proof.
  gen r.
  induction T; cbn[rw_r]; intros.
  - exists O.
    esx.
  - refine 
    (match r with
    | 1>>0>>r => _
    | 1>>1>>1>>1>>0>>1>>r => _
    | 1>>1>>1>>1>>1>>1>>r => _
    | _ => _
    end)%sym.
    1,3,4,5,7: exists O; esx.
    + destruct (IHT r) as [n I1].
      exists n.
      eapply @segRLs_sideRLs_concat with (w1:=w) (w2:=w).
      2: apply I1.
      am 1 1 n 0 0.
    + destruct (IHT r) as [n I1].
      exists (n*2+1).
      eapply @segRLs_sideRLs_concat with (w1:=d0) (w2:=d1).
      2: apply I1.
      am 2 1 n 1 0.
    + destruct (IHT r) as [n I1].
      exists (n*2).
      eapply @segRLs_sideRLs_concat with (w1:=d1) (w2:=d1).
      2: apply I1.
      am 2 1 n 0 0.
Qed.

Open Scope sym.

Import Eqb.

Section mstep_sec.

Hypothesis T:nat.

Definition astep(x:Q*tape):(Q*tape) :=
let '(q,(l,m,r)):=x in
if eqb q D then
match l with
| l0<<0<<0<<1<<0 => 
  let r':= rw_r T (m>>r) in
  l {{D}}> r'
| _ => x
end
else x.

Definition mstep x :=
match step_c tm x with
| Some x' => inl (astep x')
| None => inr tt
end.

Lemma astep_spec x:
  x -->* astep x.
Proof.
  unfold astep.
  destruct x as [q [[l m] r]].
  destruct (eqb_spec q D); subst.
  2: finish.
  refine
  (match l with
  | l0<<0<<0<<1<<0 => _
  | _ => _
  end).
  1,3,4,5: finish.
  epose proof (rw_r_spec T (m>>r)) as [n I1].
  epose proof (sideRLs_concat_1 I1 (LIncs _ _)) as I2.
  apply I2.
Qed.

Definition msteps T0 :=
  N_iter_until mstep (inl c0) T0.

Lemma msteps_spec T0:
match msteps T0 with
| inl x => c0 -->* x
| inr _ => halts tm c0
end.
Proof.
  eapply N_iter_until_spec.
  2: finish.
  intros.
  unfold mstep.
  destruct (step_c tm x0) as [x'|] eqn:E.
  - apply step_c_spec in E.
    follow H.
    eapply evstep_step.
    1: apply E.
    apply astep_spec.
  - apply step_c_None in E.
    eapply halts_evstep; eauto 1.
Qed.

Lemma msteps_halt T0:
  msteps T0 = inr tt ->
  halts tm c0.
Proof.
  intros.
  pose proof (msteps_spec T0) as I1.
  rewrite H in I1.
  trivial.
Qed.

End mstep_sec.

Lemma halt: halts tm c0.
Proof.
  eapply (msteps_halt (10^6) (10^12)).
  native_check_eq.
Time Qed.

End TM1.

