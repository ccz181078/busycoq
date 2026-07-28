From BusyCoq Require Import Individual62 Longitudinal DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1LA_1RA0LD_0LC0RE_0LB1RF_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition h1 := [((B,<[1]),(D,[0]));((B,<[1;1]),(D,[0;1;0;1;0]))].
Definition h2 := [((B,<[1]),(D,[0]))].

Inductive RC :=
| D0(a:nat)(r:RC)
| D1(a:nat)(r:RC)
| Dt0 | Dt1.

Fixpoint toRC x :=
match x with
| D0 a r => [0] *> [1;0]^^a *> toRC r
| D1 a r => [1] *> [1;0]^^a *> toRC r
| Dt0 => [0;1] *> 0inf
| Dt1 => [1;1] *> 0inf
end.

Inductive RInc: RC->RC->Prop :=
| RInc01 a b r r':
  RInc r r' ->
  RInc (D0 (2+a) (D1 (2+b) r)) (D0 (1+a) (D1 (3+b) r'))
| ROv01 b c r:
  RInc (D0 1 (D1 (2+b) (D0 c r))) (D0 (2+b) (D1 c r))
| ROv01t b:
  RInc (D0 1 (D1 (2+b) Dt0)) (D0 (2+b) Dt1)
| RInc011 a b c r r':
  RInc r r' ->
  RInc (D0 (2+a) (D1 (2+b) (D1 (2+c) r))) (D0 (2+a) (D0 (1+b) (D1 (3+c) r')))
| RInc0t a:
  RInc (D0 (2+a) Dt1) (D0 (2+a) Dt0)
| RInct:
  RInc Dt0 Dt0
.

Lemma RInc_spec x x':
  RInc x x' ->
  sideRLs tm h1 (toRC x) (toRC x').
Proof.
  intro H.
  induction H; cbn[toRC].
  2,3,5,6: ut; esx.
  all: repeat rewrite <-Str_app_assoc; eapply segRLs_sideRLs_concat; [|eauto 1]; ut; esx.
Qed.

Definition S0 x := 0inf <* <[1;1;0;0;1;0; 1;1;1;0;0;1;0; 1;1;1] {{{ (B,<[1],R) }}} toRC x.

Lemma BigStep x x0 x1:
  RInc x x0 ->
  RInc x0 x1 ->
  S0 x -->+ S0 (D0 1 (D1 5 x1)).
Proof.
  unfold S0.
  intros H H0.
  eapply RInc_spec in H,H0.
  repeat
  match goal with
  | [H: sideRLs _ _ _ _ |- _] => inverts H
  end.
  unfold sideRL in *.
  follow10 H7.
  er.
  follow100 H4.
  er.
  follow100 H6.
  er.
  follow100 H5.
  er.
Qed.

Lemma init:
  c0 -->*
  S0 (D0 1 (D1 5 Dt0)).
Proof.
  esx.
Qed.

Local Open Scope nat_scope.

Definition RP p := exists k, p = 5+4*k.

Lemma RP_ge p:
  RP p -> 5<=p.
Proof.
  intros [k ->]; flia.
Qed.

Lemma RP_next p:
  RP p -> RP (2*p-1).
Proof.
  intros [k ->].
  exists (1+2*k).
  flia.
Qed.

Lemma RInc01' A B r r':
  2<=A -> 2<=B ->
  RInc r r' ->
  RInc (D0 A (D1 B r)) (D0 (A-1) (D1 (B+1) r')).
Proof.
  intros HA HB H.
  applys_eq (RInc01 (A-2) (B-2) r r' H); flia.
Qed.

Lemma RInc011' A B C r r':
  2<=A -> 2<=B -> 2<=C ->
  RInc r r' ->
  RInc (D0 A (D1 B (D1 C r))) (D0 A (D0 (B-1) (D1 (C+1) r'))).
Proof.
  intros HA HB HC H.
  applys_eq (RInc011 (A-2) (B-2) (C-2) r r' H); flia.
Qed.

Lemma ROv01' B C r:
  2<=B ->
  RInc (D0 1 (D1 B (D0 C r))) (D0 B (D1 C r)).
Proof.
  intro HB.
  applys_eq (ROv01 (B-2) C r); flia.
Qed.

Lemma ROv01t' B:
  2<=B ->
  RInc (D0 1 (D1 B Dt0)) (D0 B Dt1).
Proof.
  intro HB.
  applys_eq (ROv01t (B-2)); flia.
Qed.

Lemma RInc0t' A:
  2<=A ->
  RInc (D0 A Dt1) (D0 A Dt0).
Proof.
  intro HA.
  applys_eq (RInc0t (A-2)); flia.
Qed.

Inductive RT: nat->RC->Prop :=
| RTt p:
  RP p ->
  RT p Dt0
| RT0 p:
  RP p ->
  RT p (D0 p Dt0)
| RTe p s:
  RP p ->
  RR (p-1) (p+1) s ->
  RT p (D0 (p-1) (D1 (p+1) s))
| RTo p s:
  RP p ->
  RR (p-2) (p+2) s ->
  RT p (D0 p (D0 (p-2) (D1 (p+2) s)))
with RR: nat->nat->RC->Prop :=
| RR0 a b:
  1<=a ->
  2<=b ->
  RP (a+b-1) ->
  RR a b Dt0
| RRc b s:
  2<=b ->
  RT b s ->
  RR 1 b s
| RRm b s:
  2<=b ->
  RM (b+1) s ->
  RR 2 b s
| RRs a b s:
  3<=a ->
  2<=b ->
  RR (a-2) (b+2) s ->
  RR a b (D0 (a-2) (D1 (b+2) s))
with RM: nat->RC->Prop :=
| RMt p:
  RP p ->
  RM p (D0 p Dt1)
| RM0 p:
  RP p ->
  RM p (D0 p (D1 p Dt0))
| RMe p s:
  RP p ->
  RR (p-1) (p+1) s ->
  RM p (D0 p (D1 (p-1) (D1 (p+1) s)))
| RMo p s:
  RP p ->
  RR (p-2) (p+2) s ->
  RM p (D0 p (D1 p (D0 (p-2) (D1 (p+2) s)))).

Scheme RT_ind' := Induction for RT Sort Prop
with RR_ind' := Induction for RR Sort Prop
with RM_ind' := Induction for RM Sort Prop.
Combined Scheme RWFp_ind from RT_ind', RR_ind', RM_ind'.

Definition RTP p r := exists r', RInc (D0 1 (D1 p r)) r' /\ RM p r'.
Definition RRP a b s :=
  (exists s', RInc (D0 a (D1 b s)) s' /\
  ((a=1 /\ RM b s') \/
   exists t, s'=D0 (a-1) (D1 (b+1) t) /\ RR (a-1) (b+1) t)) /\
  (2<=a -> exists s', RInc s s' /\ RR (a-1) (b+1) s').
Definition RMP p r := exists r', RInc r r' /\ RT p r'.

Lemma RR_ge a b s:
  RR a b s -> 1<=a.
Proof.
  intro H.
  inversion H; subst; flia.
Qed.

Ltac bound_flia :=
  match goal with
  | H: RP ?p |- _ => pose proof (RP_ge _ H)
  | _ => idtac
  end;
  flia.

Lemma RWFp_step:
  (forall p r, RT p r -> RTP p r) /\
  (forall a b s, RR a b s -> RRP a b s) /\
  (forall p r, RM p r -> RMP p r).
Proof.
  apply (RWFp_ind
    (fun p r _ => RTP p r)
    (fun a b s _ => RRP a b s)
    (fun p r _ => RMP p r));
    unfold RTP, RRP, RMP; intros.
  - exists (D0 p Dt1).
    split.
    + apply ROv01t'.
      bound_flia.
    + apply RMt; exact r.
  - exists (D0 p (D1 p Dt0)).
    split.
    + apply ROv01'.
      * bound_flia.
    + apply RM0; exact r.
  - exists (D0 p (D1 (p-1) (D1 (p+1) s))).
    split.
    + apply ROv01'.
      bound_flia.
    + apply RMe; assumption.
  - exists (D0 p (D1 p (D0 (p-2) (D1 (p+2) s)))).
    split.
    + apply ROv01'.
      * bound_flia.
    + apply RMo; assumption.
  - assert (HTail: 2<=a -> exists s', RInc Dt0 s' /\ RR (a-1) (b+1) s').
    {
      intro HA.
      exists Dt0.
      split.
      - apply RInct.
      - applys_eq (RR0 (a-1) (b+1)); try flia.
        applys_eq r; flia.
    }
    split.
    + destruct a as [|[|a]].
      * flia.
      * exists (D0 b Dt1).
        split.
        -- apply ROv01t'; bound_flia.
        -- left.
           split; [reflexivity|].
           applys_eq (RMt b).
           applys_eq r; flia.
      * destruct (HTail ltac:(flia)) as [t [HI HRR]].
        exists (D0 (S (S a)-1) (D1 (b+1) t)).
        split.
        -- apply RInc01'; try flia.
           exact HI.
        -- right.
           exists t.
           split; [reflexivity|exact HRR].
    + exact HTail.
  - destruct H as [s' [HI HRM]].
    split.
    + exists s'.
      split.
      * exact HI.
      * left.
        split; [reflexivity|exact HRM].
    + intro HA; flia.
  - assert (HTail: 2<=2 -> exists s', RInc s s' /\ RR (2-1) (b+1) s').
    {
      intro H2.
      destruct H as [s' [HI HRT]].
      exists s'.
      split.
      - exact HI.
      - applys_eq (RRc (b+1) s'); try flia.
        exact HRT.
    }
    split.
    + destruct (HTail ltac:(flia)) as [t [HI HRR]].
      exists (D0 1 (D1 (b+1) t)).
      split.
      * replace 1 with (2-1) by flia.
        apply RInc01'; try flia.
        exact HI.
      * right.
        exists t.
        split; [reflexivity|].
        applys_eq HRR; flia.
    + exact HTail.
  - destruct H as [[t [HI Hcase]] _].
    assert (HTail: 2<=a -> exists s', RInc (D0 (a-2) (D1 (b+2) s)) s' /\ RR (a-1) (b+1) s').
    {
      intro H2.
      destruct Hcase as [[Ha1 HRM]|[u [Hu HRR]]].
      - exists t.
        split.
        + exact HI.
        + applys_eq (RRm (b+1) t); try flia.
          applys_eq HRM; flia.
      - subst t.
        assert (HA4: 4<=a).
        {
          pose proof (RR_ge _ _ _ HRR).
          flia.
        }
        exists (D0 (a-2-1) (D1 (b+2+1) u)).
        split.
        + exact HI.
        + applys_eq (RRs (a-1) (b+1) u); try flia.
          applys_eq HRR; flia.
    }
    split.
    + destruct (HTail ltac:(flia)) as [u [HIu HRR]].
      exists (D0 (a-1) (D1 (b+1) u)).
      split.
      * apply RInc01'; try flia.
        exact HIu.
      * right.
        exists u.
        split; [reflexivity|exact HRR].
    + exact HTail.
  - exists (D0 p Dt0).
    split.
    + apply RInc0t'.
      bound_flia.
    + apply RT0; exact r.
  - exists (D0 (p-1) (D1 (p+1) Dt0)).
    split.
    + apply RInc01'; try bound_flia.
      apply RInct.
    + apply RTe.
      * exact r.
      * applys_eq (RR0 (p-1) (p+1)); try bound_flia.
        applys_eq (RP_next p r); flia.
  - destruct H as [_ HTail].
    destruct (HTail ltac:(bound_flia)) as [s' [HI HRR]].
    exists (D0 p (D0 (p-2) (D1 (p+2) s'))).
    split.
    + applys_eq (RInc011' p (p-1) (p+1) s s'); try bound_flia.
      exact HI.
    + apply RTo.
      * exact r.
      * applys_eq HRR; flia.
  - destruct H as [[s' [HI Hcase]] _].
    destruct Hcase as [[Hp1 HRM]|[t [Hs' HRR]]].
    + bound_flia.
    + subst s'.
      exists (D0 (p-1) (D1 (p+1) (D0 (p - 2 - 1) (D1 (p + 2 + 1) t)))).
      split.
      * apply RInc01'; try bound_flia.
        exact HI.
      * apply RTe.
        -- exact r.
        -- applys_eq (RRs (p-1) (p+1) t); try bound_flia.
           applys_eq HRR; flia.
Qed.

Lemma RWF_spec:
  exists (RWF:RC->Prop),
  RWF (D0 1 (D1 5 Dt0)) /\
  (forall r,
  RWF r ->
  exists r0 r1,
  RInc r r0 /\ RInc r0 r1 /\ RWF (D0 1 (D1 5 r1))).
Proof.
  exists (fun r => exists s, r = D0 1 (D1 5 s) /\ RT 5 s).
  split.
  - exists Dt0.
    split; [reflexivity|].
    apply RTt.
    exists 0; flia.
  - intros r [s [-> HRT]].
    destruct RWFp_step as [HRT_step [_ HRM_step]].
    destruct (HRT_step 5 s HRT) as [r0 [H0 HRM]].
    destruct (HRM_step 5 r0 HRM) as [r1 [H1 HRT1]].
    exists r0, r1.
    split; [exact H0|].
    split; [exact H1|].
    exists r1.
    split; [reflexivity|exact HRT1].
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  epose proof RWF_spec as [RWF [I1 I2]].
  eapply progress_nonhalt_cond with (P:=RWF).
  2: apply I1.
  intros.
  apply I2 in H.
  destruct H as [r0 [r1 [I3 [I4 I5]]]].
  eexists; split.
  2: apply I5.
  eapply BigStep; eauto 1.
Qed.

End TM1.

