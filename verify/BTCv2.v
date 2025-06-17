From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0LC0LE_---1LD_1LA0LD_1LB1RF_0RE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;1;0].
Notation d2 := [1;0;1;0].
Notation dx' := <[1;0].
Notation d21' := <[1;0;1;0; 1;0;0].
Notation dC := [1;0;0;1;0].
Notation Rh := ([1;1;0;1;0]*>0inf).
Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Inductive RD := w1|w2|wC.

Inductive RInc: list RD -> list RD -> Prop :=
| RInc11 r r':
    RInc r r' ->
    RInc (w1::w1::r) (w1::w1::r')
| RInc12 r r':
    RInc r r' ->
    RInc (w1::w2::r) (w1::w2::r')
| RInc21 r r':
    RInc r r' ->
    RInc (w2::w1::r) (w2::w1::r')
| RInc22 r r':
    RInc r r' ->
    RInc (w2::w2::r) (w2::w2::r')
| RInc21C r r':
    RInc r r' ->
    RInc (w2::w1::wC::w2::r) (wC::w2::w1::w2::r')
| RInc11C r r':
    RInc r r' ->
    RInc (w1::w1::wC::w2::r) (w2::w2::w1::w2::r')
| RInc12C r:
    RInc (w1::w2::wC::r) (w1::w1::w1::r)
| RInc22C r:
    RInc (w2::w2::wC::r) (w2::w1::w1::r)
| RInc1':
    RInc (w1::nil) (w2::nil)
| RInc2':
    RInc (w2::nil) (wC::nil)
| RInc21C':
    RInc (w2::w1::wC::nil) (wC::w2::w2::nil)
| RInc11C':
    RInc (w1::w1::wC::nil) (w2::w2::w2::nil)
. 

Inductive RWF: nat -> list RD -> Prop :=
| RWF11 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w1::c::r)
| RWF12 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w2::c::r)
| RWF21 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w1::c::r)
| RWF22 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w2::c::r)
| RWFC21 n r:
    RWF n (w1::r) ->
    RWF (S n) (wC::w2::w1::r)
| RWFC22 n r:
    RWF n (w2::r) ->
    RWF (S n) (wC::w2::w2::r)
| RWF_O a:
    RWF O (a::nil)
.

Fixpoint Rmp(x:list RD):side :=
match x with
| w1::r => d1 *> Rmp r
| w2::r => d2 *> Rmp r
| wC::r => dC *> Rmp r
| [] => Rh
end.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Inductive RnotC: list RD -> Prop :=
| RnotC_1 r: RnotC (w1::r)
| RnotC_2 r: RnotC (w2::r)
.

Lemma RInc_WF' n x:
  RWF n x ->
  RnotC x ->
  exists x', RInc x x'.
Proof.
  gen x.
  induction n using lt_wf_ind.
  intros x HW HC.
  inverts HW.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * eexists.
        eapply RInc11C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + eexists; eapply RInc12C.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * eexists.
        eapply RInc21C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + eexists; eapply RInc22C.
  - inverts HC.
  - inverts HC.
  - inverts HC.
    + eexists; eapply RInc1'.
    + eexists; eapply RInc2'.
  Unshelve.
  all: lia.
Qed.

Lemma RInc_WF n x x':
  RInc x x' ->
  RWF n x ->
  RWF n x'.
Proof.
  gen x x'.
  induction n using lt_wf_ind; intros x x' HI HW.
  inverts HI.
  1-4: inverts HW;
    remember H0 as HI0;
    inverts H0;
    econstructor; eauto.
  1,2: inverts HW;
    econstructor;
    remember H0 as HI0;
    inverts H0;
    inverts H3;
    econstructor;
    eauto.
  1-6: inverts HW;
    econstructor;
    inverts H2;
    econstructor; eauto.
Qed.

Lemma isC n x:
  RWF n x ->
  RnotC x \/ (exists r, x = wC::r /\ RWF n (w1::r)).
Proof.
  intros HW.
  inverts HW.
  7: destruct a.
  1-4,7-8: left; constructor.
  all: right;
    eexists;
    split; [reflexivity|];
    econstructor; eauto.
Qed.

Definition S0 '(n,x) := 0inf <* d21'^^(1+n) <* dx' |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (3,[w1;w1;wC])).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,x) => exists m, RWF m x).
  2: eexists; repeat econstructor.
  intros [n x] [m HW].
  epose proof (isC _ _ HW) as [HC|[r[Hr HW']]].
  - epose proof (RInc_WF' _ _ HW HC) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW) as HW'.
    eexists (S n,x').
    split.
    2: eexists; eapply HW'.
    unfold S0.
    follow RInc_spec.
    es.
  - subst.
    epose proof (RInc_WF' _ _ HW' (RnotC_1 _)) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW') as HW''.
    eexists (S n,w1::w1::x').
    split.
    + unfold S0.
      mid10 (0inf <* d21'^^(2+n) <* <[0] |> Rmp (w1::r)).
      1: es.
      follow RInc_spec.
      rewrite lpow_add,Str_app_assoc.
      do 2 (repeat step1; use_shift_rule).
      er.
    + remember HW'' as I;
      inverts HW'';
      eexists; econstructor; eauto.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0LC0RE_---1LD_1LA0LD_1LB1RF_0RE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;1;0].
Notation d2 := [1;0;1;0].
Notation dx' := <[1;0].
Notation d21' := <[1;0;1;0; 1;0;0].
Notation dC := [1;0;0;1;0].
Notation Rh := ([1;1;0;1;0]*>0inf).
Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Inductive RD := w1|w2|wC.

Inductive RInc: list RD -> list RD -> Prop :=
| RInc11 r r':
    RInc r r' ->
    RInc (w1::w1::r) (w1::w1::r')
| RInc12 r r':
    RInc r r' ->
    RInc (w1::w2::r) (w1::w2::r')
| RInc21 r r':
    RInc r r' ->
    RInc (w2::w1::r) (w2::w1::r')
| RInc22 r r':
    RInc r r' ->
    RInc (w2::w2::r) (w2::w2::r')
| RInc21C r r':
    RInc r r' ->
    RInc (w2::w1::wC::w2::r) (wC::w2::w1::w2::r')
| RInc11C r r':
    RInc r r' ->
    RInc (w1::w1::wC::w2::r) (w2::w2::w1::w2::r')
| RInc12C r:
    RInc (w1::w2::wC::r) (w1::w1::w1::r)
| RInc22C r:
    RInc (w2::w2::wC::r) (w2::w1::w1::r)
| RInc1':
    RInc (w1::nil) (w2::nil)
| RInc2':
    RInc (w2::nil) (wC::nil)
| RInc21C':
    RInc (w2::w1::wC::nil) (wC::w2::w2::nil)
| RInc11C':
    RInc (w1::w1::wC::nil) (w2::w2::w2::nil)
. 

Inductive RWF: nat -> list RD -> Prop :=
| RWF11 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w1::c::r)
| RWF12 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w2::c::r)
| RWF21 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w1::c::r)
| RWF22 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w2::c::r)
| RWFC21 n r:
    RWF n (w1::r) ->
    RWF (S n) (wC::w2::w1::r)
| RWFC22 n r:
    RWF n (w2::r) ->
    RWF (S n) (wC::w2::w2::r)
| RWF_O a:
    RWF O (a::nil)
.

Fixpoint Rmp(x:list RD):side :=
match x with
| w1::r => d1 *> Rmp r
| w2::r => d2 *> Rmp r
| wC::r => dC *> Rmp r
| [] => Rh
end.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Inductive RnotC: list RD -> Prop :=
| RnotC_1 r: RnotC (w1::r)
| RnotC_2 r: RnotC (w2::r)
.

Lemma RInc_WF' n x:
  RWF n x ->
  RnotC x ->
  exists x', RInc x x'.
Proof.
  gen x.
  induction n using lt_wf_ind.
  intros x HW HC.
  inverts HW.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * eexists.
        eapply RInc11C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + eexists; eapply RInc12C.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * eexists.
        eapply RInc21C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + eexists; eapply RInc22C.
  - inverts HC.
  - inverts HC.
  - inverts HC.
    + eexists; eapply RInc1'.
    + eexists; eapply RInc2'.
  Unshelve.
  all: lia.
Qed.

Lemma RInc_WF n x x':
  RInc x x' ->
  RWF n x ->
  RWF n x'.
Proof.
  gen x x'.
  induction n using lt_wf_ind; intros x x' HI HW.
  inverts HI.
  1-4: inverts HW;
    remember H0 as HI0;
    inverts H0;
    econstructor; eauto.
  1,2: inverts HW;
    econstructor;
    remember H0 as HI0;
    inverts H0;
    inverts H3;
    econstructor;
    eauto.
  1-6: inverts HW;
    econstructor;
    inverts H2;
    econstructor; eauto.
Qed.

Lemma isC n x:
  RWF n x ->
  RnotC x \/ (exists r, x = wC::r /\ RWF n (w1::r)).
Proof.
  intros HW.
  inverts HW.
  7: destruct a.
  1-4,7-8: left; constructor.
  all: right;
    eexists;
    split; [reflexivity|];
    econstructor; eauto.
Qed.

Definition S0 '(n,x) := 0inf <* d21'^^(1+n) <* dx' |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (3,[w1;w1;wC])).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,x) => exists m, RWF m x).
  2: eexists; repeat econstructor.
  intros [n x] [m HW].
  epose proof (isC _ _ HW) as [HC|[r[Hr HW']]].
  - epose proof (RInc_WF' _ _ HW HC) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW) as HW'.
    eexists (S n,x').
    split.
    2: eexists; eapply HW'.
    unfold S0.
    follow RInc_spec.
    es.
  - subst.
    epose proof (RInc_WF' _ _ HW' (RnotC_1 _)) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW') as HW''.
    eexists (S n,w1::w1::x').
    split.
    + unfold S0.
      mid10 (0inf <* d21'^^(2+n) <* <[0] |> Rmp (w1::r)).
      1: es.
      follow RInc_spec.
      rewrite lpow_add,Str_app_assoc.
      do 2 (repeat step1; use_shift_rule).
      er.
    + remember HW'' as I;
      inverts HW'';
      eexists; econstructor; eauto.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0LC0LE_---1LD_1LA0LD_1LB1RF_0RE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;1;0].
Notation d2 := [1;0;1;0].
Notation dx' := <[1;0].
Notation d21' := <[1;0;1;0; 1;0;0].
Notation dC := [1;0;0;1;0].
Notation Rh := ([1;1;0;1;0]*>0inf).
Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Inductive RD := w1|w2|wC.

Inductive RInc: list RD -> list RD -> Prop :=
| RInc11 r r':
    RInc r r' ->
    RInc (w1::w1::r) (w1::w1::r')
| RInc12 r r':
    RInc r r' ->
    RInc (w1::w2::r) (w1::w2::r')
| RInc21 r r':
    RInc r r' ->
    RInc (w2::w1::r) (w2::w1::r')
| RInc22 r r':
    RInc r r' ->
    RInc (w2::w2::r) (w2::w2::r')
| RInc21C r r':
    RInc r r' ->
    RInc (w2::w1::wC::w2::r) (wC::w2::w1::w2::r')
| RInc11C r r':
    RInc r r' ->
    RInc (w1::w1::wC::w2::r) (w2::w2::w1::w2::r')
| RInc12C r:
    RInc (w1::w2::wC::r) (w1::w1::w1::r)
| RInc22C r:
    RInc (w2::w2::wC::r) (w2::w1::w1::r)
| RInc1':
    RInc (w1::nil) (w2::nil)
| RInc2':
    RInc (w2::nil) (wC::nil)
| RInc21C':
    RInc (w2::w1::wC::nil) (wC::w2::w2::nil)
| RInc11C':
    RInc (w1::w1::wC::nil) (w2::w2::w2::nil)
. 

Inductive RWF: nat -> list RD -> Prop :=
| RWF11 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w1::c::r)
| RWF12 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w2::c::r)
| RWF21 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w1::c::r)
| RWF22 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w2::c::r)
| RWFC21 n r:
    RWF n (w1::r) ->
    RWF (S n) (wC::w2::w1::r)
| RWFC22 n r:
    RWF n (w2::r) ->
    RWF (S n) (wC::w2::w2::r)
| RWF_O a:
    RWF O (a::nil)
.

Fixpoint Rmp(x:list RD):side :=
match x with
| w1::r => d1 *> Rmp r
| w2::r => d2 *> Rmp r
| wC::r => dC *> Rmp r
| [] => Rh
end.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Inductive RnotC: list RD -> Prop :=
| RnotC_1 r: RnotC (w1::r)
| RnotC_2 r: RnotC (w2::r)
.

Lemma RInc_WF' n x:
  RWF n x ->
  RnotC x ->
  exists x', RInc x x'.
Proof.
  gen x.
  induction n using lt_wf_ind.
  intros x HW HC.
  inverts HW.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * eexists.
        eapply RInc11C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + eexists; eapply RInc12C.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * eexists.
        eapply RInc21C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + eexists; eapply RInc22C.
  - inverts HC.
  - inverts HC.
  - inverts HC.
    + eexists; eapply RInc1'.
    + eexists; eapply RInc2'.
  Unshelve.
  all: lia.
Qed.

Lemma RInc_WF n x x':
  RInc x x' ->
  RWF n x ->
  RWF n x'.
Proof.
  gen x x'.
  induction n using lt_wf_ind; intros x x' HI HW.
  inverts HI.
  1-4: inverts HW;
    remember H0 as HI0;
    inverts H0;
    econstructor; eauto.
  1,2: inverts HW;
    econstructor;
    remember H0 as HI0;
    inverts H0;
    inverts H3;
    econstructor;
    eauto.
  1-6: inverts HW;
    econstructor;
    inverts H2;
    econstructor; eauto.
Qed.

Lemma isC n x:
  RWF n x ->
  RnotC x \/ (exists r, x = wC::r /\ RWF n (w1::r)).
Proof.
  intros HW.
  inverts HW.
  7: destruct a.
  1-4,7-8: left; constructor.
  all: right;
    eexists;
    split; [reflexivity|];
    econstructor; eauto.
Qed.

Definition S0 '(n,x) := 0inf <* d21'^^(1+n) <* dx' |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (3,[w1;w1;wC])).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,x) => exists m, RWF m x).
  2: eexists; repeat econstructor.
  intros [n x] [m HW].
  epose proof (isC _ _ HW) as [HC|[r[Hr HW']]].
  - epose proof (RInc_WF' _ _ HW HC) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW) as HW'.
    eexists (S n,x').
    split.
    2: eexists; eapply HW'.
    unfold S0.
    follow RInc_spec.
    es.
  - subst.
    epose proof (RInc_WF' _ _ HW' (RnotC_1 _)) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW') as HW''.
    eexists (S n,w1::w1::x').
    split.
    + unfold S0.
      mid10 (0inf <* d21'^^(2+n) <* <[0] |> Rmp (w1::r)).
      1: es.
      follow RInc_spec.
      rewrite lpow_add,Str_app_assoc.
      do 2 (repeat step1; use_shift_rule).
      er.
    + remember HW'' as I;
      inverts HW'';
      eexists; econstructor; eauto.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0LC0RE_---1LD_1LA0LD_1LB1RF_0RE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;1;0].
Notation d2 := [1;0;1;0].
Notation dx' := <[1;0].
Notation d21' := <[1;0;1;0; 1;0;0].
Notation dC := [1;0;0;1;0].
Notation Rh := ([1;1;0;1;0]*>0inf).
Notation "l |> r" := (l {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;1;0] *> r) (at level 30).

Inductive RD := w1|w2|wC.

Inductive RInc: list RD -> list RD -> Prop :=
| RInc11 r r':
    RInc r r' ->
    RInc (w1::w1::r) (w1::w1::r')
| RInc12 r r':
    RInc r r' ->
    RInc (w1::w2::r) (w1::w2::r')
| RInc21 r r':
    RInc r r' ->
    RInc (w2::w1::r) (w2::w1::r')
| RInc22 r r':
    RInc r r' ->
    RInc (w2::w2::r) (w2::w2::r')
| RInc21C r r':
    RInc r r' ->
    RInc (w2::w1::wC::w2::r) (wC::w2::w1::w2::r')
| RInc11C r r':
    RInc r r' ->
    RInc (w1::w1::wC::w2::r) (w2::w2::w1::w2::r')
| RInc12C r:
    RInc (w1::w2::wC::r) (w1::w1::w1::r)
| RInc22C r:
    RInc (w2::w2::wC::r) (w2::w1::w1::r)
| RInc1':
    RInc (w1::nil) (w2::nil)
| RInc2':
    RInc (w2::nil) (wC::nil)
| RInc21C':
    RInc (w2::w1::wC::nil) (wC::w2::w2::nil)
| RInc11C':
    RInc (w1::w1::wC::nil) (w2::w2::w2::nil)
. 

Inductive RWF: nat -> list RD -> Prop :=
| RWF11 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w1::c::r)
| RWF12 n c r:
    RWF n (c::r) ->
    RWF (S n) (w1::w2::c::r)
| RWF21 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w1::c::r)
| RWF22 n c r:
    RWF n (c::r) ->
    RWF (S n) (w2::w2::c::r)
| RWFC21 n r:
    RWF n (w1::r) ->
    RWF (S n) (wC::w2::w1::r)
| RWFC22 n r:
    RWF n (w2::r) ->
    RWF (S n) (wC::w2::w2::r)
| RWF_O a:
    RWF O (a::nil)
.

Fixpoint Rmp(x:list RD):side :=
match x with
| w1::r => d1 *> Rmp r
| w2::r => d2 *> Rmp r
| wC::r => dC *> Rmp r
| [] => Rh
end.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Inductive RnotC: list RD -> Prop :=
| RnotC_1 r: RnotC (w1::r)
| RnotC_2 r: RnotC (w2::r)
.

Lemma RInc_WF' n x:
  RWF n x ->
  RnotC x ->
  exists x', RInc x x'.
Proof.
  gen x.
  induction n using lt_wf_ind.
  intros x HW HC.
  inverts HW.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc11,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc11C,HR.
      * eexists.
        eapply RInc11C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc12,HR.
    + eexists; eapply RInc12C.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc21,HR.
    + inverts H0.
      * epose proof (H _ _ _ H3 (RnotC_1 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * epose proof (H _ _ _ H3 (RnotC_2 _)) as [x' HR].
        eexists.
        eapply RInc21C,HR.
      * eexists.
        eapply RInc21C'.
  - destruct c.
    + epose proof (H _ _ _ H0 (RnotC_1 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + epose proof (H _ _ _ H0 (RnotC_2 _)) as [x' HR].
      eexists.
      eapply RInc22,HR.
    + eexists; eapply RInc22C.
  - inverts HC.
  - inverts HC.
  - inverts HC.
    + eexists; eapply RInc1'.
    + eexists; eapply RInc2'.
  Unshelve.
  all: lia.
Qed.

Lemma RInc_WF n x x':
  RInc x x' ->
  RWF n x ->
  RWF n x'.
Proof.
  gen x x'.
  induction n using lt_wf_ind; intros x x' HI HW.
  inverts HI.
  1-4: inverts HW;
    remember H0 as HI0;
    inverts H0;
    econstructor; eauto.
  1,2: inverts HW;
    econstructor;
    remember H0 as HI0;
    inverts H0;
    inverts H3;
    econstructor;
    eauto.
  1-6: inverts HW;
    econstructor;
    inverts H2;
    econstructor; eauto.
Qed.

Lemma isC n x:
  RWF n x ->
  RnotC x \/ (exists r, x = wC::r /\ RWF n (w1::r)).
Proof.
  intros HW.
  inverts HW.
  7: destruct a.
  1-4,7-8: left; constructor.
  all: right;
    eexists;
    split; [reflexivity|];
    econstructor; eauto.
Qed.

Definition S0 '(n,x) := 0inf <* d21'^^(1+n) <* dx' |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (3,[w1;w1;wC])).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=fun '(n,x) => exists m, RWF m x).
  2: eexists; repeat econstructor.
  intros [n x] [m HW].
  epose proof (isC _ _ HW) as [HC|[r[Hr HW']]].
  - epose proof (RInc_WF' _ _ HW HC) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW) as HW'.
    eexists (S n,x').
    split.
    2: eexists; eapply HW'.
    unfold S0.
    follow RInc_spec.
    es.
  - subst.
    epose proof (RInc_WF' _ _ HW' (RnotC_1 _)) as [x' HI].
    epose proof (RInc_WF _ _ _ HI HW') as HW''.
    eexists (S n,w1::w1::x').
    split.
    + unfold S0.
      mid10 (0inf <* d21'^^(2+n) <* <[0] |> Rmp (w1::r)).
      1: es.
      follow RInc_spec.
      rewrite lpow_add,Str_app_assoc.
      do 2 (repeat step1; use_shift_rule).
      er.
    + remember HW'' as I;
      inverts HW'';
      eexists; econstructor; eauto.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0RC0LE_---1LD_1RA1RB_1LF0LF_1RA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;0;1].
Notation dx := [0;1].
Notation dZ := [0;0].
Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{F}} [0;0;1;0;1] *> r) (at level 30).

Inductive RD :=
| DZ(r:RD)
| Dxx1(r:RD)
| Dxxx(r:RD)
| Dx11(r:RD)
| Dx1x(r:RD)
| Dxxx'
| Dx1x'
.

Fixpoint Rmp x :=
match x with
| DZ r => dZ*>Rmp r
| Dxx1 r => dx*>dx*>d1*>Rmp r
| Dxxx r => dx*>dx*>dx*>Rmp r
| Dx11 r => dx*>d1*>d1*>Rmp r
| Dx1x r => dx*>d1*>dx*>Rmp r
| Dxxx' => dx*>dx*>dx*>0inf
| Dx1x' => dx*>d1*>dx*>0inf
end.

Inductive RInc: RD -> RD -> Prop :=
| RIncxx1 r r':
    RInc r r' ->
    RInc (Dxx1 r) (Dxx1 r')
| RIncxxx r r':
    RInc r r' ->
    RInc (Dxxx r) (Dxxx r')
| RIncx11 r r':
    RInc r r' ->
    RInc (Dx11 r) (Dx11 r')
| RIncx1x r r':
    RInc r r' ->
    RInc (Dx1x r) (Dx1x r')
| RIncxx1Z r:
    RInc (Dxx1 (DZ r)) (Dxxx r)
| RIncxxxZ r r':
    RInc r r' ->
    RInc (Dxxx (DZ r)) (Dx11 r')
| RIncx11Z r:
    RInc (Dx11 (DZ r)) (Dx1x r)
| RIncx1xZ r r':
    RInc r r' ->
    RInc (Dx1x (DZ r)) (DZ (Dxx1 r'))
| RIncxxx':
    RInc Dxxx' Dx1x'
| RIncx1x':
    RInc Dx1x' (DZ Dxxx')
.

Inductive RWF: RD->Prop :=
| RWFxx1 r: RWF r -> RWF (Dxx1 r)
| RWFxxx r: RWF r -> RWF (Dxxx r)
| RWFx11 r: RWF r -> RWF (Dx11 r)
| RWFx1x r: RWF r -> RWF (Dx1x r)
| RWFxx1Z r: RWF r -> RWF (Dxx1 (DZ r))
| RWFxxxZ r: RWF r -> RWF (Dxxx (DZ r))
| RWFx11Z r: RWF r -> RWF (Dx11 (DZ r))
| RWFx1xZ r: RWF r -> RWF (Dx1x (DZ r))
| RWFxxx': RWF Dxxx'
| RWFx1x': RWF Dx1x'
.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Lemma RInc_WF' x:
  RWF x ->
  exists x', RInc x x'.
Proof.
  intros HW.
  induction HW.
  all: try destruct IHHW;
    eexists;
    solve [econstructor; eauto].
Qed.

Inductive RWFZ: RD->Prop :=
| RWFZ_intro r: RWF r -> RWFZ (DZ r)
.

Ltac solve_RWF :=
  left;
  solve [econstructor; eauto].

Lemma RInc_WF x x':
  RInc x x' ->
  RWF x ->
  (RWF x' \/ RWFZ x').
Proof.
  intros HI.
  induction HI; intros.
  1-4: inverts H; [ | inverts HI ];
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ].
    + right.
      do 2 econstructor; eauto.
    + inverts HZ.
      right.
      solve [do 2 econstructor; apply H].
  - left; constructor.
  - right; do 2 constructor.
Qed.

Definition S0 x := 0inf <* <[1;0] |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 Dxxx').
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=RWF).
  2: constructor.
  intros x HW.
  epose proof (RInc_WF' _ HW) as [x' HI].
  eexists (Dxxx x').
  split.
  1: unfold S0; follow RInc_spec; es.
  epose proof (RInc_WF _ _ HI HW) as [HW'|HZ].
  - constructor; eauto.
  - inverts HZ.
    solve[constructor; eauto].
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB0RE_0RC0LF_---1LD_1RA1LE_1RA1RB_1LD0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;0;1].
Notation dx := [0;1].
Notation dZ := [0;0].
Notation "l |> r" := (l <* <[1;0] {{E}}> r) (at level 30).
Notation "l <| r" := (l <{{D}} [0;0;1;0;1] *> r) (at level 30).

Inductive RD :=
| DZ(r:RD)
| Dxx1(r:RD)
| Dxxx(r:RD)
| Dx11(r:RD)
| Dx1x(r:RD)
| Dxxx'
| Dx1x'
.

Fixpoint Rmp x :=
match x with
| DZ r => dZ*>Rmp r
| Dxx1 r => dx*>dx*>d1*>Rmp r
| Dxxx r => dx*>dx*>dx*>Rmp r
| Dx11 r => dx*>d1*>d1*>Rmp r
| Dx1x r => dx*>d1*>dx*>Rmp r
| Dxxx' => dx*>dx*>dx*>0inf
| Dx1x' => dx*>d1*>dx*>0inf
end.

Inductive RInc: RD -> RD -> Prop :=
| RIncxx1 r r':
    RInc r r' ->
    RInc (Dxx1 r) (Dxx1 r')
| RIncxxx r r':
    RInc r r' ->
    RInc (Dxxx r) (Dxxx r')
| RIncx11 r r':
    RInc r r' ->
    RInc (Dx11 r) (Dx11 r')
| RIncx1x r r':
    RInc r r' ->
    RInc (Dx1x r) (Dx1x r')
| RIncxx1Z r:
    RInc (Dxx1 (DZ r)) (Dxxx r)
| RIncxxxZ r r':
    RInc r r' ->
    RInc (Dxxx (DZ r)) (Dx11 r')
| RIncx11Z r:
    RInc (Dx11 (DZ r)) (Dx1x r)
| RIncx1xZ r r':
    RInc r r' ->
    RInc (Dx1x (DZ r)) (DZ (Dxx1 r'))
| RIncxxx':
    RInc Dxxx' Dx1x'
| RIncx1x':
    RInc Dx1x' (DZ Dxxx')
.

Inductive RWF: RD->Prop :=
| RWFxx1 r: RWF r -> RWF (Dxx1 r)
| RWFxxx r: RWF r -> RWF (Dxxx r)
| RWFx11 r: RWF r -> RWF (Dx11 r)
| RWFx1x r: RWF r -> RWF (Dx1x r)
| RWFxx1Z r: RWF r -> RWF (Dxx1 (DZ r))
| RWFxxxZ r: RWF r -> RWF (Dxxx (DZ r))
| RWFx11Z r: RWF r -> RWF (Dx11 (DZ r))
| RWFx1xZ r: RWF r -> RWF (Dx1x (DZ r))
| RWFxxx': RWF Dxxx'
| RWFx1x': RWF Dx1x'
.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Lemma RInc_WF' x:
  RWF x ->
  exists x', RInc x x'.
Proof.
  intros HW.
  induction HW.
  all: try destruct IHHW;
    eexists;
    solve [econstructor; eauto].
Qed.

Inductive RWFZ: RD->Prop :=
| RWFZ_intro r: RWF r -> RWFZ (DZ r)
.

Ltac solve_RWF :=
  left;
  solve [econstructor; eauto].

Lemma RInc_WF x x':
  RInc x x' ->
  RWF x ->
  (RWF x' \/ RWFZ x').
Proof.
  intros HI.
  induction HI; intros.
  1-4: inverts H; [ | inverts HI ];
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ].
    + right.
      do 2 econstructor; eauto.
    + inverts HZ.
      right.
      solve [do 2 econstructor; apply H].
  - left; constructor.
  - right; do 2 constructor.
Qed.

Definition S0 x := 0inf <* <[1;0] |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 Dxxx').
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=RWF).
  2: constructor.
  intros x HW.
  epose proof (RInc_WF' _ HW) as [x' HI].
  eexists (Dxxx x').
  split.
  1: unfold S0; follow RInc_spec; es.
  epose proof (RInc_WF _ _ HI HW) as [HW'|HZ].
  - constructor; eauto.
  - inverts HZ.
    solve[constructor; eauto].
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0LB_1RC1LD_1LE0RD_1RC1RE_1RF0LA_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d1 := [1;0;1].
Notation dx := [0;1].
Notation dZ := [0;0].
Notation "l |> r" := (l <* <[1;0] {{D}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} [0;0;1;0;1] *> r) (at level 30).

Inductive RD :=
| DZ(r:RD)
| Dxx1(r:RD)
| Dxxx(r:RD)
| Dx11(r:RD)
| Dx1x(r:RD)
| Dxxx'
| Dx1x'
.

Fixpoint Rmp x :=
match x with
| DZ r => dZ*>Rmp r
| Dxx1 r => dx*>dx*>d1*>Rmp r
| Dxxx r => dx*>dx*>dx*>Rmp r
| Dx11 r => dx*>d1*>d1*>Rmp r
| Dx1x r => dx*>d1*>dx*>Rmp r
| Dxxx' => dx*>dx*>dx*>0inf
| Dx1x' => dx*>d1*>dx*>0inf
end.

Inductive RInc: RD -> RD -> Prop :=
| RIncxx1 r r':
    RInc r r' ->
    RInc (Dxx1 r) (Dxx1 r')
| RIncxxx r r':
    RInc r r' ->
    RInc (Dxxx r) (Dxxx r')
| RIncx11 r r':
    RInc r r' ->
    RInc (Dx11 r) (Dx11 r')
| RIncx1x r r':
    RInc r r' ->
    RInc (Dx1x r) (Dx1x r')
| RIncxx1Z r:
    RInc (Dxx1 (DZ r)) (Dxxx r)
| RIncxxxZ r r':
    RInc r r' ->
    RInc (Dxxx (DZ r)) (Dx11 r')
| RIncx11Z r:
    RInc (Dx11 (DZ r)) (Dx1x r)
| RIncx1xZ r r':
    RInc r r' ->
    RInc (Dx1x (DZ r)) (DZ (Dxx1 r'))
| RIncxxx':
    RInc Dxxx' Dx1x'
| RIncx1x':
    RInc Dx1x' (DZ Dxxx')
.

Inductive RWF: RD->Prop :=
| RWFxx1 r: RWF r -> RWF (Dxx1 r)
| RWFxxx r: RWF r -> RWF (Dxxx r)
| RWFx11 r: RWF r -> RWF (Dx11 r)
| RWFx1x r: RWF r -> RWF (Dx1x r)
| RWFxx1Z r: RWF r -> RWF (Dxx1 (DZ r))
| RWFxxxZ r: RWF r -> RWF (Dxxx (DZ r))
| RWFx11Z r: RWF r -> RWF (Dx11 (DZ r))
| RWFx1xZ r: RWF r -> RWF (Dx1x (DZ r))
| RWFxxx': RWF Dxxx'
| RWFx1x': RWF Dx1x'
.

Lemma RInc_spec x x':
  RInc x x' ->
  forall l,
  l |> Rmp x -->* l <| Rmp x'.
Proof.
  intros HR.
  induction HR; intros; cbn in *.
  all: es; er; follow IHHR; es.
Qed.

Lemma RInc_WF' x:
  RWF x ->
  exists x', RInc x x'.
Proof.
  intros HW.
  induction HW.
  all: try destruct IHHW;
    eexists;
    solve [econstructor; eauto].
Qed.

Inductive RWFZ: RD->Prop :=
| RWFZ_intro r: RWF r -> RWFZ (DZ r)
.

Ltac solve_RWF :=
  left;
  solve [econstructor; eauto].

Lemma RInc_WF x x':
  RInc x x' ->
  RWF x ->
  (RWF x' \/ RWFZ x').
Proof.
  intros HI.
  induction HI; intros.
  1-4: inverts H; [ | inverts HI ];
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ];
    [ solve_RWF 
    | inverts HZ; solve_RWF
    ].
  - inverts H.
    1: inverts H1.
    solve_RWF.
  - inverts H.
    1: inverts H1.
    destruct (IHHI H1) as [HW|HZ].
    + right.
      do 2 econstructor; eauto.
    + inverts HZ.
      right.
      solve [do 2 econstructor; apply H].
  - left; constructor.
  - right; do 2 constructor.
Qed.

Definition S0 x := 0inf <* <[1;0] |> Rmp x.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 Dxxx').
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=RWF).
  2: constructor.
  intros x HW.
  epose proof (RInc_WF' _ HW) as [x' HI].
  eexists (Dxxx x').
  split.
  1: unfold S0; follow RInc_spec; es.
  epose proof (RInc_WF _ _ HI HW) as [HW'|HZ].
  - constructor; eauto.
  - inverts HZ.
    solve[constructor; eauto].
Qed.

End TM7.


