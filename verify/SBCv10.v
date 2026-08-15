From BusyCoq Require Import Individual62 ES_v3.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Module Macro.

Inductive signal := Hash | At.
Inductive phase := P0 | P1.

Inductive cstate :=
| C_RD (n:nat)
| C_RD1 (m n:nat)
| C_RD2 (n:nat).

Inductive estate :=
| E_RH (n:nat) (i:phase)
| E_RH1 (m n:nat) (i:phase)
| E_RH2 (n:nat) (i:phase)
| E_RH3 (a:nat).

Inductive net :=
| NEdge (e:estate)
| NCol (c:cstate) (r:net).

Definition col_step (x:signal) (c:cstate)
  : option (cstate * list signal) :=
match x,c with
| Hash,C_RD n => Some (C_RD (n+2),[Hash;Hash;Hash])
| At,C_RD O => None
| At,C_RD (S n) => Some (C_RD2 n,[Hash])
| Hash,C_RD2 n => Some (C_RD1 0 n,[])
| At,C_RD2 _ => None
| Hash,C_RD1 m O => Some (C_RD (m+2),[At;Hash;Hash])
| Hash,C_RD1 m 1 => Some (C_RD (m+2),[At;Hash])
| Hash,C_RD1 m 2 => Some (C_RD (m+2),[At])
| Hash,C_RD1 m (S (S (S n))) => Some (C_RD1 (m+2) n,[])
| At,C_RD1 _ _ => None
end.

Definition edge_step (x:signal) (e:estate) : option net :=
match x,e with
| Hash,E_RH n P0 => Some (NEdge (E_RH n P1))
| Hash,E_RH n P1 => Some (NEdge (E_RH (n+1) P0))
| At,E_RH O P0 => None
| At,E_RH 1 P0 => None
| At,E_RH (S (S n)) P0 => Some (NEdge (E_RH2 n P1))
| At,E_RH O P1 => None
| At,E_RH (S n) P1 => Some (NEdge (E_RH2 n P0))
| Hash,E_RH2 n i => Some (NEdge (E_RH1 0 n i))
| At,E_RH2 _ _ => None
| Hash,E_RH1 m O P0 => Some (NEdge (E_RH (m+2) P0))
| Hash,E_RH1 m 1 P0 => Some (NEdge (E_RH (m+2) P1))
| Hash,E_RH1 m 2 P0 => Some (NEdge (E_RH (m+3) P0))
| Hash,E_RH1 m (S (S (S n))) i =>
    Some (NEdge (E_RH1 (m+2) n i))
| Hash,E_RH1 m O P1 =>
    Some (NCol (C_RD (m+2)) (NEdge (E_RH 1 P0)))
| Hash,E_RH1 m 1 P1 =>
    Some (NCol (C_RD (m+2)) (NEdge (E_RH 0 P1)))
| Hash,E_RH1 m 2 P1 => Some (NEdge (E_RH3 m))
| At,E_RH1 _ _ _ => None
| Hash,E_RH3 a =>
    Some (NCol (C_RD (a+4)) (NEdge (E_RH 1 P1)))
| At,E_RH3 _ => None
end.

Inductive Push : list signal -> net -> net -> Prop :=
| push_nil n: Push [] n n
| push_cons x xs n n1 n2:
    Push1 x n n1 ->
    Push xs n1 n2 ->
    Push (x::xs) n n2
with Push1 : signal -> net -> net -> Prop :=
| push1_edge x e n:
    edge_step x e = Some n ->
    Push1 x (NEdge e) n
| push1_col x c c' ys n n':
    col_step x c = Some (c',ys) ->
    Push ys n n' ->
    Push1 x (NCol c n) (NCol c' n').

Scheme Push_ind' := Induction for Push Sort Prop
with Push1_ind' := Induction for Push1 Sort Prop.
Combined Scheme Push_Push1_ind from Push_ind', Push1_ind'.

Fixpoint col_run (xs:list signal) (c:cstate)
  : option (cstate * list signal) :=
match xs with
| [] => Some (c,[])
| x::xs =>
    match col_step x c with
    | None => None
    | Some (c1,ys) =>
        match col_run xs c1 with
        | None => None
        | Some (c2,zs) => Some (c2,ys++zs)
        end
    end
end.

Fixpoint eat (xs:list signal) (p A:nat) : option (nat*nat) :=
match xs with
| [] => Some (p,A)
| Hash::xs =>
    match p with
    | O => None
    | S p => eat xs p A
    end
| At::xs =>
    match p with
    | O => eat xs A (2*A)
    | S _ => None
    end
end.

Definition prefixW p A xs := exists p' A', eat xs p A = Some (p',A').

Fixpoint countO (xs:list signal) : nat :=
match xs with
| [] => 0
| Hash::xs => countO xs
| At::xs => S (countO xs)
end.

Definition pending (c:cstate) : nat :=
match c with
| C_RD _ => O
| _ => S O
end.

Definition Safe n p A :=
  forall xs, prefixW p A xs -> exists n', Push xs n n'.

Definition ColMap c p A op OA :=
  forall xs p' A',
  eat xs p A = Some (p',A') ->
  exists c' ys op' OA',
    col_run xs c = Some (c',ys) /\
    eat ys op OA = Some (op',OA').

Lemma eat_app xs ys p A p' A':
  eat xs p A = Some (p',A') ->
  eat (xs++ys) p A = eat ys p' A'.
Proof.
  revert p A p' A'.
  induction xs as [|x xs IH]; intros p A p' A' E.
  - cbn in E. inversion E; reflexivity.
  - destruct x, p; cbn in E |- *; try discriminate;
      eapply IH; exact E.
Qed.

Lemma eat_cons_inv x xs p A p' A':
  eat (x::xs) p A = Some (p',A') ->
  exists p1 A1,
    eat [x] p A = Some (p1,A1) /\
    eat xs p1 A1 = Some (p',A').
Proof.
  destruct x, p; cbn; intros E; try discriminate.
  - eexists; eexists; split; [reflexivity|exact E].
  - eexists; eexists; split; [reflexivity|exact E].
Qed.

Lemma Push_app xs ys n n1 n2:
  Push xs n n1 -> Push ys n1 n2 -> Push (xs++ys) n n2.
Proof.
  intros H. induction H; cbn; intros Hys.
  - exact Hys.
  - econstructor; eauto.
Qed.

Lemma Push_app_inv xs ys n n2:
  Push (xs++ys) n n2 ->
  exists n1, Push xs n n1 /\ Push ys n1 n2.
Proof.
  revert n n2.
  induction xs as [|x xs IH]; cbn; intros n n2 H.
  - exists n; split; [constructor|exact H].
  - inversion H; subst.
    destruct (IH _ _ H5) as (n3&Hxs&Hys).
    exists n3; split; [econstructor; eauto|exact Hys].
Qed.

Lemma Push_deterministic:
  (forall xs n n1 (H:Push xs n n1),
      forall n2, Push xs n n2 -> n1=n2) /\
  (forall x n n1 (H:Push1 x n n1),
      forall n2, Push1 x n n2 -> n1=n2).
Proof.
  apply Push_Push1_ind.
  - intros n n2 H. inversion H. reflexivity.
  - intros x xs n n1 n2 Hx IHx Hxs IHxs n3 H.
    inversion H as [|x' xs' n' n1' n2' Hx' Hxs']; subst.
    assert (n1=n1') by (eapply IHx; eauto).
    subst n1'. eapply IHxs; eauto.
  - intros x e n E n2 H.
    inversion H; subst. congruence.
  - intros x c c' ys n n' E Hys IH n2 H.
    inversion H; subst.
    match goal with
    | E': col_step x c = Some (?d,?zs) |- _ =>
        rewrite E in E'; inversion E'; subst
    end.
    f_equal. eapply IH; eauto.
Qed.

Lemma Push_functional xs n n1 n2:
  Push xs n n1 -> Push xs n n2 -> n1=n2.
Proof.
  intros H. eapply (proj1 Push_deterministic); eauto.
Qed.

Lemma Safe_suffix n p A xs p' A' n':
  Safe n p A ->
  eat xs p A = Some (p',A') ->
  Push xs n n' ->
  Safe n' p' A'.
Proof.
  intros HS E HP ys [q [B EY]].
  assert (prefixW p A (xs++ys)) as HW.
  { exists q,B. rewrite (eat_app _ _ _ _ _ _ E). exact EY. }
  destruct (HS _ HW) as (n2&HAll).
  destruct (Push_app_inv _ _ _ _ HAll) as (n1&Hxs&Hys).
  assert (n'=n1) by (eapply Push_functional; eauto).
  subst n1. eauto.
Qed.

Lemma Push_col_run xs c c' ys n n':
  col_run xs c = Some (c',ys) ->
  Push ys n n' ->
  Push xs (NCol c n) (NCol c' n').
Proof.
  revert c c' ys n n'.
  induction xs as [|x xs IH]; cbn; intros c c' ys n n' E HP.
  - inversion E; subst. inversion HP; subst. constructor.
  - destruct (col_step x c) as [[c1 zs]|] eqn:Ex; try discriminate.
    destruct (col_run xs c1) as [[c2 us]|] eqn:Exs; try discriminate.
    inversion E; subst c2 ys.
    destruct (Push_app_inv _ _ _ _ HP) as (n1&Hzs&Hus).
    econstructor.
    + econstructor; eauto.
    + eapply IH; eauto.
Qed.

Inductive ColInv : cstate -> nat -> nat -> nat -> nat -> Prop :=
| CI_RD r p A:
    r + 2*p + 2 = A -> 3 <= A ->
    ColInv (C_RD r) p A (3*p+1) (2*A)
| CI_RD2 n:
    ColInv (C_RD2 n) (n+3) (2*n+6) 0 (2*n+6)
| CI_RD1 m n:
    ColInv (C_RD1 m n) (m+n+2) (2*n+3*m+6) 0 (2*n+3*m+6).

Lemma ColInv_step x c p A op OA p' A':
  eat [x] p A = Some (p',A') ->
  ColInv c p A op OA ->
  exists c' ys op' OA',
    col_step x c = Some (c',ys) /\
    eat ys op OA = Some (op',OA') /\
    ColInv c' p' A' op' OA'.
Proof.
  intros Ex I. inversion I; subst.
  - destruct x.
    + destruct p as [|p0]; cbn in Ex; try discriminate.
      inversion Ex; subst p' A'.
      exists (C_RD (r+2)),[Hash;Hash;Hash],(3*p0+1),
        (2*(r+2*S p0+2)).
      split; [reflexivity|]. split.
      { replace (3*S p0+1) with (S (S (S (3*p0+1)))) by lia.
        cbn. reflexivity. }
      eapply CI_RD; lia.
    + destruct p as [|p0]; cbn in Ex; try discriminate.
      inversion Ex; subst p' A'. destruct r as [|r0]; [lia|].
      exists (C_RD2 r0),[Hash],O,(2*(S r0+2)).
      split; [reflexivity|]. split.
      { cbn. repeat rewrite <- plus_n_O. reflexivity. }
      replace (S r0+O+2) with (r0+3) by lia.
      replace (r0+3+(r0+3+O)) with (2*r0+6) by lia.
      replace (2*(S r0+2)) with (2*r0+6) by lia.
      apply CI_RD2.
  - destruct x.
    + replace (n+3) with (S (n+2)) in Ex by lia.
      cbn in Ex. inversion Ex; subst p' A'.
      exists (C_RD1 O n),(@nil signal),O,(2*n+6).
      split; [reflexivity|]. split; [reflexivity|].
      replace (n+(n+O)+6) with (2*n+6) by lia.
      replace (n+2) with (O+n+2) by lia.
      replace (2*n+6) with (2*n+3*O+6) by lia.
      exact (CI_RD1 O n).
    + replace (n+3) with (S (n+2)) in Ex by lia.
      cbn in Ex. discriminate.
  - destruct x.
    2: { replace (m+n+2) with (S (m+n+1)) in Ex by lia.
         cbn in Ex. discriminate. }
    replace (m+n+2) with (S (m+n+1)) in Ex by lia.
    cbn in Ex. inversion Ex; subst p' A'.
    destruct n as [|[|[|n]]].
    + exists (C_RD (m+2)),[At;Hash;Hash],(3*(m+1)+1),(2*(3*m+6)).
      split; [reflexivity|]. split.
      { change (eat [At;Hash;Hash] O (3*m+6) =
          Some (3*(m+1)+1,2*(3*m+6))).
        assert (EM: 3*m+6 = S (S (3*m+4))) by lia.
        assert (EP: 3*(m+1)+1 = 3*m+4) by lia.
        rewrite EM,EP. cbn. reflexivity. }
      replace (m+O+1) with (m+1) by lia.
      replace (O+(O+O)+(m+(m+(m+O)))+6) with (3*m+6) by lia.
      apply CI_RD; lia.
    + exists (C_RD (m+2)),[At;Hash],(3*(m+2)+1),(2*(3*m+8)).
      split; [reflexivity|]. split.
      { assert (EM: 2*1+3*m+6 = S (3*m+7)) by lia.
        assert (EP: 3*(m+2)+1 = 2*1+3*m+5) by lia.
        assert (ER: 2*1+3*m+5 = 3*m+7) by lia.
        assert (EOA: 2*(3*m+8) = 2*(2*1+3*m+6)) by lia.
        rewrite EOA,EP,ER,EM. cbn. reflexivity. }
      replace (m+1+1) with (m+2) by lia.
      replace (1+(1+O)+(m+(m+(m+O)))+6) with (3*m+8) by lia.
      apply CI_RD; lia.
    + exists (C_RD (m+2)),[At],(3*(m+3)+1),(2*(3*m+10)).
      split; [reflexivity|]. split.
      { assert (EP: 3*(m+3)+1 = 2*2+3*m+6) by lia.
        assert (EOA: 2*(3*m+10) = 2*(2*2+3*m+6)) by lia.
        rewrite EOA,EP. cbn. reflexivity. }
      replace (m+2+1) with (m+3) by lia.
      replace (2+(2+O)+(m+(m+(m+O)))+6) with (3*m+10) by lia.
      apply CI_RD; lia.
    + exists (C_RD1 (m+2) n),(@nil signal),O,(2*n+3*m+12).
      split; [reflexivity|]. split.
      { assert (EA: 2*S (S (S n))+3*m+6 = 2*n+3*m+12) by lia.
        rewrite EA. reflexivity. }
      replace (m+S (S (S n))+1) with ((m+2)+n+2) by lia.
      replace (S (S (S n))+(S (S (S n))+O)+(m+(m+(m+O)))+6)
        with (2*n+3*(m+2)+6) by lia.
      replace (2*n+3*m+12) with (2*n+3*(m+2)+6) by lia.
      exact (CI_RD1 (m+2) n).
Qed.

Lemma ColInv_run xs c p A op OA p' A':
  eat xs p A = Some (p',A') ->
  ColInv c p A op OA ->
  exists c' ys op' OA',
    col_run xs c = Some (c',ys) /\
    eat ys op OA = Some (op',OA') /\
    ColInv c' p' A' op' OA'.
Proof.
  revert c p A op OA p' A'.
  induction xs as [|x xs IH]; intros c p A op OA p' A' E I.
  - cbn in E. inversion E; subst.
    exists c,(@nil signal),op,OA.
    split; [reflexivity|]. split; [reflexivity|exact I].
  - destruct (eat_cons_inv _ _ _ _ _ _ E) as (p1&A1&Ex&Es).
    destruct (ColInv_step _ _ _ _ _ _ _ _ Ex I)
      as (c1&ys&op1&OA1&Ec&Eout&I1).
    destruct (IH _ _ _ _ _ _ _ Es I1)
      as (c2&zs&op2&OA2&Erun&Ez&I2).
    exists c2,(ys++zs),op2,OA2.
    split.
    + cbn. rewrite Ec,Erun. reflexivity.
    + split.
      * rewrite (eat_app _ _ _ _ _ _ Eout). exact Ez.
      * exact I2.
Qed.

Lemma ColMap_RD r p A:
  r + 2*p + 2 = A -> 3 <= A ->
  ColMap (C_RD r) p A (3*p+1) (2*A).
Proof.
  intros Er EA xs p' A' E.
  destruct (ColInv_run _ _ _ _ _ _ _ _ E (CI_RD _ _ _ Er EA))
    as (c'&ys&op'&OA'&Erun&Eout&_).
  eauto 8.
Qed.

Lemma ColMap_safe c p A op OA n:
  ColMap c p A op OA -> Safe n op OA -> Safe (NCol c n) p A.
Proof.
  intros CM HS xs [p' [A' E]].
  destruct (CM _ _ _ E) as (c'&ys&op'&OA'&Erun&Eout).
  destruct (HS ys) as (n'&HP).
  { exists op',OA'. exact Eout. }
  exists (NCol c' n'). eapply Push_col_run; eauto.
Qed.

Definition hashes n : list signal := repeat Hash n.
Definition block p c := hashes p ++ At :: hashes c.

Lemma hashes_add a b:
  hashes (a+b) = hashes a ++ hashes b.
Proof.
  unfold hashes. induction a; cbn; congruence.
Qed.

Lemma hashes_split k p:
  k <= p -> exists zs, hashes p = hashes k ++ zs.
Proof.
  intros H. exists (hashes (p-k)).
  replace p with (k+(p-k)) at 1 by lia. apply hashes_add.
Qed.

Lemma countO_hashes n: countO (hashes n) = O.
Proof. induction n; cbn; auto. Qed.

Lemma countO_app xs ys:
  countO (xs++ys) = countO xs + countO ys.
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|].
  destruct x; cbn; rewrite IH; lia.
Qed.

Lemma Push_prefix xs zs n n':
  Push (xs++zs) n n' -> exists n1, Push xs n n1.
Proof.
  intros H. destruct (Push_app_inv _ _ _ _ H) as (n1&H1&_).
  eauto.
Qed.

Lemma eat_prefix p A xs p' A':
  eat xs p A = Some (p',A') ->
  (exists k, k <= p /\ xs = hashes k) \/
  (exists ys, xs = hashes p ++ At::ys /\
              eat ys A (2*A) = Some (p',A')).
Proof.
  revert xs p' A'. induction p as [|p IH]; intros xs p' A' E.
  - destruct xs as [|x xs].
    + left. exists O. split; [lia|reflexivity].
    + destruct x; cbn in E.
      * discriminate.
      * right. exists xs. cbn. split; [reflexivity|exact E].
  - destruct xs as [|x xs].
    + left. exists O. split; [lia|reflexivity].
    + destruct x; cbn in E.
      * destruct (IH _ _ _ E) as [(k&Hk&Ek)|(ys&Ey&ER)].
        -- left. exists (S k). cbn. split; [lia|now rewrite Ek].
        -- right. exists ys. cbn. split; [now rewrite Ey|exact ER].
      * discriminate.
Qed.

Lemma eat_cut_hash c p A xs p' A':
  c <= p -> eat xs p A = Some (p',A') ->
  (exists k, k < c /\ xs = hashes k) \/
  (exists ys, xs = hashes c ++ ys /\
              eat ys (p-c) A = Some (p',A')).
Proof.
  revert p xs p' A'.
  induction c as [|c IH]; intros p xs p' A' Hcp E.
  - right. exists xs. cbn. split; [reflexivity|].
    replace (p-O) with p by lia. exact E.
  - destruct p as [|p]; [lia|]. destruct xs as [|x xs].
    + left. exists O. cbn. auto with arith.
    + destruct x; cbn in E.
      * destruct (IH p xs p' A') as [(k&Hk&Ek)|(ys&Ey&ER)];
          try lia; auto.
        -- left. exists (S k). cbn. split; [lia|now rewrite Ek].
        -- right. exists ys. cbn. split; [now rewrite Ey|].
           replace (S p-S c) with (p-c) by lia. exact ER.
      * discriminate.
Qed.

Definition SafeN d n p A :=
  forall xs, countO xs <= d -> prefixW p A xs ->
  exists n', Push xs n n'.

Lemma SafeN_zero_of_block n n' p A c:
  Push (block p c) n n' -> SafeN 0 n p A.
Proof.
  intros HB xs HC [p' [A' E]].
  destruct (eat_prefix _ _ _ _ _ E) as [(k&Hk&->)|(ys&->&Ey)].
  - destruct (hashes_split _ _ Hk) as (zs&Ep).
    unfold block in HB. rewrite Ep,<-app_assoc in HB.
    eapply Push_prefix; exact HB.
  - rewrite countO_app,countO_hashes in HC. cbn in HC. lia.
Qed.

Lemma SafeN_block d n n' p A c:
  c <= A ->
  Push (block p c) n n' ->
  SafeN d n' (A-c) (2*A) ->
  SafeN (S d) n p A.
Proof.
  intros Hc HB HS xs HC [p' [A' E]].
  destruct (eat_prefix _ _ _ _ _ E) as [(k&Hk&->)|(ys&->&Ey)].
  - destruct (hashes_split _ _ Hk) as (zs&Ep).
    unfold block in HB. rewrite Ep,<-app_assoc in HB.
    eapply Push_prefix; exact HB.
  - destruct (eat_cut_hash _ _ _ _ _ _ Hc Ey)
      as [(k&Hk&->)|(zs&->&Ez)].
    + destruct (hashes_split _ _ (Nat.lt_le_incl _ _ Hk)) as (us&Ec).
      change (Push (hashes p ++ At::hashes c) n n') in HB.
      rewrite Ec in HB.
      change (Push (hashes p ++ ((At::hashes k)++us)) n n') in HB.
      rewrite app_assoc in HB.
      eapply Push_prefix; exact HB.
    + destruct (HS zs) as (n2&Hzs).
      { rewrite countO_app,countO_hashes in HC. cbn in HC.
        rewrite countO_app,countO_hashes in HC. cbn in HC. lia. }
      { exists p',A'. exact Ez. }
      exists n2.
      change (Push (hashes p ++ ((At::hashes c)++zs)) n n2).
      rewrite app_assoc.
      eapply Push_app; eauto.
Qed.

Lemma col_step_count x c c' ys:
  col_step x c = Some (c',ys) ->
  countO ys + pending c' = countO [x] + pending c.
Proof.
  destruct x; destruct c as [n|m n|n]; cbn; intros E.
  - inversion E; subst. cbn. lia.
  - destruct n as [|[|[|n]]]; cbn in E; inversion E; subst; cbn; lia.
  - inversion E; subst. cbn. lia.
  - destruct n; cbn in E; try discriminate. inversion E; subst; cbn; lia.
  - discriminate.
  - discriminate.
Qed.

Lemma col_run_count xs c c' ys:
  col_run xs c = Some (c',ys) ->
  countO ys + pending c' = countO xs + pending c.
Proof.
  revert c c' ys. induction xs as [|x xs IH]; cbn;
    intros c c' ys E.
  - inversion E; subst. cbn. lia.
  - destruct (col_step x c) as [[c1 zs]|] eqn:Ex; try discriminate.
    destruct (col_run xs c1) as [[c2 us]|] eqn:ER; try discriminate.
    inversion E; subst c2 ys. rewrite countO_app.
    pose proof (col_step_count _ _ _ _ Ex).
    pose proof (IH _ _ _ ER). destruct x; cbn in *; lia.
Qed.

Lemma ColMap_safeN_RD d r p A op OA n:
  ColMap (C_RD r) p A op OA ->
  SafeN d n op OA -> SafeN d (NCol (C_RD r) n) p A.
Proof.
  intros CM HS xs HC [p' [A' E]].
  destruct (CM _ _ _ E) as (c'&ys&op'&OA'&Erun&Eout).
  destruct (HS ys) as (n'&HP).
  { pose proof (col_run_count _ _ _ _ Erun). cbn in H. lia. }
  { exists op',OA'. exact Eout. }
  exists (NCol c' n'). eapply Push_col_run; eauto.
Qed.

Lemma Push_one x e n:
  edge_step x e = Some n -> Push [x] (NEdge e) n.
Proof.
  intros E. econstructor.
  - econstructor; exact E.
  - constructor.
Qed.

Lemma Push_RH_pair n i:
  Push [Hash;Hash] (NEdge (E_RH n i)) (NEdge (E_RH (n+1) i)).
Proof.
  destruct i.
  - change (Push ([Hash]++[Hash]) (NEdge (E_RH n P0))
      (NEdge (E_RH (n+1) P0))).
    eapply Push_app with (n1:=NEdge (E_RH n P1));
      apply Push_one; cbn; reflexivity.
  - change (Push ([Hash]++[Hash]) (NEdge (E_RH n P1))
      (NEdge (E_RH (n+1) P1))).
    eapply Push_app with (n1:=NEdge (E_RH (n+1) P0));
      apply Push_one; cbn; reflexivity.
Qed.

Lemma Push_RH_even k n i:
  Push (hashes (2*k)) (NEdge (E_RH n i))
       (NEdge (E_RH (n+k) i)).
Proof.
  revert n. induction k as [|k IH]; intros n.
  - cbn. replace (n+O) with n by lia. constructor.
  - replace (2*S k) with (2+2*k) by lia.
    rewrite hashes_add. replace (n+S k) with ((n+1)+k) by lia.
    eapply Push_app; [apply Push_RH_pair|apply IH].
Qed.

Lemma Push_RH_odd0 k n:
  Push (hashes (2*k+1)) (NEdge (E_RH n P0))
       (NEdge (E_RH (n+k) P1)).
Proof.
  replace (2*k+1) with (2*k+1) by lia.
  rewrite hashes_add. eapply Push_app.
  - apply Push_RH_even.
  - apply Push_one. cbn. reflexivity.
Qed.

Lemma Push_RH_odd1 k n:
  Push (hashes (2*k+1)) (NEdge (E_RH n P1))
       (NEdge (E_RH (n+k+1) P0)).
Proof.
  rewrite hashes_add. eapply Push_app.
  - apply Push_RH_even.
  - apply Push_one. cbn. reflexivity.
Qed.

Lemma Push_RH1_incs q m r i:
  Push (hashes q) (NEdge (E_RH1 m (3*q+r) i))
       (NEdge (E_RH1 (m+2*q) r i)).
Proof.
  revert m. induction q as [|q IH]; intros m.
  - cbn. replace (m+O) with m by lia. constructor.
  - cbn [hashes].
    replace (3*S q+r) with (S (S (S (3*q+r)))) by lia.
    replace (m+2*S q) with ((m+2)+2*q) by lia.
    change (Push ([Hash]++hashes q)
      (NEdge (E_RH1 m (S (S (S (3*q+r)))) i))
      (NEdge (E_RH1 (m+2+2*q) r i))).
    eapply Push_app with
      (n1:=NEdge (E_RH1 (m+2) (3*q+r) i)).
    + apply Push_one. cbn. reflexivity.
    + apply IH.
Qed.

Lemma hashes_plus2 q:
  hashes (q+2) = Hash :: hashes q ++ [Hash].
Proof.
  replace (q+2) with (1+q+1) by lia.
  rewrite hashes_add,hashes_add. reflexivity.
Qed.

Lemma hashes_plus3 q:
  hashes (q+3) = Hash :: hashes q ++ [Hash;Hash].
Proof.
  replace (q+3) with (1+q+2) by lia.
  rewrite hashes_add,hashes_add. reflexivity.
Qed.

Lemma Cleanup_P0_0 q:
  Push (At::hashes (q+2)) (NEdge (E_RH (3*q+2) P0))
    (NCol (C_RD (2*q+2)) (NEdge (E_RH 1 P0))).
Proof.
  rewrite hashes_plus2.
  change (Push ([At;Hash]++(hashes q++[Hash]))
    (NEdge (E_RH (3*q+2) P0))
    (NCol (C_RD (2*q+2)) (NEdge (E_RH 1 P0)))).
  eapply Push_app with (n1:=NEdge (E_RH1 O (3*q) P1)).
  - change (Push ([At]++[Hash]) (NEdge (E_RH (3*q+2) P0))
      (NEdge (E_RH1 O (3*q) P1))).
    eapply Push_app with (n1:=NEdge (E_RH2 (3*q) P1));
      apply Push_one.
    + replace (3*q+2) with (S (S (3*q))) by lia. cbn. reflexivity.
    + reflexivity.
  - eapply Push_app with (n1:=NEdge (E_RH1 (2*q) O P1)).
    + replace (3*q) with (3*q+O) by lia.
      replace (2*q) with (O+2*q) by lia. apply Push_RH1_incs.
    + apply Push_one. reflexivity.
Qed.

Lemma Cleanup_P0_1 q:
  Push (At::hashes (q+2)) (NEdge (E_RH (3*q+3) P0))
    (NCol (C_RD (2*q+2)) (NEdge (E_RH O P1))).
Proof.
  rewrite hashes_plus2.
  change (Push ([At;Hash]++(hashes q++[Hash]))
    (NEdge (E_RH (3*q+3) P0))
    (NCol (C_RD (2*q+2)) (NEdge (E_RH O P1)))).
  eapply Push_app with (n1:=NEdge (E_RH1 O (3*q+1) P1)).
  - change (Push ([At]++[Hash]) (NEdge (E_RH (3*q+3) P0))
      (NEdge (E_RH1 O (3*q+1) P1))).
    eapply Push_app with (n1:=NEdge (E_RH2 (3*q+1) P1));
      apply Push_one.
    + replace (3*q+3) with (S (S (3*q+1))) by lia. cbn. reflexivity.
    + reflexivity.
  - eapply Push_app with (n1:=NEdge (E_RH1 (2*q) 1 P1)).
    + replace (2*q) with (O+2*q) by lia. apply Push_RH1_incs.
    + apply Push_one. reflexivity.
Qed.

Lemma Cleanup_P0_2 q:
  Push (At::hashes (q+3)) (NEdge (E_RH (3*q+4) P0))
    (NCol (C_RD (2*q+4)) (NEdge (E_RH 1 P1))).
Proof.
  rewrite hashes_plus3.
  change (Push ([At;Hash]++(hashes q++[Hash;Hash]))
    (NEdge (E_RH (3*q+4) P0))
    (NCol (C_RD (2*q+4)) (NEdge (E_RH 1 P1)))).
  eapply Push_app with (n1:=NEdge (E_RH1 O (3*q+2) P1)).
  - change (Push ([At]++[Hash]) (NEdge (E_RH (3*q+4) P0))
      (NEdge (E_RH1 O (3*q+2) P1))).
    eapply Push_app with (n1:=NEdge (E_RH2 (3*q+2) P1));
      apply Push_one.
    + replace (3*q+4) with (S (S (3*q+2))) by lia. cbn. reflexivity.
    + reflexivity.
  - eapply Push_app with (n1:=NEdge (E_RH1 (2*q) 2 P1)).
    + replace (2*q) with (O+2*q) by lia. apply Push_RH1_incs.
    + change (Push ([Hash]++[Hash]) (NEdge (E_RH1 (2*q) 2 P1))
        (NCol (C_RD (2*q+4)) (NEdge (E_RH 1 P1)))).
      eapply Push_app with (n1:=NEdge (E_RH3 (2*q))).
      * apply Push_one. reflexivity.
      * apply Push_one. reflexivity.
Qed.

Lemma Cleanup_P1_0 q:
  Push (At::hashes (q+2)) (NEdge (E_RH (3*q+1) P1))
    (NEdge (E_RH (2*q+2) P0)).
Proof.
  rewrite hashes_plus2.
  change (Push ([At;Hash]++(hashes q++[Hash]))
    (NEdge (E_RH (3*q+1) P1)) (NEdge (E_RH (2*q+2) P0))).
  eapply Push_app with (n1:=NEdge (E_RH1 O (3*q) P0)).
  - change (Push ([At]++[Hash]) (NEdge (E_RH (3*q+1) P1))
      (NEdge (E_RH1 O (3*q) P0))).
    eapply Push_app with (n1:=NEdge (E_RH2 (3*q) P0));
      apply Push_one.
    + replace (3*q+1) with (S (3*q)) by lia.
      remember (3*q) as t. destruct t; reflexivity.
    + reflexivity.
  - eapply Push_app with (n1:=NEdge (E_RH1 (2*q) O P0)).
    + replace (3*q) with (3*q+O) by lia.
      replace (2*q) with (O+2*q) by lia. apply Push_RH1_incs.
    + apply Push_one. reflexivity.
Qed.

Lemma Cleanup_P1_2 q:
  Push (At::hashes (q+2)) (NEdge (E_RH (3*q+3) P1))
    (NEdge (E_RH (2*q+3) P0)).
Proof.
  rewrite hashes_plus2.
  change (Push ([At;Hash]++(hashes q++[Hash]))
    (NEdge (E_RH (3*q+3) P1)) (NEdge (E_RH (2*q+3) P0))).
  eapply Push_app with (n1:=NEdge (E_RH1 O (3*q+2) P0)).
  - change (Push ([At]++[Hash]) (NEdge (E_RH (3*q+3) P1))
      (NEdge (E_RH1 O (3*q+2) P0))).
    eapply Push_app with (n1:=NEdge (E_RH2 (3*q+2) P0));
      apply Push_one.
    + replace (3*q+3) with (S (3*q+2)) by lia.
      remember (3*q+2) as t. destruct t; reflexivity.
    + reflexivity.
  - eapply Push_app with (n1:=NEdge (E_RH1 (2*q) 2 P0)).
    + replace (2*q) with (O+2*q) by lia. apply Push_RH1_incs.
    + apply Push_one. reflexivity.
Qed.

Lemma T4_initial_block:
  Push (block 1 3) (NEdge (E_RH 4 P1))
    (NCol (C_RD 4) (NEdge (E_RH 1 P0))).
Proof.
  unfold block. change (Push (hashes 1 ++ (At::hashes 3))
    (NEdge (E_RH 4 P1))
    (NCol (C_RD 4) (NEdge (E_RH 1 P0)))).
  eapply Push_app with (n1:=NEdge (E_RH 5 P0)).
  - exact (Push_RH_odd1 O 4).
  - replace 5 with (3*1+2) by lia.
    replace 3 with (1+2) by lia.
    replace 4 with (2*1+2) by lia. apply Cleanup_P0_0.
Qed.

Lemma T4_X_block k:
  Push (block (6*k+4) (k+2))
    (NEdge (E_RH 1 P0))
    (NCol (C_RD (2*k+2)) (NEdge (E_RH O P1))).
Proof.
  unfold block.
  change (Push (hashes (6*k+4) ++ (At::hashes (k+2)))
    (NEdge (E_RH 1 P0))
    (NCol (C_RD (2*k+2)) (NEdge (E_RH O P1)))).
  eapply Push_app with (n1:=NEdge (E_RH (1+(3*k+2)) P0)).
  - replace (6*k+4) with (2*(3*k+2)) by lia. apply Push_RH_even.
  - replace (1+(3*k+2)) with (3*k+3) by lia.
    apply Cleanup_P0_1.
Qed.

Lemma T4_Y_block j:
  Push (block (6*S j+1) (S j+2))
    (NEdge (E_RH O P1))
    (NCol (C_RD (2*S j+2)) (NEdge (E_RH 1 P1))).
Proof.
  unfold block.
  change (Push (hashes (6*S j+1) ++ (At::hashes (S j+2)))
    (NEdge (E_RH O P1))
    (NCol (C_RD (2*S j+2)) (NEdge (E_RH 1 P1)))).
  eapply Push_app with (n1:=NEdge (E_RH (O+(3*j+3)+1) P0)).
  - replace (6*S j+1) with (2*(3*j+3)+1) by lia.
    apply Push_RH_odd1.
  - replace (O+(3*j+3)+1) with (3*j+4) by lia.
    replace (S j+2) with (j+3) by lia.
    replace (2*S j+2) with (2*j+4) by lia.
    apply Cleanup_P0_2.
Qed.

Lemma T4_Z_block k:
  Push (block (6*k+1) (k+2))
    (NEdge (E_RH 1 P1))
    (NCol (C_RD (2*k+2)) (NEdge (E_RH 1 P0))).
Proof.
  unfold block.
  change (Push (hashes (6*k+1) ++ (At::hashes (k+2)))
    (NEdge (E_RH 1 P1))
    (NCol (C_RD (2*k+2)) (NEdge (E_RH 1 P0)))).
  eapply Push_app with (n1:=NEdge (E_RH (1+3*k+1) P0)).
  - replace (6*k+1) with (2*(3*k)+1) by lia. apply Push_RH_odd1.
  - replace (1+3*k+1) with (3*k+2) by lia. apply Cleanup_P0_0.
Qed.

Lemma T5_initial_edge_block:
  Push (block 4 5) (NEdge (E_RH 8 P0))
    (NCol (C_RD 8) (NEdge (E_RH 1 P1))).
Proof.
  unfold block. change (Push (hashes 4 ++ (At::hashes 5))
    (NEdge (E_RH 8 P0))
    (NCol (C_RD 8) (NEdge (E_RH 1 P1)))).
  eapply Push_app with (n1:=NEdge (E_RH (8+2) P0)).
  - replace 4 with (2*2) by lia. apply Push_RH_even.
  - replace (8+2) with (3*2+4) by lia.
    replace 5 with (2+3) by lia.
    replace 8 with (2*2+4) by lia. apply Cleanup_P0_2.
Qed.

Lemma T5_A_block q:
  Push (block (6*q+4) (q+2)) (NEdge (E_RH 1 P1))
    (NEdge (E_RH (2*q+3) P0)).
Proof.
  unfold block. change (Push (hashes (6*q+4) ++ (At::hashes (q+2)))
    (NEdge (E_RH 1 P1)) (NEdge (E_RH (2*q+3) P0))).
  eapply Push_app with (n1:=NEdge (E_RH (1+(3*q+2)) P1)).
  - replace (6*q+4) with (2*(3*q+2)) by lia. apply Push_RH_even.
  - replace (1+(3*q+2)) with (3*q+3) by lia. apply Cleanup_P1_2.
Qed.

Lemma T5_B_block q:
  Push (block (8*q+9) (2*q+4)) (NEdge (E_RH (2*q+3) P0))
    (NEdge (E_RH (4*q+6) P0)).
Proof.
  unfold block. change (Push (hashes (8*q+9) ++ (At::hashes (2*q+4)))
    (NEdge (E_RH (2*q+3) P0)) (NEdge (E_RH (4*q+6) P0))).
  eapply Push_app with
    (n1:=NEdge (E_RH ((2*q+3)+(4*q+4)) P1)).
  - replace (8*q+9) with (2*(4*q+4)+1) by lia. apply Push_RH_odd0.
  - replace ((2*q+3)+(4*q+4)) with (3*(2*q+2)+1) by lia.
    replace (2*q+4) with ((2*q+2)+2) by lia.
    replace (4*q+6) with (2*(2*q+2)+2) by lia.
    apply Cleanup_P1_0.
Qed.

Lemma T5_C_block q:
  Push (block (16*q+18) (4*q+6)) (NEdge (E_RH (4*q+6) P0))
    (NCol (C_RD (8*q+10)) (NEdge (E_RH O P1))).
Proof.
  unfold block. change (Push (hashes (16*q+18) ++ (At::hashes (4*q+6)))
    (NEdge (E_RH (4*q+6) P0))
    (NCol (C_RD (8*q+10)) (NEdge (E_RH O P1)))).
  eapply Push_app with
    (n1:=NEdge (E_RH ((4*q+6)+(8*q+9)) P0)).
  - replace (16*q+18) with (2*(8*q+9)) by lia. apply Push_RH_even.
  - replace ((4*q+6)+(8*q+9)) with (3*(4*q+4)+3) by lia.
    replace (8*q+10) with (2*(4*q+4)+2) by lia.
    replace (4*q+6) with ((4*q+4)+2) by lia.
    apply Cleanup_P0_1.
Qed.

Lemma T5_D_block q:
  Push (block (96*q+115) (16*q+21)) (NEdge (E_RH O P1))
    (NCol (C_RD (32*q+40)) (NEdge (E_RH 1 P1))).
Proof.
  unfold block. change (Push (hashes (96*q+115) ++ (At::hashes (16*q+21)))
    (NEdge (E_RH O P1))
    (NCol (C_RD (32*q+40)) (NEdge (E_RH 1 P1)))).
  eapply Push_app with
    (n1:=NEdge (E_RH (O+(48*q+57)+1) P0)).
  - replace (96*q+115) with (2*(48*q+57)+1) by lia.
    apply Push_RH_odd1.
  - replace (O+(48*q+57)+1) with (3*(16*q+18)+4) by lia.
    replace (32*q+40) with (2*(16*q+18)+4) by lia.
    replace (16*q+21) with ((16*q+18)+3) by lia.
    apply Cleanup_P0_2.
Qed.

Lemma Safe_of_all_SafeN n p A:
  (forall d, SafeN d n p A) -> Safe n p A.
Proof.
  intros H xs HW. eapply H with (d:=countO xs); eauto.
Qed.

Lemma T4_cycles_safeN d:
  (forall k, SafeN d (NEdge (E_RH 1 P0)) (6*k+4) (9*k+10)) /\
  (forall j, SafeN d (NEdge (E_RH O P1)) (6*S j+1) (9*S j+4)) /\
  (forall k, SafeN d (NEdge (E_RH 1 P1)) (6*k+1) (9*k+7)).
Proof.
  induction d as [|d IH].
  - repeat split; intros.
    + eapply SafeN_zero_of_block. apply T4_X_block.
    + eapply SafeN_zero_of_block. apply T4_Y_block.
    + eapply SafeN_zero_of_block. apply T4_Z_block.
  - destruct IH as (HX&HY&HZ). repeat split; intros.
    + eapply SafeN_block with
        (c:=k+2)
        (n':=NCol (C_RD (2*k+2)) (NEdge (E_RH O P1))).
      * lia.
      * apply T4_X_block.
      * replace (9*k+10-(k+2)) with (8*k+8) by lia.
        replace (2*(9*k+10)) with (18*k+20) by lia.
        eapply ColMap_safeN_RD.
        -- apply ColMap_RD; lia.
        -- replace (3*(8*k+8)+1) with (6*S (4*k+3)+1) by lia.
           replace (2*(18*k+20)) with (9*S (4*k+3)+4) by lia.
           apply HY.
    + eapply SafeN_block with
        (c:=S j+2)
        (n':=NCol (C_RD (2*S j+2)) (NEdge (E_RH 1 P1))).
      * lia.
      * apply T4_Y_block.
      * replace (9*S j+4-(S j+2)) with (8*S j+2) by lia.
        replace (2*(9*S j+4)) with (18*S j+8) by lia.
        eapply ColMap_safeN_RD.
        -- apply ColMap_RD; lia.
        -- replace (3*(8*S j+2)+1) with (6*(4*S j+1)+1) by lia.
           replace (2*(18*S j+8)) with (9*(4*S j+1)+7) by lia.
           apply HZ.
    + eapply SafeN_block with
        (c:=k+2)
        (n':=NCol (C_RD (2*k+2)) (NEdge (E_RH 1 P0))).
      * lia.
      * apply T4_Z_block.
      * replace (9*k+7-(k+2)) with (8*k+5) by lia.
        replace (2*(9*k+7)) with (18*k+14) by lia.
        eapply ColMap_safeN_RD.
        -- apply ColMap_RD; lia.
        -- replace (3*(8*k+5)+1) with (6*(4*k+2)+4) by lia.
           replace (2*(18*k+14)) with (9*(4*k+2)+10) by lia.
           apply HX.
Qed.

Lemma T4_initial_safeN d:
  SafeN d (NEdge (E_RH 4 P1)) 1 16.
Proof.
  destruct d as [|d].
  - eapply SafeN_zero_of_block. apply T4_initial_block.
  - eapply SafeN_block with
      (c:=3) (n':=NCol (C_RD 4) (NEdge (E_RH 1 P0))).
    + lia.
    + apply T4_initial_block.
    + replace (16-3) with 13 by lia.
      replace (2*16) with 32 by lia.
      eapply ColMap_safeN_RD.
      * apply ColMap_RD; lia.
      * replace (3*13+1) with (6*6+4) by lia.
        replace (2*32) with (9*6+10) by lia.
        apply (proj1 (T4_cycles_safeN d)).
Qed.

Lemma T4_edge_safe:
  Safe (NEdge (E_RH 4 P1)) 1 16.
Proof. apply Safe_of_all_SafeN. apply T4_initial_safeN. Qed.

Lemma T5_cycles_safeN d:
  (forall q, SafeN d (NEdge (E_RH 1 P1)) (6*q+4) (9*q+11)) /\
  (forall q, SafeN d (NEdge (E_RH (2*q+3) P0)) (8*q+9) (18*q+22)) /\
  (forall q, SafeN d (NEdge (E_RH (4*q+6) P0)) (16*q+18) (36*q+44)) /\
  (forall q, SafeN d (NEdge (E_RH O P1)) (96*q+115) (144*q+176)).
Proof.
  induction d as [|d IH].
  - repeat split; intros.
    + eapply SafeN_zero_of_block. apply T5_A_block.
    + eapply SafeN_zero_of_block. apply T5_B_block.
    + eapply SafeN_zero_of_block. apply T5_C_block.
    + eapply SafeN_zero_of_block. apply T5_D_block.
  - destruct IH as (HA&HB&HC&HD). repeat split; intros.
    + eapply SafeN_block with
        (c:=q+2) (n':=NEdge (E_RH (2*q+3) P0)).
      * lia.
      * apply T5_A_block.
      * replace (9*q+11-(q+2)) with (8*q+9) by lia.
        replace (2*(9*q+11)) with (18*q+22) by lia. apply HB.
    + eapply SafeN_block with
        (c:=2*q+4) (n':=NEdge (E_RH (4*q+6) P0)).
      * lia.
      * apply T5_B_block.
      * replace (18*q+22-(2*q+4)) with (16*q+18) by lia.
        replace (2*(18*q+22)) with (36*q+44) by lia. apply HC.
    + eapply SafeN_block with
        (c:=4*q+6)
        (n':=NCol (C_RD (8*q+10)) (NEdge (E_RH O P1))).
      * lia.
      * apply T5_C_block.
      * replace (36*q+44-(4*q+6)) with (32*q+38) by lia.
        replace (2*(36*q+44)) with (72*q+88) by lia.
        eapply ColMap_safeN_RD.
        -- apply ColMap_RD; lia.
        -- replace (3*(32*q+38)+1) with (96*q+115) by lia.
           replace (2*(72*q+88)) with (144*q+176) by lia. apply HD.
    + eapply SafeN_block with
        (c:=16*q+21)
        (n':=NCol (C_RD (32*q+40)) (NEdge (E_RH 1 P1))).
      * lia.
      * apply T5_D_block.
      * replace (144*q+176-(16*q+21)) with (128*q+155) by lia.
        replace (2*(144*q+176)) with (288*q+352) by lia.
        eapply ColMap_safeN_RD.
        -- apply ColMap_RD; lia.
        -- replace (3*(128*q+155)+1) with (6*(64*q+77)+4) by lia.
           replace (2*(288*q+352)) with (9*(64*q+77)+11) by lia.
           apply HA.
Qed.

Lemma T5_initial_edge_safeN d:
  SafeN d (NEdge (E_RH 8 P0)) 4 32.
Proof.
  destruct d as [|d].
  - eapply SafeN_zero_of_block. apply T5_initial_edge_block.
  - eapply SafeN_block with
      (c:=5) (n':=NCol (C_RD 8) (NEdge (E_RH 1 P1))).
    + lia.
    + apply T5_initial_edge_block.
    + replace (32-5) with 27 by lia. replace (2*32) with 64 by lia.
      eapply ColMap_safeN_RD.
      * apply ColMap_RD; lia.
      * replace (3*27+1) with (6*13+4) by lia.
        replace (2*64) with (9*13+11) by lia.
        apply (proj1 (T5_cycles_safeN d)).
Qed.

Lemma T5_initial_edge_safe:
  Safe (NEdge (E_RH 8 P0)) 4 32.
Proof. apply Safe_of_all_SafeN. apply T5_initial_edge_safeN. Qed.

Lemma T5_net_safe:
  Safe (NCol (C_RD 12) (NEdge (E_RH 8 P0))) 1 16.
Proof.
  eapply ColMap_safe.
  - apply ColMap_RD; lia.
  - replace (3*1+1) with 4 by lia. replace (2*16) with 32 by lia.
    apply T5_initial_edge_safe.
Qed.

Definition packet := At :: hashes 7.

Lemma eat_packet:
  eat packet O 8 = Some (S O,16).
Proof. reflexivity. Qed.

Lemma loop_step n:
  Safe n 1 16 ->
  exists n', Push packet (NCol (C_RD 6) n) n' /\ Safe n' 1 16.
Proof.
  intros HS.
  assert (Safe (NCol (C_RD 6) n) O 8) as HC.
  { eapply ColMap_safe.
    - apply ColMap_RD; lia.
    - replace (3*O+1) with (S O) by lia. replace (2*8) with 16 by lia.
      exact HS. }
  destruct (HC packet) as (n'&HP).
  { exists (S O),16. apply eat_packet. }
  exists n'. split; [exact HP|].
  eapply Safe_suffix; eauto. apply eat_packet.
Qed.

End Macro.

Module TM4.
Import Macro.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LE_0RA0RE_0RA0RB_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,@nil Sym).
Notation hR' := (A,<[0;1;0;1;1;0;1;0]).
Notation hL := (C,[0;1;0;1;0]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation w := [1;1;0;1;0].

Definition RD n := [1;1;1;0] ++ w^^n.
Definition RD1 m n := RD m ++ [1;1;0;1;0;1;1;0] ++ w^^n.
Definition RD2 n := w++[1;0]++w^^(2+n).

Definition rh n :=
match n with
| O => 0inf
| _ => [1;1] *> 0inf
end.

Definition RH n i := RD n *> rh i.
Definition RH1 m n i := RD1 m n *> rh i.
Definition RH2 n i := RD2 n *> rh i.
Definition RH3 a := RD (3+a) *> [1] *> 0inf.



Lemma RD_Inc n:
  segRLs tm h (h^^3) (RD n) (RD (2+n)).
Proof.
  ut; esx.
Qed.

Lemma RD_Ov a:
  segRLs tm h' h (RD (1+a)) (RD2 a).
Proof.
  ut; esx.
Qed.

Lemma RD2_Ov a:
  segRLs tm h [] (RD2 a) (RD1 0 a).
Proof.
  ut; esx.
Qed.

Lemma RD1_Inc m n:
  segRLs tm h [] (RD1 m (3+n)) (RD1 (2+m) n).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov0 m:
  segRLs tm h (h'++h^^2) (RD1 m 0) (RD (2+m)).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov1 m:
  segRLs tm h (h'++h) (RD1 m 1) (RD (2+m)).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov2 m:
  segRLs tm h h' (RD1 m 2) (RD (2+m)).
Proof.
  ut; esx.
Qed.


Lemma RH_Inc0 n:
  sideRLs tm h (RH n 0) (RH n 1).
Proof.
  ut; es' n.
Qed.

Lemma RH_Inc1 n:
  sideRLs tm h (RH n 1) (RH (1+n) 0).
Proof.
  ut; es' n.
Qed.

Lemma RH_Ov0 n:
  sideRLs tm h' (RH (2+n) 0) (RH2 n 1).
Proof.
  ut; es' n.
Qed.

Lemma RH_Ov1 n:
  sideRLs tm h' (RH (1+n) 1) (RH2 n 0).
Proof.
  ut; es' n.
Qed.

Lemma RH2_Ov n i:
  sideRLs tm h (RH2 n i) (RH1 0 n i).
Proof.
  destruct i;
  ut; es' n.
Qed.

Lemma RH1_Inc m n i:
  sideRLs tm h (RH1 m (3+n) i) (RH1 (2+m) n i).
Proof.
  destruct i;
  ut; st; es' m n.
Qed.

Lemma RH1_Ov00 a:
  sideRLs tm h (RH1 a 0 0) (RH (2+a) 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov10 a:
  sideRLs tm h (RH1 a 1 0) (RH (2+a) 1).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov20 a:
  sideRLs tm h (RH1 a 2 0) (RH (3+a) 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov01 a:
  sideRLs tm h (RH1 a 0 1) (RD (2+a) *> RH 1 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov11 a:
  sideRLs tm h (RH1 a 1 1) (RD (2+a) *> RH 0 1).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov21 a:
  sideRLs tm h (RH1 a 2 1) (RH3 a).
Proof.
  ut; st; es' a.
Qed.

Lemma RH3_Ov a:
  sideRLs tm h (RH3 a) (RD (4+a) *> RH 1 1).
Proof.
  ut; st; es' a.
Qed.

Definition cdenote c :=
match c with
| C_RD n => RD n
| C_RD1 m n => RD1 m n
| C_RD2 n => RD2 n
end.

Definition edenote e :=
match e with
| E_RH n P0 => RH n O
| E_RH n P1 => RH n 1
| E_RH1 m n P0 => RH1 m n O
| E_RH1 m n P1 => RH1 m n 1
| E_RH2 n P0 => RH2 n O
| E_RH2 n P1 => RH2 n 1
| E_RH3 a => RH3 a
end.

Fixpoint ndenote n :=
match n with
| NEdge e => edenote e
| NCol c r => cdenote c *> ndenote r
end.

Fixpoint sdenote xs :=
match xs with
| [] => []
| Hash::xs => h ++ sdenote xs
| At::xs => h' ++ sdenote xs
end.

Lemma sdenote_cons x xs:
  sdenote (x::xs) = sdenote [x] ++ sdenote xs.
Proof. destruct x; reflexivity. Qed.

Lemma col_step_sound x c c' ys:
  col_step x c = Some (c',ys) ->
  segRLs tm (sdenote [x]) (sdenote ys) (cdenote c) (cdenote c').
Proof.
  destruct x; destruct c as [n|m n|n]; cbn; intros E.
  - inversion E; subst. cbn.
    replace (n+2) with (2+n) by lia. apply RD_Inc.
  - destruct n as [|[|[|n]]]; cbn in E; inversion E; subst; cbn.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov0.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov1.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov2.
    + replace (m+2) with (2+m) by lia. apply RD1_Inc.
  - inversion E; subst. cbn. apply RD2_Ov.
  - destruct n as [|n]; cbn in E; try discriminate.
    inversion E; subst. cbn. apply RD_Ov.
  - discriminate.
  - discriminate.
Qed.

Lemma edge_step_sound x e n:
  edge_step x e = Some n ->
  sideRLs tm (sdenote [x]) (edenote e) (ndenote n).
Proof.
  destruct x; destruct e as [a i|m a i|a i|a].
  - destruct i; intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    + apply RH_Inc0.
    + replace (a+1) with (1+a) by lia. apply RH_Inc1.
  - destruct i; destruct a as [|[|[|a]]]; intros E;
      cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    + replace (m+2) with (2+m) by lia. apply RH1_Ov00.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov10.
    + replace (m+3) with (3+m) by lia. apply RH1_Ov20.
    + replace (m+2) with (2+m) by lia. apply RH1_Inc.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov01.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov11.
    + apply RH1_Ov21.
    + replace (m+2) with (2+m) by lia. apply RH1_Inc.
  - destruct i; intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote]; apply RH2_Ov.
  - intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    replace (a+4) with (4+a) by lia. apply RH3_Ov.
  - destruct i.
    + destruct a as [|[|a]]; intros E; cbn [edge_step] in E;
        try discriminate.
      inversion E; subst; cbn [sdenote edenote ndenote cdenote]. apply RH_Ov0.
    + destruct a as [|a]; intros E; cbn [edge_step] in E;
        try discriminate.
      destruct a; cbn [edge_step] in E; inversion E; subst;
        cbn [sdenote edenote ndenote cdenote]; apply RH_Ov1.
  - intros E; cbn [edge_step] in E; discriminate.
  - intros E; cbn [edge_step] in E; discriminate.
  - intros E; cbn [edge_step] in E; discriminate.
Qed.

Lemma Push_sound:
  (forall xs n n' (H:Push xs n n'),
      sideRLs tm (sdenote xs) (ndenote n) (ndenote n')) /\
  (forall x n n' (H:Push1 x n n'),
      sideRLs tm (sdenote [x]) (ndenote n) (ndenote n')).
Proof.
  apply Push_Push1_ind.
  - intros. constructor.
  - intros x xs n n1 n2 H1 IH1 Hs IHs.
    rewrite sdenote_cons. eapply sideRLs_trans; eauto.
  - intros. cbn. eapply edge_step_sound; eauto.
  - intros x c c' ys n n' E HP IH. cbn.
    eapply segRLs_sideRLs_concat.
    + eapply col_step_sound; eauto.
    + exact IH.
Qed.

Lemma Push_sound_main xs n n':
  Push xs n n' -> sideRLs tm (sdenote xs) (ndenote n) (ndenote n').
Proof. apply (proj1 Push_sound). Qed.


Notation lh := (0inf<*<[1;0;1;1;1;0;1;1;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1]).
Notation lh' := (0inf<*<[1;0;1;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;1;0;1;0;1;1;0;0;1;1]).

Lemma LIncs:
  sideRLs (flip tm) ([(hL,hR)]^^7) lh' lh.
Proof.
  esc.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh' {{{ (hR',R) }}} RD 6 *> r.
Proof.
  ut; es' & r.
Qed.

Definition Config r :=
  lh {{{ (hL,L) }}} r.

Lemma BigStep r r':
  sideRLs tm (h'++h^^7) (RD 6 *> r) r' ->
  Config r -->+ Config r'.
Proof.
  intros I1.
  unfold Config.
  follow LRst.
  apply (sideRLs_concat (LIncs) I1).
Qed.

Lemma init:
  c0 -->* Config (RH 4 1).
Proof.
  esx.
Qed.

Lemma packet_denote:
  sdenote packet = h'++h^^7.
Proof. reflexivity. Qed.

Definition GoodNet := { n : net | Safe n 1 16 }.
Definition GoodConfig (z:GoodNet) := Config (ndenote (proj1_sig z)).

Lemma GoodStep z:
  exists z', GoodConfig z -->+ GoodConfig z'.
Proof.
  destruct z as [n HS].
  destruct (loop_step _ HS) as (n'&HP&HS').
  exists (exist (fun n => Safe n 1 16) n' HS'). unfold GoodConfig. cbn.
  apply BigStep.
  pose proof (Push_sound_main _ _ _ HP) as H.
  cbn [ndenote cdenote] in H. rewrite packet_denote in H. exact H.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply init.
  - eapply progress_nonhalt_simple with
      (C:=GoodConfig)
      (i0:=exist (fun n => Safe n 1 16) (NEdge (E_RH 4 P1)) T4_edge_safe).
    apply GoodStep.
Qed.

End TM4.









Module TM5.
Import Macro.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA0RF_0RC0RD_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,@nil Sym).
Notation hR' := (C,<[0;1;0;1;1;0;1;0]).
Notation hL := (A,[0;1;0;1;0]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].
Notation w := [1;1;0;1;0].

Definition RD n := [1;1;1;0] ++ w^^n.
Definition RD1 m n := RD m ++ [1;1;0;1;0;1;1;0] ++ w^^n.
Definition RD2 n := w++[1;0]++w^^(2+n).

Definition rh n :=
match n with
| O => 0inf
| _ => [1;1] *> 0inf
end.

Definition RH n i := RD n *> rh i.
Definition RH1 m n i := RD1 m n *> rh i.
Definition RH2 n i := RD2 n *> rh i.
Definition RH3 a := RD (3+a) *> [1] *> 0inf.



Lemma RD_Inc n:
  segRLs tm h (h^^3) (RD n) (RD (2+n)).
Proof.
  ut; esx.
Qed.

Lemma RD_Ov a:
  segRLs tm h' h (RD (1+a)) (RD2 a).
Proof.
  ut; esx.
Qed.

Lemma RD2_Ov a:
  segRLs tm h [] (RD2 a) (RD1 0 a).
Proof.
  ut; esx.
Qed.

Lemma RD1_Inc m n:
  segRLs tm h [] (RD1 m (3+n)) (RD1 (2+m) n).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov0 m:
  segRLs tm h (h'++h^^2) (RD1 m 0) (RD (2+m)).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov1 m:
  segRLs tm h (h'++h) (RD1 m 1) (RD (2+m)).
Proof.
  ut; esx.
Qed.

Lemma RD1_Ov2 m:
  segRLs tm h h' (RD1 m 2) (RD (2+m)).
Proof.
  ut; esx.
Qed.


Lemma RH_Inc0 n:
  sideRLs tm h (RH n 0) (RH n 1).
Proof.
  ut; es' n.
Qed.

Lemma RH_Inc1 n:
  sideRLs tm h (RH n 1) (RH (1+n) 0).
Proof.
  ut; es' n.
Qed.

Lemma RH_Ov0 n:
  sideRLs tm h' (RH (2+n) 0) (RH2 n 1).
Proof.
  ut; es' n.
Qed.

Lemma RH_Ov1 n:
  sideRLs tm h' (RH (1+n) 1) (RH2 n 0).
Proof.
  ut; es' n.
Qed.

Lemma RH2_Ov n i:
  sideRLs tm h (RH2 n i) (RH1 0 n i).
Proof.
  destruct i;
  ut; es' n.
Qed.

Lemma RH1_Inc m n i:
  sideRLs tm h (RH1 m (3+n) i) (RH1 (2+m) n i).
Proof.
  destruct i;
  ut; st; es' m n.
Qed.

Lemma RH1_Ov00 a:
  sideRLs tm h (RH1 a 0 0) (RH (2+a) 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov10 a:
  sideRLs tm h (RH1 a 1 0) (RH (2+a) 1).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov20 a:
  sideRLs tm h (RH1 a 2 0) (RH (3+a) 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov01 a:
  sideRLs tm h (RH1 a 0 1) (RD (2+a) *> RH 1 0).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov11 a:
  sideRLs tm h (RH1 a 1 1) (RD (2+a) *> RH 0 1).
Proof.
  ut; st; es' a.
Qed.

Lemma RH1_Ov21 a:
  sideRLs tm h (RH1 a 2 1) (RH3 a).
Proof.
  ut; st; es' a.
Qed.

Lemma RH3_Ov a:
  sideRLs tm h (RH3 a) (RD (4+a) *> RH 1 1).
Proof.
  ut; st; es' a.
Qed.


Definition cdenote c :=
match c with
| C_RD n => RD n
| C_RD1 m n => RD1 m n
| C_RD2 n => RD2 n
end.

Definition edenote e :=
match e with
| E_RH n P0 => RH n O
| E_RH n P1 => RH n 1
| E_RH1 m n P0 => RH1 m n O
| E_RH1 m n P1 => RH1 m n 1
| E_RH2 n P0 => RH2 n O
| E_RH2 n P1 => RH2 n 1
| E_RH3 a => RH3 a
end.

Fixpoint ndenote n :=
match n with
| NEdge e => edenote e
| NCol c r => cdenote c *> ndenote r
end.

Fixpoint sdenote xs :=
match xs with
| [] => []
| Hash::xs => h ++ sdenote xs
| At::xs => h' ++ sdenote xs
end.

Lemma sdenote_cons x xs:
  sdenote (x::xs) = sdenote [x] ++ sdenote xs.
Proof. destruct x; reflexivity. Qed.

Lemma col_step_sound x c c' ys:
  col_step x c = Some (c',ys) ->
  segRLs tm (sdenote [x]) (sdenote ys) (cdenote c) (cdenote c').
Proof.
  destruct x; destruct c as [n|m n|n]; cbn; intros E.
  - inversion E; subst. cbn.
    replace (n+2) with (2+n) by lia. apply RD_Inc.
  - destruct n as [|[|[|n]]]; cbn in E; inversion E; subst; cbn.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov0.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov1.
    + replace (m+2) with (2+m) by lia. apply RD1_Ov2.
    + replace (m+2) with (2+m) by lia. apply RD1_Inc.
  - inversion E; subst. cbn. apply RD2_Ov.
  - destruct n as [|n]; cbn in E; try discriminate.
    inversion E; subst. cbn. apply RD_Ov.
  - discriminate.
  - discriminate.
Qed.

Lemma edge_step_sound x e n:
  edge_step x e = Some n ->
  sideRLs tm (sdenote [x]) (edenote e) (ndenote n).
Proof.
  destruct x; destruct e as [a i|m a i|a i|a].
  - destruct i; intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    + apply RH_Inc0.
    + replace (a+1) with (1+a) by lia. apply RH_Inc1.
  - destruct i; destruct a as [|[|[|a]]]; intros E;
      cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    + replace (m+2) with (2+m) by lia. apply RH1_Ov00.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov10.
    + replace (m+3) with (3+m) by lia. apply RH1_Ov20.
    + replace (m+2) with (2+m) by lia. apply RH1_Inc.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov01.
    + replace (m+2) with (2+m) by lia. apply RH1_Ov11.
    + apply RH1_Ov21.
    + replace (m+2) with (2+m) by lia. apply RH1_Inc.
  - destruct i; intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote]; apply RH2_Ov.
  - intros E; cbn [edge_step] in E; inversion E; subst;
      cbn [sdenote edenote ndenote cdenote].
    replace (a+4) with (4+a) by lia. apply RH3_Ov.
  - destruct i.
    + destruct a as [|[|a]]; intros E; cbn [edge_step] in E;
        try discriminate.
      inversion E; subst; cbn [sdenote edenote ndenote cdenote]. apply RH_Ov0.
    + destruct a as [|a]; intros E; cbn [edge_step] in E;
        try discriminate.
      destruct a; cbn [edge_step] in E; inversion E; subst;
        cbn [sdenote edenote ndenote cdenote]; apply RH_Ov1.
  - intros E; cbn [edge_step] in E; discriminate.
  - intros E; cbn [edge_step] in E; discriminate.
  - intros E; cbn [edge_step] in E; discriminate.
Qed.

Lemma Push_sound:
  (forall xs n n' (H:Push xs n n'),
      sideRLs tm (sdenote xs) (ndenote n) (ndenote n')) /\
  (forall x n n' (H:Push1 x n n'),
      sideRLs tm (sdenote [x]) (ndenote n) (ndenote n')).
Proof.
  apply Push_Push1_ind.
  - intros. constructor.
  - intros x xs n n1 n2 H1 IH1 Hs IHs.
    rewrite sdenote_cons. eapply sideRLs_trans; eauto.
  - intros. cbn. eapply edge_step_sound; eauto.
  - intros x c c' ys n n' E HP IH. cbn.
    eapply segRLs_sideRLs_concat.
    + eapply col_step_sound; eauto.
    + exact IH.
Qed.

Lemma Push_sound_main xs n n':
  Push xs n n' -> sideRLs tm (sdenote xs) (ndenote n) (ndenote n').
Proof. apply (proj1 Push_sound). Qed.


Notation lh := (0inf<*<[1;0;1;1;1;0;1;1;1;0;1;1;0;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1;0;1;0;1;1]).
Notation lh' := (0inf<*<[1;0;1;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;1;0;1;0;1;1;0;0;1;1]).

Lemma LIncs:
  sideRLs (flip tm) ([(hL,hR)]^^7) lh' lh.
Proof.
  esc.
Qed.

Lemma LRst r:
  lh {{{ (hL,L) }}} r -->*
  lh' {{{ (hR',R) }}} RD 6 *> r.
Proof.
  ut; es' & r.
Qed.

Definition Config r :=
  lh {{{ (hL,L) }}} r.

Lemma BigStep r r':
  sideRLs tm (h'++h^^7) (RD 6 *> r) r' ->
  Config r -->+ Config r'.
Proof.
  intros I1.
  unfold Config.
  follow LRst.
  apply (sideRLs_concat (LIncs) I1).
Qed.

Lemma init:
  c0 -->* Config (RD 12 *> RH 8 0).
Proof.
  esx.
Qed.

Lemma packet_denote:
  sdenote packet = h'++h^^7.
Proof. reflexivity. Qed.

Definition GoodNet := { n : net | Safe n 1 16 }.
Definition GoodConfig (z:GoodNet) := Config (ndenote (proj1_sig z)).

Lemma GoodStep z:
  exists z', GoodConfig z -->+ GoodConfig z'.
Proof.
  destruct z as [n HS].
  destruct (loop_step _ HS) as (n'&HP&HS').
  exists (exist (fun n => Safe n 1 16) n' HS'). unfold GoodConfig. cbn.
  apply BigStep.
  pose proof (Push_sound_main _ _ _ HP) as H.
  cbn [ndenote cdenote] in H. rewrite packet_denote in H. exact H.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply init.
  - eapply progress_nonhalt_simple with
      (C:=GoodConfig)
      (i0:=exist (fun n => Safe n 1 16)
        (NCol (C_RD 12) (NEdge (E_RH 8 P0))) T5_net_safe).
    apply GoodStep.
Qed.

End TM5.
