(* 1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB--- never halts.
   Bell eats counter. Adapted from verify/SOMDCv6.v, Module TM7
   (1RB0RC_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---), which differs only in A1 (0RC there, 0RF here).
   Here every L digit that a sweep enters fires one extra h pass, a +1 on the digits to its right.
   Informal proof: the accompanying write-up (proof.md).
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62 Longitudinal DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac ec := econstructor.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld := [1;1;0].
Notation d0 := [0;0;0].
Notation d1 := [1;0;0].
Notation w1ld := [1;1;1;0].
Notation hR := (B,@nil Sym).
Notation hR' := (D,[1]).
Notation hL := (C,@nil Sym).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL)].

Inductive RD := LD|D0|D1.
Inductive H := hx|h1.

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| LD::ls => ld*>toRC ls
| D0::ls => d0*>toRC ls
| D1::ls => d1*>toRC ls
end.

Definition toH' x :=
match x with
| hx => []
| h1 => [1]
end.

Definition toH x :=
match x with
| hx => h'
| h1 => []
end.

(* one h pass over the digits = +1 on the little-endian binary number of the 0/1 digits, L skipped *)
Inductive Inc: list RD -> list RD -> Prop :=
| Inc_nil: Inc [] [D1]
| Inc_d0 r: Inc (D0::r) (D1::r)
| Inc_d1 r r': Inc r r' -> Inc (D1::r) (D0::r')
| Inc_ld r r': Inc r r' -> Inc (LD::r) (LD::r').

Inductive RIncs: H->nat->(list RD)->(list RD)->Prop :=
| RIncs_hx_ld k r r1 r':
  Inc r r1 ->
  RIncs hx (1+k) r1 r' ->
  RIncs hx k (LD::r) (LD::r')

| RIncs_hx_d1 k r r':
  RIncs h1 k r r' ->
  RIncs hx k (D1::r) (LD::r')

| RIncs_hx_d0 k r r':
  RIncs hx (1+k) r r' ->
  RIncs hx k (D0::r) (LD::r')

| RIncs_h1_ld k r r1 r':
  Inc r r1 ->
  RIncs hx (1+k) r1 r' ->
  RIncs h1 (1+k) (LD::r) (LD::r')

| RIncs_h1_d1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k) (D1::r) (LD::r')

| RIncs_h1_d0_0 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (1+k*2) (D0::r) (D0::r')

| RIncs_h1_d0_1 k r r':
  RIncs h1 k r r' ->
  RIncs h1 (2+k*2) (D0::r) (D1::r')

| RIncs_h1_rh_0:
  RIncs h1 0 [] [D1]

| RIncs_h1_rh_1 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (1+k*2) [] (D0::r')

| RIncs_h1_rh_2 k r':
  RIncs h1 k [] r' ->
  RIncs h1 (2+k*2) [] (D1::r')

| RIncs_h1_z1:
  RIncs h1 0 [D1] [LD]

| RIncs_h1_z0:
  RIncs h1 0 [D0] [D1]
.

Ltac cat3 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_]) (w2:=[_;_;_]); [|eauto 1].

Ltac tr1 :=
  rewrite lpow_add,app_assoc;
  eapply segRLs_trans; [esx | ].

Ltac wal :=
  eapply segRLs_wall''; esx.

Ltac tr2 :=
  eapply sideRLs_trans; [esx | ].

Lemma z1_eq: [1] *> d1 *> 0inf = ld *> 0inf.
Proof.
  cbn. f_equal. f_equal. f_equal. symmetry. apply const_unfold.
Qed.

Lemma z0_eq: [1] *> d0 *> 0inf = d1 *> 0inf.
Proof.
  cbn. f_equal. f_equal. f_equal. symmetry. apply const_unfold.
Qed.

Open Scope nat.

Lemma Inc_spec r r':
  Inc r r' ->
  sideRLs tm h (toRC r) (toRC r').
Proof.
  intro H.
  induction H; cbn[toRC].
  - esc.
  - change h with (h++[]).
    eapply segRLs_sideRLs_concat; [esx | constructor].
  - eapply (@segRLs_sideRLs_concat tm h h); [esx | apply IHInc].
  - eapply (@segRLs_sideRLs_concat tm h h); [esx | apply IHInc].
Qed.

Lemma seg_hx_ld k:
  segRLs tm (h' ++ h^^k) (h ++ h' ++ h^^(1+k)) ld ld.
Proof.
  rewrite lpow_add.
  change (h ++ h' ++ h^^1 ++ h^^k) with ((h ++ h' ++ h^^1) ++ h^^k).
  eapply segRLs_trans; [esx | wal].
Qed.

Lemma seg_h1_ld k:
  segRLs tm (h^^1 ++ h^^k) (h ++ h' ++ h^^(1+k)) w1ld ld.
Proof.
  rewrite lpow_add.
  change (h ++ h' ++ h^^1 ++ h^^k) with ((h ++ h' ++ h^^1) ++ h^^k).
  eapply segRLs_trans; [esx | wal].
Qed.

Lemma RIncs_spec tp k r r':
  RIncs tp k r r' ->
  sideRLs tm (toH tp++h^^k) (toH' tp*>toRC r) (toRC r').
Proof.
  intro H.
  induction H; intros; cbn[toH toH' toRC] in *.
  - eapply @segRLs_sideRLs_concat with (w1:=[_;_;_]) (w2:=[_;_;_]).
    1: apply seg_hx_ld.
    eapply sideRLs_trans.
    1: apply Inc_spec; eassumption.
    apply IHRIncs.
  - tr2.
    cat3; wal.
  - cat3; tr1; wal.
  - change ([] ++ h^^(1+k)) with (h^^1 ++ h^^k).
    eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_]).
    1: apply seg_h1_ld.
    eapply sideRLs_trans.
    1: apply Inc_spec; eassumption.
    apply IHRIncs.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3; wal.
  - cat3.
    rewrite app_nil_l.
    am 2 1 k 1 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - cat3.
    rewrite Nat.add_comm.
    am 2 1 k 2 1.
    rewrite Nat.add_comm,lpow_add,Nat.mul_1_r.
    tr2; eauto 1.
  - esc.
  - rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 0 0.
  - change (2+k*2) with (1+(1+k*2)).
    rewrite lpow_add,app_assoc.
    tr2.
    cat3.
    rewrite app_nil_l.
    am 2 1 k 1 0.
  - cbn[lpow app]. rewrite z1_eq. constructor.
  - cbn[lpow app]. rewrite z0_eq. constructor.
Qed.

(* ---------- combinatorics of the sweep relation (no machine) ---------- *)

Lemma Inc_total r: exists r', Inc r r'.
Proof.
  induction r as [|d r [r' I]].
  - eexists; apply Inc_nil.
  - destruct d; eexists.
    + apply Inc_ld, I.
    + apply Inc_d0.
    + apply Inc_d1, I.
Qed.

Lemma Inc_fun r r1 r2: Inc r r1 -> Inc r r2 -> r1 = r2.
Proof.
  intro I. gen r2.
  induction I; intros r2 I2; inversion I2; subst; try reflexivity; f_equal; auto.
Qed.

Lemma RIncs_eqk tp k k' r r': RIncs tp k r r' -> k = k' -> RIncs tp k' r r'.
Proof. intros; subst; auto. Qed.

Ltac inc_nil :=
  repeat match goal with
  | J: Inc [] _ |- _ => inversion J; subst; clear J
  end.

(* proof.md Lemma A: one more pass after the k passes is +1 on the result *)
Lemma RIncs_Inc tp k r r' r'':
  RIncs tp k r r' -> Inc r' r'' -> RIncs tp (1+k) r r''.
Proof.
  intro I. gen r''.
  induction I; intros r'' J; inversion J; subst; inc_nil.
  - eapply RIncs_hx_ld; eauto.
  - apply RIncs_hx_d1; auto.
  - apply RIncs_hx_d0; auto.
  - eapply (RIncs_h1_ld (1+k)); eauto.
  - apply (RIncs_h1_d1 (1+k)); auto.
  - eapply RIncs_eqk; [apply RIncs_h1_d0_1; eauto | lia].
  - eapply RIncs_eqk; [apply (RIncs_h1_d0_0 (1+k)); eauto | lia].
  - apply (RIncs_h1_rh_1 0), RIncs_h1_rh_0.
  - eapply RIncs_eqk; [apply RIncs_h1_rh_2; eauto | lia].
  - eapply RIncs_eqk; [apply (RIncs_h1_rh_1 (1+k)); eauto | lia].
  - apply (RIncs_h1_d1 0), RIncs_h1_rh_0.
  - apply (RIncs_h1_d0_0 0), RIncs_h1_rh_0.
Qed.

Lemma RIncs_nxt_1 k:
  exists r, RIncs h1 k [] r.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  + ec. ec.
  + destruct (mod2 k); subst.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
    * epose proof (H0 _ _) as [r I].
      ec. ec. apply I.
  Unshelve. all: lia.
Qed.

Lemma End_1 m w:
  RIncs h1 m [] w -> forall q, m <= q -> exists w', RIncs h1 q w w'.
Proof.
  intro I. remember h1 as t. remember (@nil RD) as e.
  induction I; intros q Hq; try discriminate; subst.
  - destruct q as [|q].
    + eexists; apply RIncs_h1_z1.
    + destruct (RIncs_nxt_1 q) as [w I].
      eexists; apply (RIncs_h1_d1 q), I.
  - specialize (IHI eq_refl eq_refl).
    destruct (mod2 q) as [b Hb|b Hb]; subst q.
    + destruct b as [|b]; [lia|].
      destruct (IHI b) as [w I2]; [lia|].
      eexists; eapply RIncs_eqk; [apply RIncs_h1_d0_1, I2 | lia].
    + destruct (IHI b) as [w I2]; [lia|].
      eexists; apply RIncs_h1_d0_0, I2.
  - specialize (IHI eq_refl eq_refl).
    destruct q as [|q]; [lia|].
    destruct (IHI q) as [w I2]; [lia|].
    eexists; apply (RIncs_h1_d1 q), I2.
Qed.

Lemma End_x m w:
  RIncs h1 m [] w -> forall q, m <= 2*q+2 -> exists w', RIncs hx q w w'.
Proof.
  intro I. remember h1 as t. remember (@nil RD) as e.
  induction I; intros q Hq; try discriminate; subst.
  - destruct (RIncs_nxt_1 q) as [w I].
    eexists; apply RIncs_hx_d1, I.
  - specialize (IHI eq_refl eq_refl).
    destruct (IHI (1+q)) as [w I2]; [lia|].
    eexists; apply RIncs_hx_d0, I2.
  - destruct (End_1 _ _ I q) as [w I2]; [lia|].
    eexists; apply RIncs_hx_d1, I2.
Qed.

(* inversion helpers *)
Lemma inv_hx_ld k r rK: RIncs hx k (LD::r) rK ->
  exists r1 rK', Inc r r1 /\ RIncs hx (1+k) r1 rK' /\ rK = LD::rK'.
Proof. intro E; inversion E; subst; do 2 eexists; repeat split; eauto. Qed.

Lemma inv_hx_d1 k r rK: RIncs hx k (D1::r) rK ->
  exists rK', RIncs h1 k r rK' /\ rK = LD::rK'.
Proof. intro E; inversion E; subst; eexists; repeat split; eauto. Qed.

Lemma inv_hx_d0 k r rK: RIncs hx k (D0::r) rK ->
  exists rK', RIncs hx (1+k) r rK' /\ rK = LD::rK'.
Proof. intro E; inversion E; subst; eexists; repeat split; eauto. Qed.

Lemma inv_h1_ld k r rK: RIncs h1 (1+k) (LD::r) rK ->
  exists r1 rK', Inc r r1 /\ RIncs hx (1+k) r1 rK' /\ rK = LD::rK'.
Proof. intro E; inversion E; subst; do 2 eexists; repeat split; eauto. Qed.

Lemma inv_h1_d1 k r rK: RIncs h1 (1+k) (D1::r) rK ->
  exists rK', RIncs h1 k r rK' /\ rK = LD::rK'.
Proof. intro E; inversion E; subst; eexists; repeat split; eauto. Qed.

Lemma inv_h1_d0 K r rK: RIncs h1 K (D0::r) rK ->
  (exists A rK', K = 1+A*2 /\ RIncs h1 A r rK' /\ rK = D0::rK') \/
  (exists A rK', K = 2+A*2 /\ RIncs h1 A r rK' /\ rK = D1::rK') \/
  (K = 0 /\ r = [] /\ rK = [D1]).
Proof.
  intro E; inversion E; subst.
  - left; do 2 eexists; repeat split; eauto.
  - right; left; do 2 eexists; repeat split; eauto.
  - right; right; auto.
Qed.

Lemma inv_z1 K rK: RIncs h1 K [D1] rK ->
  (K = 0 /\ rK = [LD]) \/
  (exists K0 rK', K = 1+K0 /\ RIncs h1 K0 [] rK' /\ rK = LD::rK').
Proof.
  intro E; inversion E; subst.
  - right; do 2 eexists; repeat split; eauto.
  - left; auto.
Qed.

(* proof.md section 3.3: the second sweep reads the first's output after j pending +1s *)
Definition Inv tp k j tq q :=
  match tp, tq with
  | hx, hx => k <= q /\ j <= q
  | h1, hx => k+1 <= q /\ j <= q
  | h1, h1 => (j = 0 /\ 2*k+1 <= q) \/ (1 <= j /\ k+j <= q /\ 1 <= q)
  | hx, h1 => False
  end.

Lemma key tp k r r1:
  RIncs tp k r r1 ->
  forall j rK tq q,
  RIncs tp (k+j) r rK ->
  Inv tp k j tq q ->
  exists r2, RIncs tq q rK r2.
Proof.
  intro D.
  induction D as [k r r1 r' Hi D IH | k r r' D IH | k r r' D IH
                 | k r r1 r' Hi D IH | k r r' D IH | a r r' D IH | a r r' D IH
                 | | a r' D IH | a r' D IH | | ];
    intros j rK tq q E HI.
  - (* hx_ld *)
    destruct (inv_hx_ld _ _ _ E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (Inc_fun _ _ _ Hi' Hi) in E'.
    destruct tq; cbn in HI; [|contradiction].
    destruct (Inc_total rK') as [rK'' J].
    destruct (IH (1+j) rK'' hx (1+q)) as [r2 I2].
    + eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
    + cbn; lia.
    + eexists; eapply RIncs_hx_ld; eassumption.
  - (* hx_d1 *)
    destruct (inv_hx_d1 _ _ _ E) as [rK' [E' ->]].
    destruct tq; cbn in HI; [|contradiction].
    destruct (Inc_total rK') as [rK'' J].
    destruct (IH (1+j) rK'' hx (1+q)) as [r2 I2].
    + eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
    + cbn; lia.
    + eexists; eapply RIncs_hx_ld; eassumption.
  - (* hx_d0 *)
    destruct (inv_hx_d0 _ _ _ E) as [rK' [E' ->]].
    destruct tq; cbn in HI; [|contradiction].
    destruct (Inc_total rK') as [rK'' J].
    destruct (IH (1+j) rK'' hx (1+q)) as [r2 I2].
    + eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
    + cbn; lia.
    + eexists; eapply RIncs_hx_ld; eassumption.
  - (* h1_ld *)
    destruct (inv_h1_ld (k+j) _ _ E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (Inc_fun _ _ _ Hi' Hi) in E'.
    destruct (Inc_total rK') as [rK'' J].
    destruct tq; cbn in HI.
    + destruct (IH (1+j) rK'' hx (1+q)) as [r2 I2].
      * eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
      * cbn; lia.
      * eexists; eapply RIncs_hx_ld; eassumption.
    + destruct q as [|q0]; [lia|].
      destruct (IH (1+j) rK'' hx (S q0)) as [r2 I2].
      * eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
      * cbn; lia.
      * eexists; eapply (RIncs_h1_ld q0); eassumption.
  - (* h1_d1 *)
    destruct (inv_h1_d1 (k+j) _ _ E) as [rK' [E' ->]].
    destruct (Inc_total rK') as [rK'' J].
    destruct tq; cbn in HI.
    + destruct (IH (1+j) rK'' hx (1+q)) as [r2 I2].
      * eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
      * cbn; lia.
      * eexists; eapply RIncs_hx_ld; eassumption.
    + destruct q as [|q0]; [lia|].
      destruct (IH (1+j) rK'' hx (S q0)) as [r2 I2].
      * eapply RIncs_eqk; [eapply RIncs_Inc; eassumption | lia].
      * cbn; lia.
      * eexists; eapply (RIncs_h1_ld q0); eassumption.
  - (* h1_d0_0 *)
    destruct (inv_h1_d0 _ _ _ E) as [[A [rK' [HK [E' ->]]]]|[[A [rK' [HK [E' ->]]]]|[HK _]]]; [| |lia].
    + (* rK = D0::rK' *)
      assert (E2: RIncs h1 (a+(A-a)) r rK') by (eapply RIncs_eqk; [eassumption | lia]).
      destruct tq; cbn in HI.
      * destruct (IH (A-a) rK' hx (1+q) E2) as [r2 I2]; [cbn; lia|].
        eexists; apply RIncs_hx_d0, I2.
      * destruct (mod2 q) as [b Hb|b Hb]; subst q.
        -- destruct b as [|b]; [lia|].
           destruct (IH (A-a) rK' h1 b E2) as [r2 I2]; [cbn; lia|].
           eexists; eapply RIncs_eqk; [apply RIncs_h1_d0_1, I2 | lia].
        -- destruct (IH (A-a) rK' h1 b E2) as [r2 I2]; [cbn; lia|].
           eexists; apply RIncs_h1_d0_0, I2.
    + (* rK = D1::rK' *)
      assert (E2: RIncs h1 (a+(A-a)) r rK') by (eapply RIncs_eqk; [eassumption | lia]).
      destruct tq; cbn in HI.
      * destruct (IH (A-a) rK' h1 q E2) as [r2 I2]; [cbn; lia|].
        eexists; apply RIncs_hx_d1, I2.
      * destruct q as [|q0]; [lia|].
        destruct (IH (A-a) rK' h1 q0 E2) as [r2 I2]; [cbn; lia|].
        eexists; apply (RIncs_h1_d1 q0), I2.
  - (* h1_d0_1 *)
    destruct (inv_h1_d0 _ _ _ E) as [[A [rK' [HK [E' ->]]]]|[[A [rK' [HK [E' ->]]]]|[HK _]]]; [| |lia].
    + (* rK = D0::rK' *)
      assert (E2: RIncs h1 (a+(A-a)) r rK') by (eapply RIncs_eqk; [eassumption | lia]).
      destruct tq; cbn in HI.
      * destruct (IH (A-a) rK' hx (1+q) E2) as [r2 I2]; [cbn; lia|].
        eexists; apply RIncs_hx_d0, I2.
      * destruct (mod2 q) as [b Hb|b Hb]; subst q.
        -- destruct b as [|b]; [lia|].
           destruct (IH (A-a) rK' h1 b E2) as [r2 I2]; [cbn; lia|].
           eexists; eapply RIncs_eqk; [apply RIncs_h1_d0_1, I2 | lia].
        -- destruct (IH (A-a) rK' h1 b E2) as [r2 I2]; [cbn; lia|].
           eexists; apply RIncs_h1_d0_0, I2.
    + (* rK = D1::rK' *)
      assert (E2: RIncs h1 (a+(A-a)) r rK') by (eapply RIncs_eqk; [eassumption | lia]).
      destruct tq; cbn in HI.
      * destruct (IH (A-a) rK' h1 q E2) as [r2 I2]; [cbn; lia|].
        eexists; apply RIncs_hx_d1, I2.
      * destruct q as [|q0]; [lia|].
        destruct (IH (A-a) rK' h1 q0 E2) as [r2 I2]; [cbn; lia|].
        eexists; apply (RIncs_h1_d1 q0), I2.
  - (* rh_0 *)
    destruct tq; cbn in HI.
    + eapply End_x; [eassumption | lia].
    + eapply End_1; [eassumption | lia].
  - (* rh_1 *)
    destruct tq; cbn in HI.
    + eapply End_x; [eassumption | lia].
    + eapply End_1; [eassumption | lia].
  - (* rh_2 *)
    destruct tq; cbn in HI.
    + eapply End_x; [eassumption | lia].
    + eapply End_1; [eassumption | lia].
  - (* z1 *)
    destruct (inv_z1 _ _ E) as [[HK ->]|[K0 [rK' [HK [E' ->]]]]].
    + destruct tq; cbn in HI.
      * destruct (RIncs_nxt_1 (1+q)) as [w I].
        eexists; eapply RIncs_hx_ld; [apply Inc_nil | apply RIncs_hx_d1, I].
      * destruct q as [|q0]; [lia|].
        destruct (RIncs_nxt_1 (1+q0)) as [w I].
        eexists; eapply (RIncs_h1_ld q0); [apply Inc_nil | apply RIncs_hx_d1, I].
    + destruct (Inc_total rK') as [rK'' J].
      pose proof (RIncs_Inc _ _ _ _ _ E' J) as E''.
      destruct tq; cbn in HI.
      * destruct (End_x _ _ E'' (1+q)) as [w I]; [lia|].
        eexists; eapply RIncs_hx_ld; eassumption.
      * destruct q as [|q0]; [lia|].
        destruct (End_x _ _ E'' (1+q0)) as [w I]; [lia|].
        eexists; eapply (RIncs_h1_ld q0); eassumption.
  - (* z0 *)
    destruct (inv_h1_d0 _ _ _ E) as [[A [rK' [HK [E' ->]]]]|[[A [rK' [HK [E' ->]]]]|[HK [_ ->]]]].
    + destruct tq; cbn in HI.
      * destruct (End_x _ _ E' (1+q)) as [w I]; [lia|].
        eexists; apply RIncs_hx_d0, I.
      * destruct (mod2 q) as [b Hb|b Hb]; subst q.
        -- destruct b as [|b]; [lia|].
           destruct (End_1 _ _ E' b) as [w I]; [lia|].
           eexists; eapply RIncs_eqk; [apply RIncs_h1_d0_1, I | lia].
        -- destruct (End_1 _ _ E' b) as [w I]; [lia|].
           eexists; apply RIncs_h1_d0_0, I.
    + destruct tq; cbn in HI.
      * destruct (End_1 _ _ E' q) as [w I]; [lia|].
        eexists; apply RIncs_hx_d1, I.
      * destruct q as [|q0]; [lia|].
        destruct (End_1 _ _ E' q0) as [w I]; [lia|].
        eexists; apply (RIncs_h1_d1 q0), I.
    + destruct tq; cbn in HI.
      * destruct (RIncs_nxt_1 q) as [w I].
        eexists; apply RIncs_hx_d1, I.
      * destruct q as [|q0]; [lia|].
        destruct (RIncs_nxt_1 q0) as [w I].
        eexists; apply (RIncs_h1_d1 q0), I.
Qed.

Lemma domain r r':
  RIncs hx 0 r r' -> exists r'', RIncs hx 0 r' r''.
Proof.
  intro I.
  eapply (key _ _ _ _ I 0 r' hx 0).
  - apply I.
  - cbn; lia.
Qed.


Open Scope sym.

Notation lh := (0inf<*<[1]).

Definition S' r :=
  lh {{{ (hR',R) }}} toH' hx *> toRC r.

Lemma BigStep r r':
  RIncs hx 0 r r' ->
  S' r -->+ S' r'.
Proof.
  intros H.
  apply RIncs_spec in H.
  unfold S'.
  eapply sideRLs_1 in H.
  follow10 H.
  es.
Qed.

Lemma start: c0 -->* S' [LD;D1].
Proof. esx. Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' [LD;D1]).
  1: apply start.
  eapply progress_nonhalt_cond with (P:=fun r => exists r', RIncs hx 0 r r').
  2: {
    exists [LD;LD;LD;D1;D1].
    eapply RIncs_hx_ld; [apply Inc_d1, Inc_nil |].
    apply RIncs_hx_d0. apply RIncs_hx_d1.
    apply (RIncs_h1_rh_2 0), RIncs_h1_rh_0.
  }
  intros r [r' I1].
  exists r'; split.
  - apply BigStep, I1.
  - apply (domain _ _ I1).
Qed.

Close Scope sym.

(*
```
1RB0RF_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---

S(r) = 0^inf 11 D> <r> 0^inf          digits: L = 110, 0 = 000, 1 = 100
start: 0^inf A> 0^inf  -->*  S(L1)    (S(1) at step 5, S(L1) at step 16)
sweep: S(r) -->+ S(r')  if RIncs hx 0 r r'

inc(r): +1 on the little-endian binary number of the 0/1 digits of r, L skipped,
        a carry out of the last digit appends a 1
eater (hx,k):  L -> L, k+1, inc the rest;   0 -> L, k+1;   1 -> L, drain with k
drain (h1,k):  L -> L, eater with k, inc the rest (k >= 1);   1 -> L, k-1 (k >= 1)
               0 -> 0, (k-1)/2 (k odd);   0 -> 1, (k-2)/2 (k even, k >= 2)
right end (h1,k):  k = 0 -> 1;   k odd -> 0, (k-1)/2;   k even -> 1, (k-2)/2
last digit, drain with k = 0:  1 -> L,  0 -> 1   (1 100 0^inf = 110 0^inf, 1 000 0^inf = 100 0^inf)

domain: RIncs hx 0 r r' -> exists r'', RIncs hx 0 r' r''
  (key: a second sweep reading the first one's output after j pending +1 passes,
   under Inv; with j = 0 these are TM7's RIncs_nxt conditions)
```
*)
