From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import ZifyNat Lia ZArith PeanoNat ArithRing String List.

(* SOBC12 and SOBC13 share the service algebra and the closed reset family.
   Their native machines and their blank-start entrances remain distinct. *)
Notation aw := [1;0].         (* 01 *)
Notation bw := [0;1].         (* 10 *)
Notation tw := [0;1;0;1].     (* 1010 *)
Notation kw := [1;0;1;0].     (* 0101 *)
Notation zw := [0;1;1;0].     (* 0110 *)
Notation jw := [0;1;0;0].     (* 0010 *)
Notation lw := [1;0;0;1].     (* 1001 *)
Notation mw := [0;0;0;1].     (* 1000 *)
Notation rw := [0;0;1;0].     (* 0100 *)

Definition root (q:Q) (n:nat) (r:side) :=
  0inf {{{((q,[]),L)}}} zw^^(1+n) *> tw *> r.

Section Kernel.
Variables (tm:TM) (f h p:Q).
Local Notation fR := (f,[1]).
Local Notation fL := (f,[1]).
Local Notation hR := (h,[1]).
Local Notation hL := (f,[1]).
Local Notation hf := [(fR,fL)].
Local Notation hh := [(hR,hL)].
Local Notation hg := (hf ++ hh).

(* Eleven finite services and two root-owned returns.  A concrete proof
   supplies this record; no assumptions remain in either final theorem. *)
Record Kernel : Prop := {
  kernel_F_A : segRLs tm hf [] aw [0;0];
  kernel_F_T : segRLs tm hf [] tw zw;
  kernel_F_11 : segRLs tm hf [] [1;1] bw;
  kernel_H_T : segRLs tm hh [] tw lw;
  kernel_H_Z : segRLs tm hh [] zw kw;
  kernel_H_R : segRLs tm hh [] rw jw;
  kernel_F_J : segRLs tm hf hf jw tw;
  kernel_H_M : segRLs tm hh hh mw tw;
  kernel_H_L : segRLs tm hh hh lw zw;
  kernel_H_K : segRLs tm hh hf kw tw;
  kernel_F_Z : segRLs tm hf hg zw tw;
  kernel_P_step : forall n r s, sideRLs tm hf r s ->
    root p n r -[tm]->+ root p (1+n) s;
  kernel_zero_return : forall n k r,
    root p n (zw *> jw^^(1+k) *> [0;0] *> r) -[tm]->+
    root p 0 (tw *> lw^^n *> kw *> tw *> aw *> tw^^k *> [1;0;1] *> r)
}.
End Kernel.

Module Type Model.
Parameter tm : TM.
Parameter f h p : Q.
Parameter rules : Kernel tm f h p.
End Model.

Module Common (M:Model).
Import M.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation fR := (f,[1]).
Notation fL := (f,[1]).
Notation hR := (h,[1]).
Notation hL := (f,[1]).
Notation hf := [(fR,fL)].
Notation hh := [(hR,hL)].
Notation hg := (hf ++ hh).

Lemma F_A : segRLs tm hf [] aw [0;0].
Proof. exact (@kernel_F_A tm f h p rules). Qed.

Lemma F_T : segRLs tm hf [] tw zw.
Proof. exact (@kernel_F_T tm f h p rules). Qed.

Lemma F_11 : segRLs tm hf [] [1;1] bw.
Proof. exact (@kernel_F_11 tm f h p rules). Qed.

(* The older fixed pair is retained by finite concatenation. *)
Lemma F_K : segRLs tm hf [] kw rw.
Proof.
  change (segRLs tm hf [] (aw ++ aw) ([0;0] ++ aw)).
  eapply segRLs_concat; [apply F_A|constructor].
Qed.

Lemma F_L : segRLs tm hf [] lw mw.
Proof.
  change (segRLs tm hf [] (aw ++ bw) ([0;0] ++ bw)).
  eapply segRLs_concat; [apply F_A|constructor].
Qed.

Lemma H_T : segRLs tm hh [] tw lw.
Proof. exact (@kernel_H_T tm f h p rules). Qed.

Lemma H_Z : segRLs tm hh [] zw kw.
Proof. exact (@kernel_H_Z tm f h p rules). Qed.

Lemma H_R : segRLs tm hh [] rw jw.
Proof. exact (@kernel_H_R tm f h p rules). Qed.

(* A real pending-buffer cut: scanning J emits four ones before the
   older f call.  That outgoing call is retained in the conclusion. *)
Lemma F_J : segRLs tm hf hf jw tw.
Proof. exact (@kernel_F_J tm f h p rules). Qed.

(* The h-head scan of physical 1000 has the same four-one pending cut. *)
Lemma H_M : segRLs tm hh hh mw tw.
Proof. exact (@kernel_H_M tm f h p rules). Qed.

(* The h-head scanning physical L leaves 1110 followed by the original 1.  Only
   its first 1 is the outgoing buffer; the rest 1101 is processed below. *)
Lemma H_L : segRLs tm hh hh lw zw.
Proof. exact (@kernel_H_L tm f h p rules). Qed.

Lemma H_K : segRLs tm hh hf kw tw.
Proof. exact (@kernel_H_K tm f h p rules). Qed.

(* After the Z scan the pending word is 10111.  The first f call uses
   its first 1.  Its return really turns back into h in two steps:
     x 1 f>0111 -> x <h 11111.
   The final four pending ones are returned locally. *)
Lemma F_Z : segRLs tm hf hg zw tw.
Proof. exact (@kernel_F_Z tm f h p rules). Qed.

Lemma G_T : segRLs tm hg [] tw kw.
Proof.
  change (segRLs tm (hf ++ hh) ([] ++ []) tw kw).
  eapply segRLs_trans; [apply F_T|apply H_Z].
Qed.

Lemma G_K : segRLs tm hg [] kw jw.
Proof.
  change (segRLs tm (hf ++ hh) ([] ++ []) kw jw).
  eapply segRLs_trans; [apply F_K|apply H_R].
Qed.

Lemma G_J : segRLs tm hg hf jw lw.
Proof.
  change (segRLs tm (hf ++ hh) (hf ++ []) jw lw).
  eapply segRLs_trans; [apply F_J|apply H_T].
Qed.

Lemma G_L : segRLs tm hg hh lw tw.
Proof.
  change (segRLs tm (hf ++ hh) ([] ++ hh) lw tw).
  eapply segRLs_trans; [apply F_L|apply H_M].
Qed.

Lemma G_Z : segRLs tm hg hg zw lw.
Proof.
  change (segRLs tm (hf ++ hh) (hg ++ []) zw lw).
  eapply segRLs_trans; [apply F_Z|apply H_T].
Qed.

Lemma G2_J : segRLs tm (hg^^2) hg jw tw.
Proof.
  change (segRLs tm (hg ++ hg) (hf ++ hh) jw tw).
  eapply segRLs_trans; [apply G_J|apply G_L].
Qed.

Lemma G4_T : segRLs tm (hg^^4) hg tw tw.
Proof.
  change (segRLs tm (hg ++ (hg ++ hg^^2)) ([] ++ ([] ++ hg)) tw tw).
  eapply segRLs_trans; [apply G_T|].
  eapply segRLs_trans; [apply G_K|apply G2_J].
Qed.

Lemma G4_J : segRLs tm (hg^^4) hg jw jw.
Proof.
  change (segRLs tm (hg^^2 ++ (hg ++ hg)) (hg ++ ([] ++ [])) jw jw).
  eapply segRLs_trans; [apply G2_J|].
  eapply segRLs_trans; [apply G_T|apply G_K].
Qed.

Lemma F_Js n : segRLs tm hf hf (jw^^n) (tw^^n).
Proof.
  induction n as [|n IH].
  - apply segRLs_nil.
  - cbn [lpow]. eapply segRLs_concat; [apply F_J|exact IH].
Qed.

Lemma H_Ms n : segRLs tm hh hh (mw^^n) (tw^^n).
Proof.
  induction n as [|n IH].
  - apply segRLs_nil.
  - cbn [lpow]. eapply segRLs_concat; [apply H_M|exact IH].
Qed.

Lemma H_Ls n : segRLs tm hh hh (lw^^n) (zw^^n).
Proof.
  induction n as [|n IH].
  - apply segRLs_nil.
  - cbn [lpow]. eapply segRLs_concat; [apply H_L|exact IH].
Qed.

(* Parameter service counts; no concrete tower is evaluated. *)
Fixpoint q4 n := match n with O => O | S k => 1 + 4*q4 k end.

Lemma q4_pow n : 1 + 3*q4 n = 4^n.
Proof. induction n; cbn [q4 Nat.pow]; nia. Qed.

Lemma q4_add n m : q4 (n+m) = q4 n + 4^n*q4 m.
Proof.
  induction n; [change (q4 m = q4 m + 0); lia|].
  change (1+4*q4 (n+m) = 1+4*q4 n + (4*4^n)*q4 m).
  rewrite IHn. nia.
Qed.

Lemma service_repeat hs ks w n :
  segRLs tm hs ks w w -> segRLs tm (hs^^n) (ks^^n) w w.
Proof.
  intro H. induction n; [constructor|].
  cbn [lpow]. eapply segRLs_trans; eauto.
Qed.

Lemma F2_T : segRLs tm (hf^^2) hg tw tw.
Proof.
  change (segRLs tm (hf ++ hf) ([] ++ hg) tw tw).
  eapply segRLs_trans; [apply F_T|apply F_Z].
Qed.

Lemma G_recycle w n :
  segRLs tm (hg^^4) hg w w ->
  segRLs tm (hg^^(n*4)) (hg^^n) w w.
Proof.
  intro H. rewrite lpow_mul. apply service_repeat. exact H.
Qed.

Lemma G_lift w a n :
  segRLs tm (hg^^4) hg w w ->
  segRLs tm (hg^^(n*4^a)) (hg^^n) (w^^a) (w^^a).
Proof.
  intro H. induction a as [|a IH].
  - replace (n*4^0) with n by lia. apply segRLs_nil.
  - cbn [lpow Nat.pow].
    replace (n*(4*4^a)) with ((n*4^a)*4) by nia.
    eapply segRLs_concat; [apply G_recycle; exact H|exact IH].
Qed.

Lemma G_Ts a n :
  segRLs tm (hg^^(n*4^a)) (hg^^n) (tw^^a) (tw^^a).
Proof. apply G_lift, G4_T. Qed.

Lemma G_Js a n :
  segRLs tm (hg^^(n*4^a)) (hg^^n) (jw^^a) (jw^^a).
Proof. apply G_lift, G4_J. Qed.

Lemma F_T_calls a n :
  segRLs tm (hf^^(2*n*4^a)) (hg^^n) (tw^^(1+a)) (tw^^(1+a)).
Proof.
  cbn [lpow].
  replace (2*n*4^a) with ((n*4^a)*2) by nia.
  eapply segRLs_concat; [|apply G_Ts].
  rewrite lpow_mul. apply service_repeat, F2_T.
Qed.

Lemma G2_T : segRLs tm (hg^^2) [] tw jw.
Proof.
  change (segRLs tm (hg ++ hg) ([] ++ []) tw jw).
  eapply segRLs_trans; [apply G_T|apply G_K].
Qed.

Lemma G_normalize n : segRLs tm (hg^^(2*q4 n)) [] (tw^^n) (jw^^n).
Proof.
  induction n as [|n IH]; [constructor|].
  cbn [lpow].
  replace (2*q4 (S n)) with (2+(2*q4 n)*4) by (cbn [q4]; lia).
  rewrite lpow_add.
  change (segRLs tm (hg^^2 ++ hg^^((2*q4 n)*4)) ([] ++ [])
    (tw ++ tw^^n) (jw ++ jw^^n)).
  eapply (segRLs_trans (w2:=jw ++ tw^^n)).
  - eapply segRLs_concat; [apply G2_T|constructor].
  - eapply segRLs_concat; [apply G_recycle, G4_J|exact IH].
Qed.

Lemma F_normalize n :
  segRLs tm (hf^^(q4 (1+n))) [] (tw^^(1+n)) (zw ++ jw^^n).
Proof.
  replace (q4 (1+n)) with (2*(2*q4 n)*4^0+1)
    by (cbn [q4 Nat.add Nat.mul Nat.pow]; lia).
  rewrite lpow_add.
  change (segRLs tm (hf^^(2*(2*q4 n)*4^0) ++ hf) ([] ++ [])
    (tw ++ tw^^n) (zw ++ jw^^n)).
  eapply (segRLs_trans (w2:=tw ++ jw^^n)).
  - eapply segRLs_concat; [apply (F_T_calls 0 (2*q4 n))|apply G_normalize].
  - eapply segRLs_concat; [apply F_T|constructor].
Qed.

(* These two scans keep the older caller explicit: neither h nor f is
   asserted to return on an unknown prefix.  Physical order is reversed. *)
Lemma F_outer n :
  segRLs tm hf hh (zw ++ lw ++ mw^^n) (tw^^(2+n)).
Proof.
  change (segRLs tm hf hh (zw ++ (lw ++ mw^^n))
    (tw ++ (tw ++ tw^^n))).
  eapply segRLs_concat; [apply F_Z|].
  eapply segRLs_concat; [apply G_L|apply H_Ms].
Qed.

Lemma F_postJ n :
  segRLs tm hf hf (zw ++ jw^^(1+n)) (tw ++ lw ++ tw^^n).
Proof.
  change (segRLs tm hf hf (zw ++ (jw ++ jw^^n))
    (tw ++ (lw ++ tw^^n))).
  eapply segRLs_concat; [apply F_Z|].
  eapply segRLs_concat; [apply G_J|apply F_Js].
Qed.

Lemma BIN_borrow n :
  segRLs tm (hf^^(8+16*q4 n)) []
    (zw ++ lw ++ mw^^n ++ tw) (zw ++ lw ++ tw^^n ++ mw).
Proof.
  replace (8+16*q4 n) with (1+(q4 (1+(1+n))+(1+1)))
    by (cbn [q4 Nat.add Nat.mul]; lia).
  repeat rewrite lpow_add.
  change (segRLs tm (hf ++ (hf^^(q4 (1+(1+n))) ++ (hf ++ hf)))
    ([] ++ ([] ++ ([] ++ [])))
    (zw ++ lw ++ mw^^n ++ tw) (zw ++ lw ++ tw^^n ++ mw)).
  eapply (segRLs_trans (w2:=tw^^(2+n) ++ lw)).
  - repeat rewrite app_assoc.
    eapply segRLs_concat; [apply F_outer|apply H_T].
  - eapply (segRLs_trans (w2:=zw ++ jw^^(1+n) ++ lw)).
    + rewrite app_assoc.
      eapply segRLs_concat; [apply F_normalize|constructor].
    + eapply (segRLs_trans (w2:=tw ++ lw ++ tw^^n ++ mw)).
      * repeat rewrite app_assoc.
        eapply segRLs_concat; [apply F_postJ|apply F_L].
      * eapply segRLs_concat; [apply F_T|constructor].
Qed.

Lemma BIN n :
  segRLs tm (hf^^(8*q4 n)) [] (zw ++ lw ++ tw^^n) (zw ++ lw ++ mw^^n).
Proof.
  induction n as [|n IH]; [constructor|].
  replace (8*q4 (S n)) with (8*q4 n + ((8+16*q4 n)+8*q4 n))
    by (cbn [q4]; lia).
  repeat rewrite lpow_add.
  cbn [lpow]. rewrite <- (lpow_shift tw n), <- (lpow_shift mw n).
  change (segRLs tm (hf^^(8*q4 n) ++
    (hf^^(8+16*q4 n) ++ hf^^(8*q4 n))) ([] ++ ([] ++ []))
    (zw ++ lw ++ tw^^n ++ tw) (zw ++ lw ++ mw^^n ++ mw)).
  eapply (segRLs_trans (w2:=zw ++ lw ++ mw^^n ++ tw)).
  - repeat rewrite app_assoc. eapply segRLs_concat; [exact IH|constructor].
  - eapply segRLs_trans; [apply BIN_borrow|].
    repeat rewrite app_assoc. eapply segRLs_concat; [exact IH|constructor].
Qed.

Lemma G_Zs n : segRLs tm hg hg (zw^^n) (lw^^n).
Proof.
  induction n; [apply segRLs_nil|].
  cbn [lpow]. eapply segRLs_concat; [apply G_Z|exact IHn].
Qed.

Lemma G_Ls n : segRLs tm hg hh (lw^^(1+n)) (tw ++ zw^^n).
Proof.
  change (segRLs tm hg hh (lw ++ lw^^n) (tw ++ zw^^n)).
  eapply segRLs_concat; [apply G_L|apply H_Ls].
Qed.

Lemma G_ZT n :
  segRLs tm (hg^^2) hf (zw^^(1+n) ++ tw) (tw ++ zw^^n ++ tw).
Proof.
  change (segRLs tm (hg ++ hg) ([] ++ hf)
    (zw^^(1+n) ++ tw) (tw ++ zw^^n ++ tw)).
  eapply (segRLs_trans (w2:=lw^^(1+n) ++ kw)).
  - eapply segRLs_concat; [apply G_Zs|apply G_T].
  - rewrite app_assoc. eapply segRLs_concat; [apply G_Ls|apply H_K].
Qed.

(* The n consumed Z columns request exactly n actual f calls on the
   unchanged older caller; this is not a capacity-based completion. *)
Lemma G_reduce_Z n :
  segRLs tm (hg^^(2*q4 n)) (hf^^n) (zw^^n ++ tw) (tw^^(1+n)).
Proof.
  induction n as [|n IH]; [constructor|].
  replace (2*q4 (S n)) with (2+(2*q4 n)*4) by (cbn [q4]; lia).
  rewrite lpow_add.
  change (segRLs tm (hg^^2 ++ hg^^((2*q4 n)*4)) (hf ++ hf^^n)
    (zw^^(1+n) ++ tw) (tw ++ tw^^(1+n))).
  eapply (segRLs_trans (w2:=tw ++ zw^^n ++ tw)); [apply G_ZT|].
  eapply segRLs_concat; [apply G_recycle, G4_T|exact IH].
Qed.

Lemma G_column_start n w :
  segRLs tm hg [] (lw^^(1+n) ++ kw ++ tw ++ w)
    (tw ++ zw^^n ++ tw ++ zw ++ w).
Proof.
  change (segRLs tm hg [] (lw^^(1+n) ++ (kw ++ (tw ++ w)))
    ((tw ++ zw^^n) ++ (tw ++ (zw ++ w)))).
  eapply segRLs_concat; [apply G_Ls|].
  eapply segRLs_concat; [apply H_K|].
  eapply segRLs_concat; [apply F_T|constructor].
Qed.

Lemma COLUMN n w e hs :
  segRLs tm (hf^^n) hs (zw ++ w) e ->
  segRLs tm (hf^^(2+16*q4 n)) hs
    (tw ++ lw^^(1+n) ++ kw ++ tw ++ w) (tw^^(n+3) ++ e).
Proof.
  intro H.
  replace (2+16*q4 n) with (2*(1+8*q4 n)*4^0) by (cbn [Nat.pow]; lia).
  replace (n+3) with (1+(1+(1+n))) by lia.
  change (segRLs tm (hf^^(2*(1+8*q4 n)*4^0)) hs
    (tw ++ (lw^^(1+n) ++ kw ++ tw ++ w))
    (tw ++ (tw ++ tw^^(1+n) ++ e))).
  eapply segRLs_concat; [apply (F_T_calls 0 (1+8*q4 n))|].
  replace (1+8*q4 n) with (1+(2*q4 n)*4) by lia.
  rewrite lpow_add.
  change (segRLs tm (hg ++ hg^^((2*q4 n)*4)) ([] ++ hs)
    (lw^^(1+n) ++ kw ++ tw ++ w) (tw ++ tw^^(1+n) ++ e)).
  eapply (segRLs_trans (w2:=tw ++ zw^^n ++ tw ++ zw ++ w)).
  - apply G_column_start.
  - eapply segRLs_concat; [apply G_recycle, G4_T|].
    rewrite (app_assoc (zw^^n) tw (zw ++ w)).
    eapply segRLs_concat; [apply G_reduce_Z|exact H].
Qed.

Lemma G3_T : segRLs tm (hg^^3) hf tw lw.
Proof.
  change (segRLs tm (hg^^2 ++ hg) ([] ++ hf) tw lw).
  eapply segRLs_trans; [apply G2_T|apply G_J].
Qed.

Lemma G_almost n :
  segRLs tm (hg^^(3+12*q4 n)) hf (tw^^(1+n)) (lw ++ mw^^n).
Proof.
  induction n as [|n IH]; [exact G3_T|].
  replace (3+12*q4 (S n)) with ((3+12*q4 n)*4+3) by (cbn [q4]; lia).
  rewrite lpow_add.
  change (segRLs tm (hg^^((3+12*q4 n)*4) ++ hg^^3) (hf ++ [])
    (tw ++ tw^^(1+n)) (lw ++ mw ++ mw^^n)).
  eapply (segRLs_trans (w2:=tw ++ lw ++ mw^^n)).
  - eapply segRLs_concat; [apply G_recycle, G4_T|exact IH].
  - eapply segRLs_concat; [apply G3_T|].
    eapply segRLs_concat; [apply F_L|constructor].
Qed.

Lemma G_two_before n :
  segRLs tm (hg^^(14+48*q4 n)) hf (tw^^(2+n)) (jw ++ lw ++ mw^^n).
Proof.
  replace (14+48*q4 n) with ((3+12*q4 n)*4+2) by lia.
  rewrite lpow_add.
  change (segRLs tm (hg^^((3+12*q4 n)*4) ++ hg^^2) (hf ++ [])
    (tw ++ tw^^(1+n)) (jw ++ lw ++ mw^^n)).
  eapply (segRLs_trans (w2:=tw ++ lw ++ mw^^n)).
  - eapply segRLs_concat; [apply G_recycle, G4_T|apply G_almost].
  - eapply segRLs_concat; [apply G2_T|constructor].
Qed.

(* The actual older protocol is j complete g services, then one f.
   No last h service or cancellation of a possibly failing g is used. *)
Lemma NEAR_WRAP n j :
  segRLs tm (hf^^(29+96*q4 n+2*j*4^(2+n))) (hg^^j ++ hf)
    (tw^^(3+n)) (zw ++ jw ++ lw ++ mw^^n).
Proof.
  replace (29+96*q4 n+2*j*4^(2+n)) with
    (2*j*4^(2+n)+(2*(14+48*q4 n)*4^0+1)) by (cbn [Nat.pow]; nia).
  repeat rewrite lpow_add.
  eapply segRLs_trans; [apply (F_T_calls (2+n) j)|].
  change (segRLs tm (hf^^(2*(14+48*q4 n)*4^0) ++ hf) (hf ++ [])
    (tw ++ tw^^(2+n)) (zw ++ jw ++ lw ++ mw^^n)).
  eapply (segRLs_trans (w2:=tw ++ jw ++ lw ++ mw^^n)).
  - eapply segRLs_concat; [apply (F_T_calls 0 (14+48*q4 n))|apply G_two_before].
  - eapply segRLs_concat; [apply F_T|constructor].
Qed.

Notation cw := (lw ++ rw).
Notation dw := (lw ++ mw ++ rw).

Lemma G_append n k u v w :
  segRLs tm (hg^^n) [] u v ->
  segRLs tm (hg^^k) [] (tw ++ v) w ->
  segRLs tm (hg^^(4*n+k)) [] (tw ++ u) w.
Proof.
  intros H H'. rewrite lpow_add.
  change (segRLs tm (hg^^(4*n) ++ hg^^k) ([] ++ []) (tw ++ u) w).
  eapply (segRLs_trans (w2:=tw ++ v)); [|exact H'].
  replace (4*n) with (n*4) by lia.
  eapply segRLs_concat; [apply G_recycle, G4_T|exact H].
Qed.

Lemma G7 : segRLs tm (hg^^7) [] (tw^^2) cw.
Proof.
  eapply (G_append 1 3 tw kw); [apply G_T|].
  eapply segRLs_concat; [apply G3_T|apply F_K].
Qed.

Lemma G125 : segRLs tm (hg^^125) [] (tw^^4) (kw++dw).
Proof.
  assert (H : segRLs tm (hg^^31) [] (tw^^3) dw).
  { eapply (G_append 7 3 (tw^^2) cw); [apply G7|].
    eapply (segRLs_concat (w2:=lw)); [apply G3_T|].
    eapply (segRLs_concat (w1:=lw) (w2:=mw)); [apply F_L|constructor]. }
  eapply (G_append 31 1 (tw^^3) dw); [exact H|eapply segRLs_concat; [apply G_T|constructor]].
Qed.

Lemma G_prefix7 : segRLs tm (hg^^8061) [] (tw^^7) (kw ++ dw^^2).
Proof.
  assert (H5 : segRLs tm (hg^^503) [] (tw^^5) (cw ++ dw)).
  { eapply (G_append 125 3 (tw^^4) (kw ++ dw) (cw ++ dw)); [apply G125|].
    eapply (segRLs_concat (w2:=lw)); [apply G3_T|].
    eapply (segRLs_concat (w1:=kw) (w2:=rw)); [apply F_K|constructor]. }
  assert (H6 : segRLs tm (hg^^2015) [] (tw^^6) (dw ++ dw)).
  { eapply (G_append 503 3 (tw^^5) (cw ++ dw) (dw ++ dw)); [exact H5|].
    eapply (segRLs_concat (w2:=lw)); [apply G3_T|].
    eapply (segRLs_concat (w1:=lw) (w2:=mw)); [apply F_L|constructor]. }
  eapply (G_append 2015 1 (tw^^6) (dw ++ dw) (kw ++ dw^^2)); [exact H6|].
  eapply segRLs_concat; [exact G_T|constructor].
Qed.

Lemma G_pair13 : segRLs tm (hg^^13) [] (tw^^2 ++ kw) (kw ++ cw).
Proof.
  eapply (G_append 3 1 (tw ++ kw) cw (kw ++ cw)).
  - eapply segRLs_concat; [apply G3_T|apply F_K].
  - eapply segRLs_concat; [exact G_T|constructor].
Qed.

Lemma G_last61 : segRLs tm (hg^^61) [] (tw^^3 ++ kw) (kw ++ dw).
Proof.
  eapply (G_append 15 1 (tw^^2 ++ kw) dw (kw ++ dw)).
  - eapply (G_append 3 3 (tw ++ kw) cw dw).
    + eapply segRLs_concat; [apply G3_T|apply F_K].
    + eapply (segRLs_concat (w2:=lw)); [apply G3_T|].
      eapply (segRLs_concat (w1:=lw) (w2:=mw)); [apply F_L|constructor].
  - eapply segRLs_concat; [exact G_T|constructor].
Qed.

Fixpoint supply_d r := match r with O => 8061 | S r => 16*supply_d r+13 end.

Lemma G_supply_pairs r :
  segRLs tm (hg^^(supply_d r)) [] (tw^^(7+2*r)) (kw ++ cw^^r ++ dw^^2).
Proof.
  induction r as [|r IH]; [exact G_prefix7|].
  change (segRLs tm (hg^^(16*supply_d r+13)) []
    (tw^^(7+2*S r)) (kw ++ cw ++ cw^^r ++ dw^^2)).
  replace (7+2*S r) with (2+(7+2*r)) by lia.
  rewrite (lpow_add _ 2 (7+2*r) tw), (lpow_add _ (16*supply_d r) 13 hg).
  change (segRLs tm (hg^^(16*supply_d r) ++ hg^^13) ([] ++ [])
    (tw^^2 ++ tw^^(7+2*r)) (kw ++ cw ++ cw^^r ++ dw^^2)).
  eapply (segRLs_trans (w2:=tw^^2 ++ kw ++ cw^^r ++ dw^^2)).
  - replace (16*supply_d r) with (supply_d r*4^2) by nia.
    eapply segRLs_concat; [apply G_Ts|exact IH].
  - change (segRLs tm (hg^^13) []
      ((tw^^2 ++ kw) ++ (cw^^r ++ dw^^2)) ((kw ++ cw) ++ (cw^^r ++ dw^^2))).
    eapply segRLs_concat; [apply G_pair13|constructor].
Qed.

Lemma G_supply_digits r :
  segRLs tm (hg^^(64*supply_d r+61)) [] (tw^^(10+2*r))
    (kw ++ dw ++ cw^^r ++ dw^^2).
Proof.
  replace (10+2*r) with (3+(7+2*r)) by lia.
  rewrite (lpow_add _ 3 (7+2*r) tw), (lpow_add _ (64*supply_d r) 61 hg).
  change (segRLs tm (hg^^(64*supply_d r) ++ hg^^61) ([] ++ [])
    (tw^^3 ++ tw^^(7+2*r)) (kw ++ dw ++ cw^^r ++ dw^^2)).
  eapply (segRLs_trans (w2:=tw^^3 ++ kw ++ cw^^r ++ dw^^2)).
  - replace (64*supply_d r) with (supply_d r*4^3) by nia.
    eapply segRLs_concat; [apply G_Ts|apply G_supply_pairs].
  - change (segRLs tm (hg^^61) []
      ((tw^^3 ++ kw) ++ (cw^^r ++ dw^^2)) ((kw ++ dw) ++ (cw^^r ++ dw^^2))).
    eapply segRLs_concat; [apply G_last61|constructor].
Qed.

Lemma G2_KK : segRLs tm (hg^^2) [] (kw ++ kw) cw.
Proof.
  change (segRLs tm (hg ++ hg) ([] ++ []) (kw ++ kw) cw).
  eapply (segRLs_trans (w2:=jw ++ kw)).
  - eapply segRLs_concat; [apply G_K|constructor].
  - eapply segRLs_concat; [apply G_J|apply F_K].
Qed.

Definition supply_g r := 2*4^(10+2*r)+64*supply_d r+61.

Lemma G_SUPPLY r :
  segRLs tm (hg^^(supply_g r)) [] (tw^^(10+2*r) ++ kw ++ kw)
    (kw ++ dw ++ cw^^r ++ dw^^2 ++ cw).
Proof.
  unfold supply_g. rewrite <- Nat.add_assoc, lpow_add.
  change (segRLs tm (hg^^(2*4^(10+2*r)) ++ hg^^(64*supply_d r+61))
    ([] ++ []) (tw^^(10+2*r) ++ kw ++ kw) (kw ++ dw ++ cw^^r ++ dw^^2 ++ cw)).
  eapply (segRLs_trans (w2:=tw^^(10+2*r) ++ cw)).
  - eapply segRLs_concat; [apply G_Ts|apply G2_KK].
  - rewrite (app_assoc (cw^^r) (dw^^2) cw).
    change (segRLs tm (hg^^(64*supply_d r+61)) []
      (tw^^(10+2*r) ++ cw) ((kw ++ dw ++ cw^^r ++ dw^^2) ++ cw)).
    eapply segRLs_concat; [apply G_supply_digits|constructor].
Qed.

Definition supply_f r n :=
  8*q4 (n+11+2*r)+1+(29+96*q4 n+2*supply_g r*4^(2+n)).

(* m=3+2r, B=2+n.  The older physical prefix, including its actual 00,
   is outside this finite protected window and is never inspected. *)
Lemma SUPPLY r n :
  segRLs tm (hf^^(supply_f r n)) []
    (zw ++ lw ++ tw^^(n+11+2*r) ++ zw ++ kw)
    (zw ++ jw ++ lw ++ mw^^n ++ rw ++ dw ++ cw^^r ++ dw^^2 ++ cw).
Proof.
  unfold supply_f. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ (8*q4 (n+11+2*r))
    (1+(29+96*q4 n+2*supply_g r*4^(2+n))) hf).
  rewrite (lpow_add _ 1 (29+96*q4 n+2*supply_g r*4^(2+n)) hf).
  change (segRLs tm (hf^^(8*q4 (n+11+2*r)) ++
    (hf ++ hf^^(29+96*q4 n+2*supply_g r*4^(2+n)))) ([] ++ ([] ++ []))
    (zw ++ lw ++ tw^^(n+11+2*r) ++ zw ++ kw)
    (zw ++ jw ++ lw ++ mw^^n ++ rw ++ dw ++ cw^^r ++ dw^^2 ++ cw)).
  eapply (segRLs_trans (w2:=zw ++ lw ++ mw^^(n+11+2*r) ++ zw ++ kw)).
  - change (segRLs tm (hf^^(8*q4 (n+11+2*r))) []
      ((zw ++ lw ++ tw^^(n+11+2*r)) ++ (zw ++ kw))
      ((zw ++ lw ++ mw^^(n+11+2*r)) ++ (zw ++ kw))).
    eapply segRLs_concat; [apply BIN|constructor].
  - eapply (segRLs_trans (w2:=tw^^(2+(n+11+2*r)) ++ kw ++ kw)).
    + change (segRLs tm hf []
        ((zw ++ lw ++ mw^^(n+11+2*r)) ++ (zw ++ kw))
        (tw^^(2+(n+11+2*r)) ++ (kw ++ kw))).
      eapply segRLs_concat; [apply F_outer|].
      eapply segRLs_concat; [apply H_Z|constructor].
    + replace (2+(n+11+2*r)) with ((3+n)+(10+2*r)) by lia.
      rewrite (lpow_add _ (3+n) (10+2*r) tw).
      rewrite <- app_assoc.
      change (segRLs tm (hf^^(29+96*q4 n+2*supply_g r*4^(2+n))) []
        (tw^^(3+n) ++ (tw^^(10+2*r) ++ kw ++ kw))
        ((zw ++ jw ++ lw ++ mw^^n) ++ (rw ++ dw ++ cw^^r ++ dw^^2 ++ cw))).
      eapply segRLs_concat; [apply NEAR_WRAP|].
      change (segRLs tm (hg^^(supply_g r) ++ hf) ([] ++ [])
        (tw^^(10+2*r) ++ kw ++ kw) (rw ++ dw ++ cw^^r ++ dw^^2 ++ cw)).
      eapply segRLs_trans; [apply G_SUPPLY|].
      eapply (segRLs_concat (w1:=kw) (w2:=rw)); [apply F_K|constructor].
Qed.

Fixpoint q16 n := match n with O => O | S k => 1+16*q16 k end.

Lemma q16_pow n : 1+15*q16 n = 16^n.
Proof. induction n; cbn [q16 Nat.pow]; nia. Qed.

Lemma pow4_double n : 4^(2*n) = 16^n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (2*S n) with (2+2*n) by lia.
  rewrite Nat.pow_add_r, IH. reflexivity.
Qed.

(* The two older calls are really g followed by h.  They remain present
   even when the older word does not happen to support them. *)
Lemma EVEN_END : segRLs tm (hg^^8) (hg ++ hh) (tw ++ zw) (tw^^2).
Proof.
  change (segRLs tm (hg^^3 ++ (hg ++ (hg^^2 ++ (hg ++ hg))))
    (hg ++ ([] ++ ([] ++ ([] ++ hh)))) (tw ++ zw) (tw^^2)).
  eapply (segRLs_trans (w2:=lw ++ tw)).
  - eapply segRLs_concat; [apply G3_T|apply F_Z].
  - eapply (segRLs_trans (w2:=tw ++ lw)).
    + eapply segRLs_concat; [apply G_L|apply H_T].
    + eapply (segRLs_trans (w2:=jw ++ lw)).
      * eapply segRLs_concat; [apply G2_T|constructor].
      * eapply (segRLs_trans (w2:=lw ++ mw)).
        -- eapply segRLs_concat; [apply G_J|apply F_L].
        -- eapply (segRLs_concat (w1:=lw) (w2:=tw)); [apply G_L|apply H_M].
Qed.

Lemma ODD_END : segRLs tm (hg^^8) hf (tw ++ zw ++ tw) (tw^^3).
Proof.
  change (segRLs tm (hg^^8) hf ((tw ++ zw) ++ tw) (tw^^2 ++ tw)).
  eapply segRLs_concat; [apply EVEN_END|].
  change (segRLs tm (hg ++ hh) ([] ++ hf) tw tw).
  eapply segRLs_trans; [apply G_T|apply H_K].
Qed.

Lemma SHIFT : segRLs tm (hg^^8) [] (tw ++ zw ++ tw^^2) (tw^^3 ++ zw).
Proof.
  change (segRLs tm (hg^^8) [] ((tw ++ zw ++ tw) ++ tw) (tw^^3 ++ zw)).
  eapply segRLs_concat; [apply ODD_END|apply F_T].
Qed.

Lemma SHIFTS r :
  segRLs tm (hg^^(8*q16 r)) [] (tw ++ zw ++ tw^^(2*r)) (tw^^(1+2*r) ++ zw).
Proof.
  induction r as [|r IH]; [constructor|].
  replace (8*q16 (S r)) with (8+16*(8*q16 r)) by (cbn [q16]; lia).
  replace (2*S r) with (2+2*r) by lia.
  replace (1+(2+2*r)) with (2+(1+2*r)) by lia.
  rewrite (lpow_add _ 2 (2*r) tw), (lpow_add _ 2 (1+2*r) tw), lpow_add.
  change (segRLs tm (hg^^8 ++ hg^^(16*(8*q16 r))) ([] ++ [])
    ((tw ++ zw ++ tw^^2) ++ tw^^(2*r)) ((tw^^2 ++ tw^^(1+2*r)) ++ zw)).
  eapply (segRLs_trans (w2:=tw^^2 ++ (tw ++ zw ++ tw^^(2*r)))).
  - eapply (segRLs_concat (w1:=tw ++ zw ++ tw^^2) (w2:=tw^^3 ++ zw));
      [apply SHIFT|constructor].
  - rewrite <- app_assoc.
    replace (16*(8*q16 r)) with ((8*q16 r)*4^2) by nia.
    eapply segRLs_concat; [apply G_Ts|exact IH].
Qed.

Lemma G_Mstart n :
  segRLs tm (hg^^2) hh (zw ++ jw ++ lw ++ mw^^n) (tw ++ zw ++ tw^^(1+n)).
Proof.
  change (segRLs tm (hg ++ hg) ([] ++ hh)
    (zw ++ jw ++ lw ++ mw^^n) (tw ++ zw ++ tw^^(1+n))).
  eapply (segRLs_trans (w2:=lw^^2 ++ mw^^(1+n))).
  - eapply (segRLs_concat (w1:=zw) (w2:=lw)); [apply G_Z|].
    eapply (segRLs_concat (w1:=jw) (w2:=lw)); [apply G_J|].
    eapply (segRLs_concat (w1:=lw) (w2:=mw)); [apply F_L|constructor].
  - change (segRLs tm hg hh (lw^^(1+1) ++ mw^^(1+n)) ((tw ++ zw^^1) ++ tw^^(1+n))).
    eapply segRLs_concat; [apply G_Ls|apply H_Ms].
Qed.

Lemma M_ODD r :
  segRLs tm (hg^^(2+8*q16 (2+r))) (hh ++ hg ++ hh)
    (zw ++ jw ++ lw ++ mw^^(1+2*r)) (tw^^(4+2*r)).
Proof.
  assert (E : 2+8*q16 (2+r) = 2+(8*q16 (1+r)+8*4^(2+2*r))).
  { replace (2+2*r) with (2*(1+r)) by lia. rewrite pow4_double.
    pose proof (q16_pow (1+r)).
    change (2+8*(1+16*q16 (1+r)) = 2+(8*q16 (1+r)+8*16^(1+r))). nia. }
  rewrite E.
  rewrite (lpow_add _ 2 (8*q16 (1+r)+8*4^(2+2*r)) hg).
  rewrite (lpow_add _ (8*q16 (1+r)) (8*4^(2+2*r)) hg).
  change (segRLs tm (hg^^2 ++ (hg^^(8*q16 (1+r)) ++ hg^^(8*4^(2+2*r))))
    (hh ++ ([] ++ (hg ++ hh)))
    (zw ++ jw ++ lw ++ mw^^(1+2*r)) (tw^^(4+2*r))).
  eapply (segRLs_trans (w2:=tw ++ zw ++ tw^^(2+2*r))); [apply G_Mstart|].
  eapply (segRLs_trans (w2:=tw^^(3+2*r) ++ zw)).
  - replace (2+2*r) with (2*(1+r)) by lia.
    replace (3+2*r) with (1+2*(1+r)) by lia. apply SHIFTS.
  - replace (3+2*r) with ((2+2*r)+1) by lia.
    replace (4+2*r) with ((2+2*r)+2) by lia.
    rewrite (lpow_add _ (2+2*r) 1 tw), (lpow_add _ (2+2*r) 2 tw).
    repeat rewrite <- app_assoc.
    eapply (segRLs_concat (w1:=tw^^(2+2*r)) (w2:=tw^^(2+2*r)));
      [apply G_Ts|exact EVEN_END].
Qed.

Lemma GH_JC : segRLs tm (hg ++ hh) [] (jw ++ cw) (zw ++ tw ++ jw).
Proof.
  change (segRLs tm (hg ++ hh) ([] ++ []) (jw ++ cw) (zw ++ tw ++ jw)).
  eapply (segRLs_trans (w2:=dw)).
  - eapply segRLs_concat; [apply G_J|].
    eapply segRLs_concat; [apply F_L|constructor].
  - eapply segRLs_concat; [apply H_L|].
    eapply segRLs_concat; [apply H_M|apply H_R].
Qed.

Lemma F_JC : segRLs tm hf [] (jw ++ cw) (tw ++ mw ++ rw).
Proof.
  eapply segRLs_concat; [apply F_J|].
  eapply segRLs_concat; [apply F_L|constructor].
Qed.

(* This is the precise three-service guard of the generated F caller;
   f(F) or g(F) is neither required nor substituted for it. *)
Lemma HGH_F :
  segRLs tm (hh ++ hg ++ hh) [] (rw ++ dw) (zw ++ tw^^2 ++ jw).
Proof.
  change (segRLs tm (hh ++ (hg ++ hh)) ([] ++ ([] ++ []))
    (rw ++ dw) (zw ++ tw^^2 ++ jw)).
  eapply (segRLs_trans (w2:=jw ++ dw)).
  - eapply segRLs_concat; [apply H_R|constructor].
  - eapply (segRLs_trans (w2:=lw ++ mw ++ mw ++ rw)).
    + eapply (segRLs_concat (w1:=jw) (w2:=lw)); [apply G_J|].
      eapply (segRLs_concat (w1:=lw) (w2:=mw)); [apply F_L|constructor].
    + eapply (segRLs_concat (w1:=lw) (w2:=zw)); [apply H_L|].
      eapply (segRLs_concat (w1:=mw) (w2:=tw)); [apply H_M|].
      eapply (segRLs_concat (w1:=mw) (w2:=tw)); [apply H_M|apply H_R].
Qed.

Lemma G_packet2 : segRLs tm (hg^^2) [] (zw ++ tw^^2) (tw^^2 ++ zw).
Proof.
  change (segRLs tm (hg^^2) [] ((zw^^(1+0) ++ tw) ++ tw)
    ((tw ++ zw^^0 ++ tw) ++ zw)).
  eapply segRLs_concat; [apply G_ZT|apply F_T].
Qed.

Lemma PACKET162 :
  segRLs tm (hg^^162) [] (zw ++ tw^^2 ++ jw ++ cw^^2) (tw^^6 ++ mw ++ rw).
Proof.
  change (segRLs tm (hg^^2 ++ (hg^^32 ++ hg^^128)) ([] ++ ([] ++ []))
    (zw ++ tw^^2 ++ jw ++ cw^^2) (tw^^6 ++ mw ++ rw)).
  eapply (segRLs_trans (w2:=tw^^2 ++ zw ++ jw ++ cw^^2)).
  - eapply (segRLs_concat (w1:=zw ++ tw^^2) (w2:=tw^^2 ++ zw));
      [apply G_packet2|constructor].
  - eapply (segRLs_trans (w2:=tw^^3 ++ zw ++ tw ++ jw ++ cw)).
    + eapply (segRLs_concat (w1:=tw^^1) (w2:=tw^^1)); [apply (G_Ts 1 8)|].
      eapply (segRLs_concat (w1:=tw ++ zw) (w2:=tw^^2)); [apply EVEN_END|].
      eapply (segRLs_concat (w1:=jw ++ cw) (w2:=zw ++ tw ++ jw)); [apply GH_JC|constructor].
    + eapply (segRLs_concat (w1:=tw^^2) (w2:=tw^^2)); [apply (G_Ts 2 8)|].
      eapply (segRLs_concat (w1:=tw ++ zw ++ tw) (w2:=tw^^3)); [apply ODD_END|apply F_JC].
Qed.

Lemma PACKET r :
  segRLs tm (hg^^2892) [] (zw ++ tw^^2 ++ jw ++ cw^^(2+r))
    (jw^^6 ++ mw ++ rw ++ cw^^r).
Proof.
  replace 2892 with (162+2*q4 6) by reflexivity. rewrite lpow_add.
  change (segRLs tm (hg^^162 ++ hg^^(2*q4 6)) ([] ++ [])
    (zw ++ tw^^2 ++ jw ++ cw^^(2+r)) (jw^^6 ++ mw ++ rw ++ cw^^r)).
  eapply (segRLs_trans (w2:=tw^^6 ++ mw ++ rw ++ cw^^r)).
  - rewrite (lpow_add _ 2 r cw).
    change (segRLs tm (hg^^162) []
      ((zw ++ tw^^2 ++ jw ++ cw^^2) ++ cw^^r) ((tw^^6 ++ mw ++ rw) ++ cw^^r)).
    eapply segRLs_concat; [apply PACKET162|constructor].
  - eapply segRLs_concat; [apply G_normalize|constructor].
Qed.

Definition P (n:nat) (r:side) := root p n r.

Lemma P_step n r s :
  sideRLs tm hf r s -> P n r -->+ P (1+n) s.
Proof. exact (@kernel_P_step tm f h p rules n r s). Qed.

Lemma P_calls n k r s :
  sideRLs tm (hf^^k) r s -> P n r -->* P (n+k) s.
Proof.
  gen n r; induction k as [|k IH]; intros n r H.
  - cbn [lpow] in H; inverts H; replace (n+0) with n by lia; finish.
  - replace (S k) with (1+k) in H |- * by lia.
    change (sideRLs tm (hf++hf^^k) r s) in H.
    destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^k) H) as [r1 [H1 H2]].
    follow100 (P_step n _ _ H1).
    applys_eq (IH (1+n) _ H2); flia.
Qed.

Lemma zero_return n k r :
  P n (zw *> jw^^(1+k) *> [0;0] *> r) -->+
  P 0 (tw *> lw^^n *> kw *> tw *> aw *> tw^^k *> [1;0;1] *> r).
Proof. exact (@kernel_zero_return tm f h p rules n k r). Qed.

Lemma supply_balance r :
  6*supply_d r+5 = 3*q16 (2+r)+755*4^(3+2*r).
Proof.
  induction r as [|r IH].
  - change (6*(13+16*(7+16*31))+5 = 3*17+755*64). nia.
  - replace (2+S r) with (S (2+r)) by (lia).
    replace (3+2*S r) with (2+(3+2*r)) by (lia).
    rewrite (Nat.pow_add_r 4 2 (3+2*r)).
    change (6*(16*supply_d r+13)+5 =
      3*(1+16*q16 (2+r))+755*(16*4^(3+2*r))). nia.
Qed.

Lemma supply_g_balance r :
  24*supply_g r = 184+768*q16 (2+r)+3827*4^(7+2*r).
Proof.
  pose proof (supply_balance r) as H.
  assert (P7 : 4^(7+2*r)=256*4^(3+2*r)).
  { replace (7+2*r) with (4+(3+2*r)) by (lia).
    rewrite Nat.pow_add_r. reflexivity. }
  assert (P10 : 4^(10+2*r)=64*4^(7+2*r)).
  { replace (10+2*r) with (3+(7+2*r)) by (lia).
    rewrite Nat.pow_add_r. reflexivity. }
  unfold supply_g. rewrite P10. nia.
Qed.

Lemma budget_algebra (a b c d x y g q : nat) :
  1+3*a=x -> 1+3*b=4*x -> 1+3*c=256*(x*y) -> 1+3*d=4*(x*y) ->
  x*(24*g)=x*(184+768*q+3827*y) ->
  1+(8*c+1+(29+96*a+2*g*(16*x))) =
    2+16*b+2*(2+8*q)*(64*x)+2*2892*(x*y)+d.
Proof.
  intros Q0 Q1 Q11 Q8 G.
  zify.
  ring_simplify in G.
  ring_simplify in Q0. ring_simplify in Q1.
  ring_simplify in Q11. ring_simplify in Q8.
  ring_simplify.
  replace (32*Z.of_nat g*Z.of_nat x)%Z with
    (32*Z.of_nat x*Z.of_nat g)%Z by (ring).
  repeat rewrite <- Z.mul_assoc in G.
  repeat rewrite <- Z.mul_assoc in Q8.
  repeat rewrite <- Z.mul_assoc in Q11.
  repeat rewrite <- Z.mul_assoc.
  remember (Z.of_nat x*Z.of_nat g)%Z as gx eqn:Egx in *.
  remember (Z.of_nat x*Z.of_nat q)%Z as qx eqn:Eqx in *.
  remember (Z.of_nat x*Z.of_nat y)%Z as xy eqn:Exy in *.
  clear Egx Eqx Exy.
  match goal with |- ?l = ?r => assert (Hlin : (3*(l-r)=0)%Z) end.
  - transitivity
      (8*((3*Z.of_nat c+1)-256*xy)
       +96*((3*Z.of_nat a+1)-Z.of_nat x)
       -16*((3*Z.of_nat b+1)-4*Z.of_nat x)
       -((3*Z.of_nat d+1)-4*xy)
       +4*(24*gx-(768*qx+3827*xy+184*Z.of_nat x)))%Z.
    + ring.
    + rewrite Q11, Q0, Q1, Q8, G. ring.
  - apply Z.mul_eq_0 in Hlin. destruct Hlin as [Hbad|Hlin]; [discriminate|].
    exact (proj1 (Z.sub_move_0_r _ _) Hlin).
Qed.

Lemma supply_budget r n :
  1+supply_f r n =
    2+16*q4(1+n)+2*(2+8*q16(2+r))*4^(3+n)
      +2*2892*4^(7+n+2*r)+q4(8+n+2*r).
Proof.
  assert (P1 : 4^(1+n)=4*4^n) by reflexivity.
  assert (P2 : 4^(2+n)=16*4^n).
  { change (4*(4*4^n)=16*4^n). nia. }
  assert (P3 : 4^(3+n)=64*4^n).
  { change (4*(4*(4*4^n))=64*4^n). nia. }
  assert (P7 : 4^(7+n+2*r)=4^n*4^(7+2*r)).
  { replace (7+n+2*r) with (n+(7+2*r)) by (lia). apply Nat.pow_add_r. }
  assert (P8 : 4^(8+n+2*r)=4*(4^n*4^(7+2*r))).
  { replace (8+n+2*r) with (1+(7+n+2*r)) by (lia).
    rewrite (Nat.pow_add_r 4 1 (7+n+2*r)), P7. reflexivity. }
  assert (P11 : 4^(n+11+2*r)=256*(4^n*4^(7+2*r))).
  { replace (n+11+2*r) with (4+(7+n+2*r)) by (lia).
    rewrite (Nat.pow_add_r 4 4 (7+n+2*r)), P7. reflexivity. }
  pose proof (q4_pow n) as Q0.
  pose proof (q4_pow (1+n)) as Q1.
  pose proof (q4_pow (n+11+2*r)) as Q11.
  pose proof (q4_pow (8+n+2*r)) as Q8.
  rewrite P1 in Q1. rewrite P11 in Q11. rewrite P8 in Q8.
  pose proof (f_equal (fun z : nat => 4^n*z) (supply_g_balance r)) as G.
  unfold supply_f. rewrite P2, P3, P7.
  apply budget_algebra; assumption.
Qed.

Definition e a b := 11+4*q4 (24+2*a+2*b)+48*q4 (7+2*b)
  +supply_g (3+a)*4^(9+2*b).

Lemma supply_index a b : supply_f (3+a) (7+2*b) = 8+2*e a b.
Proof.
  unfold supply_f, e.
  replace (7+2*b+11+2*(3+a)) with (24+2*a+2*b) by (lia).
  replace (2+(7+2*b)) with (9+2*b) by (lia). nia.
Qed.

Opaque e.

Lemma family_budget a b :
  2+16*q4(8+2*e a b)
    +2*(2+8*q16(5+b))*4^(10+2*e a b)
    +2*2892*4^(20+2*e a b+2*b)+q4(21+2*e a b+2*b)
  = 9+2*e b (e a b).
Proof.
  pose proof (supply_budget (3+b) (7+2*e a b)) as H.
  rewrite supply_index in H.
  replace (1+(7+2*e a b)) with (8+2*e a b) in H by (lia).
  replace (2+(3+b)) with (5+b) in H by (lia).
  replace (3+(7+2*e a b)) with (10+2*e a b) in H by (lia).
  replace (7+(7+2*e a b)+2*(3+b)) with (20+2*e a b+2*b) in H by (lia).
  replace (8+(7+2*e a b)+2*(3+b)) with (21+2*e a b+2*b) in H by (lia).
  symmetry.
  replace (9+2*e b (e a b)) with (1+(8+2*e b (e a b)))
    by (clear H; lia).
  exact H.
Qed.

(* Full reset family, retaining an arbitrary older side. *)
Lemma service_tail hs u v w :
  segRLs tm hs [] u v -> segRLs tm hs [] (u++w) (v++w).
Proof. intro H; eapply segRLs_concat; [exact H|constructor]. Qed.

Lemma F_T_service n k u v :
  segRLs tm (hg^^k) [] u v ->
  segRLs tm (hf^^(2*k*4^n)) [] (tw^^(1+n)++u) (tw^^(1+n)++v).
Proof. intro H; eapply segRLs_concat; [apply F_T_calls|exact H]. Qed.

Definition family_word a b :=
  tw ++ lw^^(9+2*e a b) ++ kw ++ tw ++ lw ++
    tw^^(24+2*a+2*b) ++ zw ++ kw ++ tw ++ [0;0].

Definition family_col a b :=
  tw^^(11+2*e a b) ++ zw ++ jw ++ lw ++ mw^^(7+2*b) ++
    rw ++ dw ++ cw^^(3+a) ++ dw^^2 ++ cw ++ tw ++ [0;0].

Definition family_mid a b :=
  tw^^(21+2*e a b+2*b) ++ zw ++ tw^^2 ++ jw ++
    cw^^(3+a) ++ dw^^2 ++ cw ++ tw ++ [0;0].

Definition family_end a b :=
  zw ++ jw^^(26+2*e a b+2*b) ++ mw ++ rw ++
    cw^^(1+a) ++ dw^^2 ++ cw ++ tw ++ [0;0].

Lemma family_column a b :
  segRLs tm (hf^^(2+16*q4(8+2*e a b))) []
    (family_word a b) (family_col a b).
Proof.
  unfold family_word, family_col.
  replace (9+2*e a b) with (1+(8+2*e a b)) by (lia).
  replace (11+2*e a b) with ((8+2*e a b)+3) by (lia).
  eapply COLUMN. rewrite <- supply_index.
  replace (24+2*a+2*b) with (7+2*b+11+2*(3+a)) by (lia).
  applys_eq (@service_tail _ _ _ (tw++[0;0]) (SUPPLY (3+a) (7+2*b)));
    repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma M_block r :
  segRLs tm (hg^^(2+8*q16(2+r))) []
    (zw++jw++lw++mw^^(1+2*r)++rw++dw)
    (tw^^(4+2*r)++zw++tw^^2++jw).
Proof.
  change (segRLs tm (hg^^(2+8*q16(2+r))) []
    ((zw++jw++lw++mw^^(1+2*r))++(rw++dw))
    (tw^^(4+2*r)++(zw++tw^^2++jw))).
  eapply segRLs_concat; [apply M_ODD|apply HGH_F].
Qed.

Lemma family_m a b :
  segRLs tm (hf^^(2*(2+8*q16(5+b))*4^(10+2*e a b))) []
    (family_col a b) (family_mid a b).
Proof.
  unfold family_col, family_mid.
  replace (21+2*e a b+2*b) with ((11+2*e a b)+(10+2*b)) by (lia).
  rewrite (lpow_add _ (11+2*e a b) (10+2*b) tw).
  repeat rewrite <- app_assoc.
  replace (11+2*e a b) with (1+(10+2*e a b)) by (lia).
  apply F_T_service.
  replace (5+b) with (2+(3+b)) by (lia).
  replace (7+2*b) with (1+2*(3+b)) by (lia).
  replace (10+2*b) with (4+2*(3+b)) by (lia).
  applys_eq (@service_tail _ _ _ (cw^^(3+a)++dw^^2++cw++tw++[0;0])
    (M_block (3+b))); repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma family_finish a b :
  segRLs tm
    (hf^^(2*2892*4^(20+2*e a b+2*b)+q4(21+2*e a b+2*b))) []
    (family_mid a b) (family_end a b).
Proof.
  unfold family_mid, family_end.
  rewrite (lpow_add _ (2*2892*4^(20+2*e a b+2*b))
    (q4(21+2*e a b+2*b)) hf).
  change (segRLs tm
    (hf^^(2*2892*4^(20+2*e a b+2*b))++hf^^(q4(21+2*e a b+2*b)))
    ([]++[])
    (tw^^(21+2*e a b+2*b)++zw++tw^^2++jw++cw^^(3+a)++dw^^2++cw++tw++[0;0])
    (zw++jw^^(26+2*e a b+2*b)++mw++rw++cw^^(1+a)++dw^^2++cw++tw++[0;0])).
  eapply (segRLs_trans
    (w2:=tw^^(21+2*e a b+2*b)++jw^^6++mw++rw++
      cw^^(1+a)++dw^^2++cw++tw++[0;0])).
  - replace (21+2*e a b+2*b) with (1+(20+2*e a b+2*b)) by (lia).
    apply F_T_service.
    replace (3+a) with (2+(1+a)) by (lia).
    eapply (segRLs_concat (w1:=zw++tw^^2++jw++cw^^(2+(1+a)))
      (w2:=jw^^6++mw++rw++cw^^(1+a))); [apply PACKET|constructor].
  - replace (26+2*e a b+2*b) with ((20+2*e a b+2*b)+6) by (lia).
    rewrite (lpow_add _ (20+2*e a b+2*b) 6 jw).
    replace (21+2*e a b+2*b) with (1+(20+2*e a b+2*b)) by (lia).
    applys_eq (@service_tail _ _ _
      (jw^^6++mw++rw++cw^^(1+a)++dw^^2++cw++tw++[0;0])
      (F_normalize (20+2*e a b+2*b)));
      repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma family_services a b :
  segRLs tm (hf^^(9+2*e b (e a b))) [] (family_word a b) (family_end a b).
Proof.
  rewrite <- family_budget.
  replace
    (2+16*q4(8+2*e a b)+2*(2+8*q16(5+b))*4^(10+2*e a b)
      +2*2892*4^(20+2*e a b+2*b)+q4(21+2*e a b+2*b))
    with ((2+16*q4(8+2*e a b))+
      (2*(2+8*q16(5+b))*4^(10+2*e a b)+
       (2*2892*4^(20+2*e a b+2*b)+q4(21+2*e a b+2*b)))) by (lia).
  repeat rewrite lpow_add.
  change (segRLs tm
    (hf^^(2+16*q4(8+2*e a b))++
      (hf^^(2*(2+8*q16(5+b))*4^(10+2*e a b))++
        (hf^^(2*2892*4^(20+2*e a b+2*b))++hf^^(q4(21+2*e a b+2*b)))))
    ([]++([]++[])) (family_word a b) (family_end a b)).
  eapply segRLs_trans; [apply family_column|].
  eapply segRLs_trans; [apply family_m|].
  rewrite <- lpow_add. apply family_finish.
Qed.

Definition family_prefix a :=
  [1] ++ rw ++ cw^^a ++ dw^^2 ++ cw ++ tw ++ [0;0].

Definition family_after_zero a b :=
  tw ++ lw^^(9+2*e b (e a b)) ++ kw ++ tw ++ aw ++
    tw^^(25+2*e a b+2*b) ++ [1;0;1] ++ bw ++ rw ++
    cw^^(1+a) ++ dw^^2 ++ cw ++ tw ++ [0;0].

Lemma bw_comm_T n : bw ++ tw^^n = tw^^n ++ bw.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (tw++(bw++tw^^n) = tw++(tw^^n++bw)). rewrite IH. reflexivity.
Qed.

(* The final C is not consumed by PACKET.  It is indispensable to this
   exact reset-language recut; arbitrary older bits remain after it. *)
Lemma reset_recut a k :
  aw++tw^^(1+k)++[1;0;1]++bw++rw++cw^^(1+a)++dw^^2++cw++tw++[0;0]
  = lw++tw^^k++zw++kw++tw++[0;0]++family_prefix a.
Proof.
  unfold family_prefix.
  change
    (lw++((bw++tw^^k)++[1;0;1]++bw++rw++cw++cw^^a++dw^^2++cw++tw++[0;0])
    =lw++tw^^k++zw++kw++tw++[0;0]++[1]++rw++cw^^a++dw^^2++cw++tw++[0;0]).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma family_recut a b :
  family_after_zero a b = family_word b (e a b) ++ family_prefix a.
Proof.
  unfold family_after_zero, family_word.
  replace (25+2*e a b+2*b) with (1+(24+2*b+2*e a b)) by (lia).
  rewrite reset_recut. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma P_service n k w1 w2 u :
  segRLs tm (hf^^k) [] w1 w2 ->
  P n (w1 *> u) -->* P (n+k) (w2 *> u).
Proof.
  intro H. apply P_calls. eapply segRLs_sideRLs_concat; [exact H|constructor].
Qed.

Lemma P_service_zero k w1 w2 u :
  segRLs tm (hf^^k) [] w1 w2 ->
  P 0 (w1 *> u) -->* P k (w2 *> u).
Proof. exact (P_service 0 k w1 w2 u). Qed.

Lemma family_reset a b u :
  P (9+2*e b (e a b)) (family_end a b *> u) -->+
  P 0 (family_word b (e a b) *> family_prefix a *> u).
Proof.
  rewrite <- Str_app_assoc, <- family_recut.
  unfold family_end, family_after_zero.
  replace (26+2*e a b+2*b) with (1+(25+2*e a b+2*b)) by (lia).
  repeat rewrite Str_app_assoc.
  apply zero_return.
Qed.

Definition I a b u := P 0 (family_word a b *> u).

Lemma I_step a b u :
  I a b u -->+ I b (e a b) (family_prefix a *> u).
Proof.
  unfold I.
  apply (@evstep_progress_trans tm
    (P 0 (family_word a b *> u))
    (P (9+2*e b (e a b)) (family_end a b *> u))
    (P 0 (family_word b (e a b) *> family_prefix a *> u))).
  - exact (P_service_zero (9+2*e b (e a b))
      (family_word a b) (family_end a b) u (family_services a b)).
  - exact (family_reset a b u).
Qed.

Theorem family_nonhalt a b u : ~ halts tm (I a b u).
Proof.
  apply (progress_nonhalt_simple tm (nat*nat*side)%type
    (fun i => let '(x,y,v) := i in I x y v) (a,b,u)).
  intros [[x y] v]. exists (y,e x y,family_prefix x *> v). apply I_step.
Qed.
Lemma tower_budget a b :
  2+16*q4(8+2*b)+2*(2+8*q16(5+a))*4^(10+2*b)
    +2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b)=9+2*e a b.
Proof.
  pose proof (supply_budget (3+a) (7+2*b)) as H.
  rewrite supply_index in H.
  replace (1+(7+2*b)) with (8+2*b) in H by lia.
  replace (2+(3+a)) with (5+a) in H by lia.
  replace (3+(7+2*b)) with (10+2*b) in H by lia.
  replace (7+(7+2*b)+2*(3+a)) with (20+2*a+2*b) in H by lia.
  replace (8+(7+2*b)+2*(3+a)) with (21+2*a+2*b) in H by lia.
  symmetry. replace (9+2*e a b) with (1+(8+2*e a b)) by (clear H;lia).
  exact H.
Qed.

Definition supply_count n k j :=
  8*q4 k+1+(4*4^(1+k)+(29+96*q4 n+2*j*4^(2+n))).

Lemma reset_supply n k z j u v w t : k+2=3+n+z ->
  segRLs tm hh [] u v -> segRLs tm (hg^^2) [] v w ->
  segRLs tm (hg^^j++hf) [] (tw^^z++w) t ->
  segRLs tm (hf^^(supply_count n k j)) []
    (zw++lw++tw^^k++u) (zw++jw++lw++mw^^n++t).
Proof.
  intros E H K L. unfold supply_count. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ (8*q4 k) (1+(4*4^(1+k)+(29+96*q4 n+2*j*4^(2+n)))) hf).
  rewrite (lpow_add _ 1 (4*4^(1+k)+(29+96*q4 n+2*j*4^(2+n))) hf).
  rewrite (lpow_add _ (4*4^(1+k)) (29+96*q4 n+2*j*4^(2+n)) hf).
  change (segRLs tm (hf^^(8*q4 k)++(hf++(hf^^(4*4^(1+k))++
    hf^^(29+96*q4 n+2*j*4^(2+n))))) ([]++([]++([]++[])))
    (zw++lw++tw^^k++u) (zw++jw++lw++mw^^n++t)).
  eapply (segRLs_trans (w2:=zw++lw++mw^^k++u)).
  - applys_eq (@service_tail _ _ _ u (BIN k)); repeat rewrite <- app_assoc; reflexivity.
  - eapply (segRLs_trans (w2:=tw^^(2+k)++v)).
    + change (segRLs tm hf [] ((zw++lw++mw^^k)++u) (tw^^(2+k)++v)).
      eapply segRLs_concat; [apply F_outer|exact H].
    + eapply (segRLs_trans (w2:=tw^^(2+k)++w)); [apply (F_T_service (1+k) 2); exact K|].
      replace (2+k) with (3+n+z) by lia.
      rewrite (lpow_add _ (3+n) z tw).
      applys_eq (@segRLs_concat tm _ _ _ _ _ _ _ (NEAR_WRAP n j) L);
        repeat rewrite <- app_assoc; reflexivity.
Qed.

End Common.

Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC0LA_1LD1RF_1RB0LE_---1LA_1RD0RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Module Base <: Model.
Definition tm := TM12.tm.
Definition f := B.
Definition h := F.
Definition p := A.
Definition rules : Kernel tm f h p.
Proof.
  constructor.
  1-11: finite_rule.
  - intros n r s H. unfold root.
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
  - intros n k r. unfold root. cbn [to_DH_config f h p]. es' n k & r.
Qed.
End Base.
Module Import Facts := Common Base.

(* Native blank-start entrance. The 3686-step finite prefix is followed
   by symbolic reset services; all large counts and old tails are retained.
   The later reset contracts are proved with variables before specializing
   them to the actual tower-scale parameters. *)
Ltac run_service H :=
  let HH := fresh "HH" in pose proof H as HH;
  repeat rewrite Str_app_assoc in HH; follow HH; clear HH.

Lemma init_raw12 : c0 -->*
  P 0 (tw *> lw^^12 *> kw *> tw *> lw *> zw *> [1] *> 0inf).
Proof. unfold P, root. cbn [to_DH_config Base.p]. esx. Qed.

Lemma init_F11 : segRLs tm (hf^^11) []
  (zw++lw++zw) (tw++kw++jw).
Proof. finite_rule. Qed.

Opaque q4 Nat.pow.

Definition init_h := 2+16*q4 11+2*4^14+q4 15.

Lemma init_services : segRLs tm (hf^^init_h) []
  (tw++lw^^12++kw++tw++lw++zw) (zw++jw^^16).
Proof.
  unfold init_h. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ (2+16*q4 11) (2*4^14+q4 15) hf).
  rewrite (lpow_add _ (2*4^14) (q4 15) hf).
  change (segRLs tm (hf^^(2+16*q4 11)++(hf^^(2*4^14)++hf^^(q4 15)))
    ([]++([]++[])) (tw++lw^^12++kw++tw++lw++zw) (zw++jw^^16)).
  eapply (segRLs_trans (w2:=tw^^15++kw++jw)).
  - change (segRLs tm (hf^^(2+16*q4 11)) []
      (tw++lw^^(1+11)++kw++tw++lw++zw) (tw^^(11+3)++(tw++kw++jw))).
    apply COLUMN. exact init_F11.
  - eapply (segRLs_trans (w2:=tw^^15++jw^^2)).
    + change (segRLs tm (hf^^(2*1*4^14)) []
        (tw^^(1+14)++(kw++jw)) (tw^^(1+14)++(jw++jw))).
      apply F_T_service. eapply segRLs_concat; [apply G_K|constructor].
    + change (segRLs tm (hf^^(q4(1+14))) []
        (tw^^(1+14)++jw^^2) ((zw++jw^^14)++jw^^2)).
      eapply segRLs_concat; [apply F_normalize|constructor].
Qed.

Opaque init_h.

Lemma one_return n k r :
  P n (zw *> jw^^(1+k) *> [1] *> r) -->+
  P (1+n) (tw *> lw *> tw^^k *> [0] *> r).
Proof. unfold P, root. cbn [to_DH_config Base.p]. es' n k & r. Qed.

Lemma ten_return n k :
  P n (zw *> lw *> mw^^k *> 0inf) -->+
  P 0 (tw *> lw^^n *> kw *> tw^^(2+k) *> [1;0;1] *> 0inf).
Proof. unfold P, root. cbn [to_DH_config Base.p]. es' n k. Qed.

Definition m0 := init_h+2+8*q4 15.
Opaque m0.

Lemma init_anchor : c0 -->*
  P 0 (tw *> lw^^m0 *> kw *> tw^^17 *> [1;0;1] *> 0inf).
Proof.
  follow init_raw12.
  run_service (@P_service_zero init_h _ _ ([1] *> 0inf) init_services).
  follow100 (one_return init_h 15 0inf).
  replace ([0] *> 0inf) with 0inf by solve_const0_eq.
  run_service (@P_service (1+init_h) 1 tw zw (lw *> tw^^15 *> 0inf) F_T).
  run_service (@P_service (1+init_h+1) (8*q4 15) _ _ 0inf (BIN 15)).
  Transparent m0.
  replace (1+init_h+1+8*q4 15) with m0 by (unfold m0; lia).
  follow100 (ten_return m0 15). finish.
Qed.

Opaque m0.

Lemma G_digits j k n u v w :
  segRLs tm (hg^^n) [] u v -> segRLs tm (hg^^k) [] tw w ->
  segRLs tm (hg^^(n*4^j+k*q4 j)) [] (tw^^j++u) (w^^j++v).
Proof.
  intros H K. induction j as [|j IH].
  - rewrite Nat.pow_0_r. Transparent q4.
    change (segRLs tm (hg^^(n*1+k*0)) [] u v). Opaque q4.
    replace (n*1+k*0) with n by lia. exact H.
  - replace (n*4^(S j)+k*q4(S j)) with (4*(n*4^j+k*q4 j)+k).
    + change (w^^(S j)++v) with ((w++w^^j)++v). rewrite <- app_assoc.
      change (segRLs tm (hg^^(4*(n*4^j+k*q4 j)+k)) []
        (tw++(tw^^j++u)) (w++(w^^j++v))).
      eapply G_append; [exact IH|apply service_tail; exact K].
    + Transparent q4 Nat.pow.
      change (4*(n*4^j+k*q4 j)+k = n*(4*4^j)+k*(1+4*q4 j)). ring.
Qed.

Lemma short1_start r : segRLs tm (hg^^2) []
  (zw++tw++jw^^r++tw^^2++lw) (tw^^(r+2)++zw++tw++lw).
Proof.
  change (segRLs tm (hg++hg) ([]++[])
    (zw++tw++jw^^r++tw^^2++lw) (tw^^(r+2)++zw++tw++lw)).
  eapply (segRLs_trans (w2:=lw++kw++jw^^r++tw^^2++lw)).
  - eapply segRLs_concat; [apply G_Z|apply service_tail, G_T].
  - replace (r+2) with (2+r) by lia.
    change (segRLs tm hg [] (lw++(kw++(jw^^r++(tw++(tw++lw)))))
      (tw++(tw++(tw^^r++(zw++(tw++lw)))))).
    eapply segRLs_concat; [apply G_L|].
    eapply segRLs_concat; [apply H_K|].
    eapply segRLs_concat; [apply F_Js|apply service_tail, F_T].
Qed.

Definition short1_count r := 2+8*4^(1+r)+2*q4(r+4).
Lemma short1 r : segRLs tm (hg^^(short1_count r)) []
  (zw++tw++jw^^r++tw^^2++lw) (jw^^(r+4)++mw).
Proof.
  unfold short1_count. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ 2 (8*4^(1+r)+2*q4(r+4)) hg).
  rewrite (lpow_add _ (8*4^(1+r)) (2*q4(r+4)) hg).
  change (segRLs tm (hg^^2++(hg^^(8*4^(1+r))++hg^^(2*q4(r+4))))
    ([]++([]++[])) (zw++tw++jw^^r++tw^^2++lw) (jw^^(r+4)++mw)).
  eapply segRLs_trans; [apply short1_start|].
  eapply (segRLs_trans (w2:=tw^^(r+4)++mw)); [|apply service_tail, G_normalize].
  replace (r+2) with ((1+r)+1) by lia.
  replace (r+4) with ((1+r)+3) by lia.
  rewrite (lpow_add _ (1+r) 1 tw), (lpow_add _ (1+r) 3 tw).
  repeat rewrite <- app_assoc.
  eapply segRLs_concat; [apply G_Ts|].
  change (segRLs tm (hg^^8) [] ((tw++zw++tw)++lw) (tw^^3++mw)).
  eapply segRLs_concat; [apply ODD_END|apply F_L].
Qed.

Definition reset_count p j := 2+16*q4 p+2*j*4^(2+p)+q4(3+p).

Lemma reset_services p j k w v u :
  segRLs tm (hf^^p) [] (zw++w) v ->
  segRLs tm (hg^^j) [] v (jw^^(1+k)++[0;0]++u) ->
  segRLs tm (hf^^(reset_count p j)) []
    (tw++lw^^(1+p)++kw++tw++w) (zw++jw^^(3+p+k)++[0;0]++u).
Proof.
  intros H K. unfold reset_count.
  replace (2+16*q4 p+2*j*4^(2+p)+q4(3+p))
    with ((2+16*q4 p)+(2*j*4^(2+p)+q4(3+p))) by lia.
  rewrite (lpow_add _ (2+16*q4 p) (2*j*4^(2+p)+q4(3+p)) hf).
  rewrite (lpow_add _ (2*j*4^(2+p)) (q4(3+p)) hf).
  change (segRLs tm (hf^^(2+16*q4 p)++(hf^^(2*j*4^(2+p))++hf^^(q4(3+p))))
    ([]++([]++[])) (tw++lw^^(1+p)++kw++tw++w) (zw++jw^^(3+p+k)++[0;0]++u)).
  eapply (segRLs_trans (w2:=tw^^(3+p)++v)).
  - replace (3+p) with (p+3) by lia. apply COLUMN, H.
  - eapply (segRLs_trans (w2:=tw^^(3+p)++jw^^(1+k)++[0;0]++u)).
    + apply F_T_service. exact K.
    + replace (3+p+k) with ((2+p)+(1+k)) by lia.
      rewrite (lpow_add _ (2+p) (1+k) jw).
      applys_eq (@service_tail _ _ _ (jw^^(1+k)++[0;0]++u) (F_normalize (2+p)));
        repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma reset_run p j k w v u r :
  segRLs tm (hf^^p) [] (zw++w) v ->
  segRLs tm (hg^^j) [] v (jw^^(1+k)++[0;0]++u) ->
  P 0 ((tw++lw^^(1+p)++kw++tw++w) *> r) -->+
  P 0 (tw *> lw^^(reset_count p j) *> kw *> tw *> aw *>
       tw^^(2+p+k) *> [1;0;1] *> u *> r).
Proof.
  intros H K. eapply evstep_progress_trans.
  - exact (P_service_zero _ _ _ r (reset_services p j k w v u H K)).
  - repeat rewrite Str_app_assoc. apply zero_return.
Qed.
Opaque q4 Nat.pow.

Definition p0 := (7*4^13+2*q4 11)*4.

Lemma first_g : segRLs tm (hg^^p0) [] (tw^^16)
  (tw++jw^^11++tw^^2++cw).
Proof.
  assert (H : segRLs tm (hg^^(7*4^2)) [] (tw^^4) (tw^^2++cw)).
  { change (segRLs tm (hg^^(7*4^2)) [] (tw^^2++tw^^2) (tw^^2++cw)).
    eapply segRLs_concat; [apply G_Ts|apply G7]. }
  assert (K : segRLs tm (hg^^(7*4^13+2*q4 11)) [] (tw^^15)
    (jw^^11++tw^^2++cw)).
  { replace (7*4^13) with ((7*4^2)*4^11)
      by (rewrite <- Nat.mul_assoc, <- Nat.pow_add_r; reflexivity).
    change (segRLs tm (hg^^((7*4^2)*4^11+2*q4 11)) []
      (tw^^11++tw^^4) (jw^^11++(tw^^2++cw))).
    apply G_digits; [exact H|apply G2_T]. }
  unfold p0. rewrite Nat.mul_comm, <- (Nat.add_0_r (4*(7*4^13+2*q4 11))).
  eapply G_append; [exact K|constructor].
Qed.

Transparent m0 init_h p0.
Lemma m0_first : m0 = 1+2*p0.
Proof.
  unfold m0, init_h, p0. pose proof (q4_pow 15) as H.
  replace 15 with (2+13) in H by reflexivity.
  rewrite (Nat.pow_add_r 4 2 13) in H.
  replace 14 with (1+13) by reflexivity.
  rewrite (Nat.pow_add_r 4 1 13).
  Transparent Nat.pow.
  change (1+3*q4 15=16*4^13) in H.
  change (2+16*q4 11+2*(4*4^13)+q4 15+2+8*q4 15
    =1+2*((7*4^13+2*q4 11)*4)). Opaque Nat.pow.
  generalize dependent (q4 15). generalize (q4 11) (4^13).
  intros. nia.
Qed.
Opaque Nat.pow init_h m0.

Definition a0 := p0-4.
Lemma m0_odd : m0=9+2*a0.
Proof.
  rewrite m0_first. unfold a0.
  assert (4<=p0).
  { unfold p0. pose proof (Nat.pow_nonzero 4 13 ltac:(discriminate)) as H.
    generalize dependent (4^13). generalize (q4 11). intros. nia. }
  generalize dependent p0. intros. lia.
Qed.
Opaque p0 a0.

Lemma first_supply : segRLs tm (hf^^(2*p0)) []
  (zw++tw^^16) (zw++tw++jw^^11++tw^^2++cw).
Proof.
  assert (H : segRLs tm (hf^^2) hg zw zw).
  { change (segRLs tm (hf++hf) (hg++[]) zw zw).
    eapply segRLs_trans; [apply F_Z|apply F_T]. }
  replace (2*p0) with (p0*2) by lia. rewrite lpow_mul.
  eapply segRLs_concat; [apply service_repeat, H|apply first_g].
Qed.

Definition reset_index p j := 7+40*q4 p+16*j*4^p.
Lemma reset_index_spec p j : reset_count p j=9+2*reset_index p j.
Proof.
  unfold reset_count, reset_index.
  rewrite (q4_add 3 p), (Nat.pow_add_r 4 2 p).
  Transparent q4 Nat.pow.
  change (2+16*q4 p+2*j*(16*4^p)+(21+64*q4 p)
    =9+2*(7+40*q4 p+16*j*4^p)). ring.
Qed.
Opaque q4 Nat.pow.

Definition b0 := reset_index (2*p0) (short1_count 11).
Definition u1 := zw++kw++tw++bw.
Opaque b0.

Lemma recut1 k : aw++tw^^(1+k)++[1;0;1]++bw++rw++[1;0;1]
  =lw++tw^^k++u1.
Proof.
  unfold u1.
  change (lw++((bw++tw^^k)++[1;0;1]++bw++rw++[1;0;1])
    =lw++tw^^k++zw++kw++tw++bw).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma first_reset : c0 -->*
  P 0 (tw *> lw^^(9+2*b0) *> kw *> tw *> lw *> tw^^(23+2*a0) *> u1 *> 0inf).
Proof.
  follow init_anchor.
  rewrite m0_first.
  assert (H : segRLs tm (hf^^(2*p0)) [] (zw++(tw^^16++[1;0;1]))
    ((zw++tw++jw^^11++tw^^2++lw)++rw++[1;0;1])).
  { applys_eq (@service_tail _ _ _ [1;0;1] first_supply);
      repeat rewrite <- app_assoc; reflexivity. }
  assert (K : segRLs tm (hg^^(short1_count 11)) []
    ((zw++tw++jw^^11++tw^^2++lw)++rw++[1;0;1])
    (jw^^15++[0;0]++bw++rw++[1;0;1])).
  { applys_eq (@service_tail _ _ _ (rw++[1;0;1]) (short1 11));
      repeat rewrite <- app_assoc; reflexivity. }
  pose proof (reset_run (2*p0) (short1_count 11) 14 _ _ _ 0inf H K) as R.
  repeat rewrite Str_app_assoc in R. follow100 R.
  rewrite reset_index_spec.
  change (reset_index (2*p0) (short1_count 11)) with b0.
  replace (2+2*p0+14) with (1+(23+2*a0))
    by (pose proof m0_first; pose proof m0_odd; lia).
  repeat rewrite <- Str_app_assoc. repeat rewrite <- app_assoc. rewrite recut1.
  repeat rewrite Str_app_assoc. finish.
Qed.

(* A reset's real BIN exhaustion and its two subsequent g calls. *)
Definition ww := rw++tw++bw.
Definition v1 := kw++kw++tw++bw.
Definition w1 := cw++tw++bw.
Definition tail1 := kw^^11++lw++mw++ww.
Definition j1 := 4*(4*(3*4^12+q4 12)+3)+1.

Lemma second_g : segRLs tm (hg^^j1) [] (tw^^15++w1) (kw++cw++tail1).
Proof.
  assert (H : segRLs tm (hg^^3) [] (tw++w1) (lw++mw++ww)).
  { unfold w1, ww. eapply segRLs_concat; [apply G3_T|].
    exact (@service_tail _ _ _ (rw++tw++bw) F_L). }
  assert (K : segRLs tm (hg^^(3*4^12+q4 12)) []
    (tw^^13++w1) (kw^^12++lw++mw++ww)).
  { pose proof (@G_digits 12 1 3 (tw++w1) (lw++mw++ww) kw H G_T) as R.
    rewrite Nat.mul_1_l in R. repeat rewrite <- app_assoc in R. exact R. }
  assert (L : segRLs tm (hg^^(4*(3*4^12+q4 12)+3)) []
    (tw^^14++w1) (cw++tail1)).
  { eapply G_append; [exact K|]. unfold tail1.
    eapply (segRLs_concat (w2:=lw)); [apply G3_T|].
    exact (@service_tail _ _ _ (kw^^11++lw++mw++ww) F_K). }
  unfold j1. eapply G_append; [exact L|apply service_tail, G_T].
Qed.
Opaque j1.

Lemma second_supply a : segRLs tm (hf^^(supply_count (7+2*a) (23+2*a) j1)) []
  (zw++lw++tw^^(23+2*a)++u1)
  (zw++jw++lw++mw^^(7+2*a)++rw++cw++tail1).
Proof.
  eapply (reset_supply (7+2*a) (23+2*a) 15 j1 u1 v1 w1 (rw++cw++tail1));
    [lia|unfold u1,v1; apply service_tail,H_Z|unfold v1,w1|].
  - exact (@service_tail _ _ _ (tw++bw) G2_KK).
  - change (segRLs tm (hg^^j1++hf) ([]++[]) (tw^^15++w1) (rw++cw++tail1)).
    eapply segRLs_trans; [apply second_g|apply service_tail,F_K].
Qed.

Lemma HGH_C : segRLs tm (hh++hg++hh) [] (rw++cw) (zw++tw++jw).
Proof. finite_rule. Qed.

Lemma short2 : segRLs tm (hg^^44) [] (zw++tw++jw++kw) (jw^^3++rw).
Proof. finite_rule. Qed.

Definition clean2 a := 2+8*q16(5+a)+44*4^(10+2*a)+2*q4(10+2*a).
Definition v2 := aw++kw^^10++lw++mw++ww.
Definition u2 := zw++[1;1;0]++kw^^10++lw++mw++ww.

Lemma second_clean a : segRLs tm (hg^^(clean2 a)) []
  (zw++jw++lw++mw^^(7+2*a)++rw++cw++tail1)
  (jw^^(13+2*a)++[0;0]++v2).
Proof.
  unfold clean2. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ (2+8*q16(5+a)) (44*4^(10+2*a)+2*q4(10+2*a)) hg).
  rewrite (lpow_add _ (44*4^(10+2*a)) (2*q4(10+2*a)) hg).
  change (segRLs tm (hg^^(2+8*q16(5+a))++
    (hg^^(44*4^(10+2*a))++hg^^(2*q4(10+2*a)))) ([]++([]++[]))
    (zw++jw++lw++mw^^(7+2*a)++rw++cw++tail1)
    (jw^^(13+2*a)++[0;0]++v2)).
  eapply (segRLs_trans (w2:=tw^^(10+2*a)++zw++tw++jw++tail1)).
  - replace (7+2*a) with (1+2*(3+a)) by lia.
    replace (10+2*a) with (4+2*(3+a)) by lia.
    replace (5+a) with (2+(3+a)) by lia.
    change (segRLs tm (hg^^(2+8*q16(2+(3+a)))) []
      ((zw++jw++lw++mw^^(1+2*(3+a)))++((rw++cw)++tail1))
      (tw^^(4+2*(3+a))++((zw++tw++jw)++tail1))).
    eapply segRLs_concat; [apply M_ODD|apply service_tail,HGH_C].
  - eapply (segRLs_trans (w2:=tw^^(10+2*a)++jw^^3++[0;0]++v2)).
    + eapply segRLs_concat; [apply G_Ts|].
      unfold tail1,v2. applys_eq (@service_tail _ _ _ (kw^^10++lw++mw++ww) short2);
        repeat rewrite <- app_assoc; reflexivity.
    + replace (13+2*a) with ((10+2*a)+3) by lia.
      rewrite (lpow_add _ (10+2*a) 3 jw).
      applys_eq (@service_tail _ _ _ (jw^^3++[0;0]++v2) (G_normalize (10+2*a)));
        repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma recut2 k : aw++tw^^(1+k)++[1;0;1]++v2 = lw++tw^^k++u2.
Proof.
  unfold v2,u2.
  change (lw++((bw++tw^^k)++[1;0;1]++aw++kw^^10++lw++mw++ww)
    =lw++tw^^k++zw++[1;1;0]++kw^^10++lw++mw++ww).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Transparent j1.
Lemma first_constants : 72+128*short1_count 11 = 8*q4 16+4*4^17+32*j1.
Proof.
  unfold short1_count,j1.
  change (72+128*(2+8*4^12+2*q4(3+12))
    =8*q4(4+12)+4*4^(5+12)+32*(4*(4*(3*4^12+q4 12)+3)+1)).
  rewrite (q4_add 3 12), (q4_add 4 12), (Nat.pow_add_r 4 5 12).
  pose proof (q4_pow 12) as H.
  Transparent q4 Nat.pow.
  change (72+128*(2+8*4^12+2*(21+64*q4 12))
    =8*(85+256*q4 12)+4*(1024*4^12)+32*(4*(4*(3*4^12+q4 12)+3)+1)).
  Opaque q4 Nat.pow.
  generalize dependent (4^12). generalize (q4 12). intros. nia.
Qed.
Opaque j1 short1_count.

Lemma first_budget n : reset_count (1+n) (short1_count 11)
  =1+supply_count n (16+n) j1.
Proof.
  unfold reset_count,supply_count.
  replace (2+(1+n)) with (n+3) by lia.
  replace (3+(1+n)) with (n+4) by lia.
  replace (1+(16+n)) with (n+17) by lia.
  replace (2+n) with (n+2) by lia.
  replace (1+n) with (n+1) by lia.
  replace (16+n) with (n+16) by lia.
  rewrite (q4_add n 1), (q4_add n 4), (q4_add n 16).
  rewrite (Nat.pow_add_r 4 n 3), (Nat.pow_add_r 4 n 17), (Nat.pow_add_r 4 n 2).
  Transparent q4 Nat.pow.
  change (q4 1) with (1%nat). rewrite Nat.mul_1_r.
  change (2+16*(q4 n+4^n)+2*short1_count 11*(4^n*64)+(q4 n+4^n*85)
    =1+(8*(q4 n+4^n*q4 16)+1+(4*(4^n*4^17)+(29+96*q4 n+2*j1*(4^n*16))))).
  Opaque q4 Nat.pow.
  pose proof (f_equal (fun t=>t*4^n) first_constants) as H.
  pose proof (q4_pow n) as K.
  generalize dependent (4^n). generalize (q4 n) (q4 16) (4^17) (short1_count 11) j1.
  intros. nia.
Qed.

Lemma first_supply_index : supply_count (7+2*a0) (23+2*a0) j1=8+2*b0.
Proof.
  pose proof (first_budget (7+2*a0)) as H.
  replace (1+(7+2*a0)) with (2*p0) in H
    by (pose proof m0_first; pose proof m0_odd; lia).
  rewrite reset_index_spec in H. change (reset_index (2*p0) (short1_count 11)) with b0 in H.
  replace (16+(7+2*a0)) with (23+2*a0) in H by lia. lia.
Qed.

Definition c0_index := reset_index (8+2*b0) (clean2 a0).
Opaque c0_index.

Lemma second_run a b : supply_count (7+2*a) (23+2*a) j1=8+2*b ->
  P 0 (tw *> lw^^(9+2*b) *> kw *> tw *> lw *> tw^^(23+2*a) *> u1 *> 0inf) -->*
  P 0 (tw *> lw^^(9+2*reset_index (8+2*b) (clean2 a)) *> kw *> tw *> lw *>
    tw^^(21+2*a+2*b) *> u2 *> 0inf).
Proof.
  intro E. pose proof (second_supply a) as H. rewrite E in H.
  pose proof (reset_run (8+2*b) (clean2 a) (12+2*a)
    (lw++tw^^(23+2*a)++u1) _ v2 0inf H (second_clean a)) as R.
  repeat rewrite Str_app_assoc in R. follow100 R.
  rewrite reset_index_spec.
  replace (2+(8+2*b)+(12+2*a)) with (1+(21+2*a+2*b)) by lia.
  repeat rewrite <- Str_app_assoc. repeat rewrite <- app_assoc. rewrite recut2.
  repeat rewrite Str_app_assoc. finish.
Qed.

Lemma second_reset : c0 -->*
  P 0 (tw *> lw^^(9+2*c0_index) *> kw *> tw *> lw *>
    tw^^(21+2*a0+2*b0) *> u2 *> 0inf).
Proof. follow first_reset. apply second_run,first_supply_index. Qed.

Definition pair_count r := 125*16^r+13*q16 r.

Lemma pair_digits r : segRLs tm (hg^^(pair_count r)) []
  (tw^^(4+2*r)) (kw++cw^^r++dw).
Proof.
  induction r as [|r IH].
  - unfold pair_count. Transparent q16 Nat.pow. exact G125.
  - assert (E : pair_count (S r)=16*pair_count r+13).
    { unfold pair_count. change (125*(16*16^r)+13*(1+16*q16 r)
        =16*(125*16^r+13*q16 r)+13). ring. }
    rewrite E. replace (4+2*S r) with (2+(4+2*r)) by lia.
    rewrite (lpow_add _ 2 (4+2*r) tw), (lpow_add _ (16*pair_count r) 13 hg).
    change (segRLs tm (hg^^(16*pair_count r)++hg^^13) ([]++[])
      (tw^^2++tw^^(4+2*r)) (kw++cw++cw^^r++dw)).
    eapply (segRLs_trans (w2:=tw^^2++kw++cw^^r++dw)).
    + replace (16*pair_count r) with (pair_count r*4^2) by lia.
      eapply segRLs_concat; [apply G_Ts|exact IH].
    + applys_eq (@service_tail _ _ _ (cw^^r++dw) G_pair13);
        repeat rewrite <- app_assoc; reflexivity.
Qed.
Opaque q4 q16 Nat.pow.

Definition j2 r := 64*pair_count r+61.
Lemma third_g r : segRLs tm (hg^^(j2 r)) []
  (tw^^(7+2*r)) (kw++dw++cw^^r++dw).
Proof.
  unfold j2. replace (7+2*r) with (3+(4+2*r)) by lia.
  rewrite (lpow_add _ 3 (4+2*r) tw), (lpow_add _ (64*pair_count r) 61 hg).
  change (segRLs tm (hg^^(64*pair_count r)++hg^^61) ([]++[])
    (tw^^3++tw^^(4+2*r)) (kw++dw++cw^^r++dw)).
  eapply (segRLs_trans (w2:=tw^^3++kw++cw^^r++dw)).
  - Transparent Nat.pow.
    replace (64*pair_count r) with (pair_count r*4^3)
      by (change (pair_count r*64=64*pair_count r); apply Nat.mul_comm).
    Opaque Nat.pow.
    eapply segRLs_concat; [apply G_Ts|apply pair_digits].
  - applys_eq (@service_tail _ _ _ (cw^^r++dw) G_last61);
      repeat rewrite <- app_assoc; reflexivity.
Qed.
Opaque Nat.pow.

Definition v3 := kw++[1;1;0]++kw^^10++lw++mw++ww.
Definition w3 := lw++[0;1;0]++kw^^10++lw++mw++ww.
Definition tail3 a := cw^^(3+a)++dw++w3.

Lemma third_H : segRLs tm hh [] u2 v3.
Proof. unfold u2,v3. apply service_tail,H_Z. Qed.
Lemma third_G2 : segRLs tm (hg^^2) [] v3 w3.
Proof. finite_rule. Qed.

Lemma third_supply a b :
  segRLs tm (hf^^(supply_count (7+2*b) (21+2*a+2*b) (j2(3+a)))) []
    (zw++lw++tw^^(21+2*a+2*b)++u2)
    (zw++jw++lw++mw^^(7+2*b)++rw++dw++tail3 a).
Proof.
  eapply (reset_supply (7+2*b) (21+2*a+2*b) (7+2*(3+a)) (j2(3+a))
    u2 v3 w3 (rw++dw++tail3 a)); [lia|apply third_H|apply third_G2|].
  change (segRLs tm (hg^^(j2(3+a))++hf) ([]++[])
    (tw^^(7+2*(3+a))++w3) (rw++dw++tail3 a)).
  eapply (segRLs_trans (w2:=kw++dw++tail3 a)).
  - unfold tail3. applys_eq (@service_tail _ _ _ w3 (third_g (3+a)));
      repeat rewrite <- app_assoc; reflexivity.
  - exact (@service_tail _ _ _ (dw++tail3 a) F_K).
Qed.

Definition clean3 b := 2+8*q16(5+b)+2892*4^(10+2*b)+2*q4(10+2*b).
Definition v4 a := bw++rw++cw^^(1+a)++dw++w3.

Lemma third_clean a b : segRLs tm (hg^^(clean3 b)) []
  (zw++jw++lw++mw^^(7+2*b)++rw++dw++tail3 a)
  (jw^^(16+2*b)++[0;0]++v4 a).
Proof.
  unfold clean3. rewrite <- Nat.add_assoc.
  rewrite (lpow_add _ (2+8*q16(5+b)) (2892*4^(10+2*b)+2*q4(10+2*b)) hg).
  rewrite (lpow_add _ (2892*4^(10+2*b)) (2*q4(10+2*b)) hg).
  change (segRLs tm (hg^^(2+8*q16(5+b))++
    (hg^^(2892*4^(10+2*b))++hg^^(2*q4(10+2*b)))) ([]++([]++[]))
    (zw++jw++lw++mw^^(7+2*b)++rw++dw++tail3 a)
    (jw^^(16+2*b)++[0;0]++v4 a)).
  eapply (segRLs_trans (w2:=tw^^(10+2*b)++zw++tw^^2++jw++tail3 a)).
  - replace (7+2*b) with (1+2*(3+b)) by lia.
    replace (10+2*b) with (4+2*(3+b)) by lia.
    replace (5+b) with (2+(3+b)) by lia.
    applys_eq (@service_tail _ _ _ (tail3 a) (M_block (3+b)));
      repeat rewrite <- app_assoc; reflexivity.
  - eapply (segRLs_trans (w2:=tw^^(10+2*b)++jw^^6++[0;0]++v4 a)).
    + eapply segRLs_concat; [apply G_Ts|].
      unfold tail3,v4. replace (3+a) with (2+(1+a)) by lia.
      applys_eq (@service_tail _ _ _ (dw++w3) (PACKET (1+a)));
        repeat rewrite <- app_assoc; reflexivity.
    + replace (16+2*b) with ((10+2*b)+6) by lia.
      rewrite (lpow_add _ (10+2*b) 6 jw).
      applys_eq (@service_tail _ _ _ (jw^^6++[0;0]++v4 a) (G_normalize (10+2*b)));
        repeat rewrite <- app_assoc; reflexivity.
Qed.

Definition v5 a := [1]++rw++cw^^a++dw++w3.
Lemma recut3 a k : aw++tw^^(1+k)++[1;0;1]++v4 a
  =lw++tw^^k++zw++kw++tw++[0;0]++v5 a.
Proof.
  unfold v4,v5.
  change (lw++((bw++tw^^k)++[1;0;1]++bw++rw++cw++cw^^a++dw++w3)
    =lw++tw^^k++zw++kw++tw++[0;0]++[1]++rw++cw^^a++dw++w3).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma reset_supply_balance n t j k :
  9+16*j=q4 t+2*4^t+4*k ->
  reset_count (1+n) j=1+supply_count n (n+t) k.
Proof.
  intro H. unfold reset_count,supply_count.
  replace (2+(1+n)) with (n+3) by lia.
  replace (3+(1+n)) with (n+4) by lia.
  replace (1+(n+t)) with (n+(1+t)) by lia.
  replace (2+n) with (n+2) by lia.
  replace (1+n) with (n+1) by lia.
  rewrite (q4_add n 1), (q4_add n 4), (q4_add n t).
  rewrite (Nat.pow_add_r 4 n 3), (Nat.pow_add_r 4 n (1+t)), (Nat.pow_add_r 4 n 2).
  Transparent q4 Nat.pow.
  change (q4 1) with (1%nat). rewrite Nat.mul_1_r.
  change (2+16*(q4 n+4^n)+2*j*(4^n*64)+(q4 n+4^n*85)
    =1+(8*(q4 n+4^n*q4 t)+1+(4*(4^n*(4*4^t))+(29+96*q4 n+2*k*(4^n*16))))).
  Opaque q4 Nat.pow.
  pose proof (f_equal (fun z=>8*z*4^n) H) as K.
  pose proof (q4_pow n). nia.
Qed.

Lemma bridge_constants a :
  9+16*clean2 a = q4(14+2*a)+2*4^(14+2*a)+4*j2(3+a).
Proof.
  pose proof (q4_pow (10+2*a)) as H1.
  pose proof (q4_pow (14+2*a)) as H2.
  pose proof (q16_pow (3+a)) as H3.
  unfold clean2,j2,pair_count.
  assert (E1 : 4^(10+2*a)=256*16^(3+a)).
  { replace (10+2*a) with (4+2*(3+a)) by lia.
    rewrite Nat.pow_add_r,pow4_double. Transparent Nat.pow. reflexivity. }
  assert (E2 : 4^(14+2*a)=(256*256)*16^(3+a)).
  { replace (14+2*a) with (4+(4+2*(3+a))) by lia.
    rewrite (Nat.pow_add_r 4 4), (Nat.pow_add_r 4 4), pow4_double.
    change (256*(256*16^(3+a))=(256*256)*16^(3+a)). ring. }
  rewrite E1 in H1 |- *. rewrite E2 in H2 |- *.
  Transparent q16.
  change (q16(5+a)) with (1+16*(1+16*q16(3+a))).
  Opaque q16 Nat.pow.
  generalize dependent (16^(3+a)). generalize (q16(3+a)) (q4(10+2*a)) (q4(14+2*a)).
  intros. nia.
Qed.

Lemma bridge_budget a b : reset_count (8+2*b) (clean2 a)
  =1+supply_count (7+2*b) (21+2*a+2*b) (j2(3+a)).
Proof.
  replace (8+2*b) with (1+(7+2*b)) by lia.
  replace (21+2*a+2*b) with ((7+2*b)+(14+2*a)) by lia.
  apply reset_supply_balance,bridge_constants.
Qed.

Lemma third_supply_index :
  supply_count (7+2*b0) (21+2*a0+2*b0) (j2(3+a0))=8+2*c0_index.
Proof.
  pose proof (bridge_budget a0 b0) as H. rewrite reset_index_spec in H.
  change (reset_index (8+2*b0) (clean2 a0)) with c0_index in H. lia.
Qed.

Lemma final_budget a b : reset_count (8+2*b) (clean3 a)=9+2*e a b.
Proof.
  rewrite <- tower_budget. unfold reset_count,clean3.
  replace (20+2*a+2*b) with ((10+2*a)+(10+2*b)) by lia.
  replace (21+2*a+2*b) with ((11+2*b)+(10+2*a)) by lia.
  rewrite (Nat.pow_add_r 4 (10+2*a) (10+2*b)), (q4_add (11+2*b) (10+2*a)).
  replace (11+2*b) with (1+(10+2*b)) by lia.
  rewrite (Nat.pow_add_r 4 1 (10+2*b)).
  Transparent Nat.pow.
  change (2+16*q4(8+2*b)+
    2*(2+8*q16(5+a)+2892*4^(10+2*a)+2*q4(10+2*a))*4^(10+2*b)+q4(11+2*b)
    =2+16*q4(8+2*b)+2*(2+8*q16(5+a))*4^(10+2*b)
      +2*2892*(4^(10+2*a)*4^(10+2*b))
      +(q4(11+2*b)+(4*4^(10+2*b))*q4(10+2*a))).
  Opaque Nat.pow.
  generalize (q4(8+2*b)) (q16(5+a)) (4^(10+2*a)) (q4(10+2*a))
    (4^(10+2*b)) (q4(11+2*b)). intros. zify. ring.
Qed.
Opaque Nat.pow.

Lemma third_run a b c : supply_count (7+2*b) (21+2*a+2*b) (j2(3+a))=8+2*c ->
  P 0 (tw *> lw^^(9+2*c) *> kw *> tw *> lw *>
    tw^^(21+2*a+2*b) *> u2 *> 0inf) -->* I b c (v5 a *> 0inf).
Proof.
  intro E. pose proof (third_supply a b) as H. rewrite E in H.
  pose proof (reset_run (8+2*c) (clean3 b) (15+2*b)
    (lw++tw^^(21+2*a+2*b)++u2) _ (v4 a) 0inf H (third_clean a b)) as R.
  repeat rewrite Str_app_assoc in R. follow100 R.
  rewrite final_budget.
  replace (2+(8+2*c)+(15+2*b)) with (1+(24+2*b+2*c)) by lia.
  repeat rewrite <- Str_app_assoc. repeat rewrite <- app_assoc. rewrite recut3.
  unfold I,family_word. repeat rewrite Str_app_assoc. finish.
Qed.

Lemma init_family : c0 -->* I b0 c0_index (v5 a0 *> 0inf).
Proof. follow second_reset. apply third_run,third_supply_index. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init_family|apply family_nonhalt]. Qed.
End TM12.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LF_1RA0LD_1RC1LC_1RB0RB_---1LD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Module Base <: Model.
Definition tm := TM13.tm.
Definition f := C.
Definition h := E.
Definition p := D.
Definition rules : Kernel tm f h p.
Proof.
  constructor.
  1-11: finite_rule.
  - intros n r s H. unfold root.
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
  - intros n k r. unfold root. cbn [to_DH_config f h p]. es' n k & r.
Qed.
End Base.
Module Import Facts := Common Base.

Lemma init_raw :
  c0 -->* P 0 (tw *> lw^^6 *> kw *> tw^^3 *> zw *> [1] *> 0inf).
Proof. unfold P, root. cbn [to_DH_config Base.p]. esx. Qed.

Lemma anchor_return n k :
  P n (zw *> jw^^k *> zw *> [1] *> 0inf) -->+
  P 0 (tw *> lw^^n *> kw *> tw *> aw *> bw *> tw^^k *> [1;0;1] *> 0inf).
Proof. unfold P, root. cbn [to_DH_config Base.p]. es' n k. Qed.

(* Compact blank-start entrance: the short native initialization is followed
   by symbolic services through three resets into I.  Only short radix
   remainders are computed; no long service list is expanded. *)
Lemma entry_F5 : segRLs tm (hf^^5) [] (zw++tw^^2) (tw++lw++zw).
Proof. finite_rule. Qed.

Lemma entry_G4 : segRLs tm (hg^^4) [] (tw++lw++zw) (tw^^2++kw).
Proof. finite_rule. Qed.

Lemma entry_G30 : segRLs tm (hg^^30) [] (tw++lw++zw) (jw^^3).
Proof.
  change (segRLs tm (hg^^4++(hg^^16++hg^^10)) ([]++([]++[]))
    (tw++lw++zw) (jw^^3)).
  eapply (segRLs_trans (w2:=tw^^2++kw)); [apply entry_G4|].
  eapply (segRLs_trans (w2:=tw^^2++jw)).
  - eapply segRLs_concat; [apply (G_Ts 2 1)|apply G_K].
  - change (segRLs tm (hg^^(2*q4 2)) [] (tw^^2++jw) (jw^^2++jw)).
    eapply segRLs_concat; [apply G_normalize|constructor].
Qed.

(* Decimal 155646 = radix-four 0211333332, retained in small factors. *)
Definition entry10_calls := 4*(4*(4*2431+3)+3)+2.

Lemma entry_G10 : segRLs tm (hg^^entry10_calls) [] (tw^^10)
  (jw++lw++mw^^4++rw++kw++jw++tw).
Proof.
  assert (H2 : segRLs tm (hg^^2) [] (tw^^2) (jw++tw)).
  { eapply (G_append 0 2 tw tw); [constructor|finite_rule]. }
  assert (H3 : segRLs tm (hg^^9) [] (tw^^3) (kw++jw++tw)).
  { eapply (G_append 2 1 (tw^^2) (jw++tw)); [exact H2|finite_rule]. }
  assert (H4 : segRLs tm (hg^^37) [] (tw^^4) (kw++kw++jw++tw)).
  { eapply (G_append 9 1 (tw^^3) (kw++jw++tw)); [exact H3|finite_rule]. }
  assert (H5 : segRLs tm (hg^^151) [] (tw^^5) (lw++rw++kw++jw++tw)).
  { eapply (G_append 37 3 (tw^^4) (kw++kw++jw++tw)); [exact H4|finite_rule]. }
  assert (H6 : segRLs tm (hg^^607) [] (tw^^6) (lw++mw++rw++kw++jw++tw)).
  { eapply (G_append 151 3 (tw^^5) (lw++rw++kw++jw++tw)); [exact H5|finite_rule]. }
  assert (H7 : segRLs tm (hg^^2431) [] (tw^^7) (lw++mw^^2++rw++kw++jw++tw)).
  { eapply (G_append 607 3 (tw^^6) (lw++mw++rw++kw++jw++tw)); [exact H6|finite_rule]. }
  assert (H8 : segRLs tm (hg^^(4*2431+3)) [] (tw^^8) (lw++mw^^3++rw++kw++jw++tw)).
  { eapply (G_append 2431 3 (tw^^7) (lw++mw^^2++rw++kw++jw++tw)); [exact H7|finite_rule]. }
  assert (H9 : segRLs tm (hg^^(4*(4*2431+3)+3)) [] (tw^^9)
    (lw++mw^^4++rw++kw++jw++tw)).
  { eapply (G_append (4*2431+3) 3 (tw^^8) (lw++mw^^3++rw++kw++jw++tw));
      [exact H8|finite_rule]. }
  unfold entry10_calls.
  eapply (G_append (4*(4*2431+3)+3) 2 (tw^^9) (lw++mw^^4++rw++kw++jw++tw));
    [exact H9|finite_rule].
Qed.

Definition entry_b := [1;0;0;1;0;0;0;1;0;1;1;0;0;1;1;0;1]%sym.
Definition entry_first_calls := 8*q4 9+1+(2*entry10_calls+1).

Lemma entry_first_service : segRLs tm (hf^^entry_first_calls) []
  (zw++lw++tw^^10++[1;0;1])
  (zw++jw++lw++mw^^4++rw++aw++entry_b).
Proof.
  unfold entry_first_calls.
  replace (8*q4 9+1+(2*entry10_calls+1))
    with (8*q4 9+(1+(2*entry10_calls+1))) by lia.
  repeat rewrite lpow_add.
  change (segRLs tm (hf^^(8*q4 9)++(hf++(hf^^(2*entry10_calls)++hf)))
    ([]++([]++([]++[]))) (zw++lw++tw^^10++[1;0;1])
    (zw++jw++lw++mw^^4++rw++aw++entry_b)).
  eapply (segRLs_trans (w2:=zw++lw++mw^^9++tw++[1;0;1])).
  - change (segRLs tm (hf^^(8*q4 9)) []
      ((zw++lw++tw^^9)++(tw++[1;0;1]))
      ((zw++lw++mw^^9)++(tw++[1;0;1]))).
    eapply segRLs_concat; [apply BIN|constructor].
  - eapply (segRLs_trans (w2:=tw^^11++lw++[1;0;1])).
    + change (segRLs tm hf []
        ((zw++lw++mw^^9)++(tw++[1;0;1])) (tw^^11++(lw++[1;0;1]))).
      eapply segRLs_concat; [apply F_outer|].
      eapply segRLs_concat; [apply H_T|constructor].
    + eapply (segRLs_trans
        (w2:=tw++jw++lw++mw^^4++rw++kw++jw++tw++lw++[1;0;1])).
      * replace (2*entry10_calls) with (2*entry10_calls*4^0) by lia.
        change (segRLs tm (hf^^(2*entry10_calls*4^0)) []
          (tw++(tw^^10++(lw++[1;0;1])))
          (tw++((jw++lw++mw^^4++rw++kw++jw++tw)++(lw++[1;0;1])))).
        eapply segRLs_concat; [apply (F_T_calls 0)|].
        eapply segRLs_concat; [apply entry_G10|constructor].
      * unfold entry_b.
        eapply segRLs_concat; [apply F_T|constructor].
Qed.

(* Decimal 30589 = radix-four 13131331. *)
Definition entry8_calls := 4*(4*1911+3)+1.

Lemma entry_G8 : segRLs tm (hg^^entry8_calls) [] (tw^^8)
  (kw++dw++cw^^2).
Proof.
  assert (H2 : segRLs tm (hg^^7) [] (tw^^2) cw).
  { apply G7. }
  assert (H3 : segRLs tm (hg^^29) [] (tw^^3) (kw++cw)).
  { eapply (G_append 7 1 (tw^^2) cw); [exact H2|finite_rule]. }
  assert (H4 : segRLs tm (hg^^119) [] (tw^^4) (cw^^2)).
  { eapply (G_append 29 3 (tw^^3) (kw++cw)); [exact H3|finite_rule]. }
  assert (H5 : segRLs tm (hg^^477) [] (tw^^5) (kw++cw^^2)).
  { eapply (G_append 119 1 (tw^^4) (cw^^2)); [exact H4|finite_rule]. }
  assert (H6 : segRLs tm (hg^^1911) [] (tw^^6) (cw^^3)).
  { eapply (G_append 477 3 (tw^^5) (kw++cw^^2)); [exact H5|finite_rule]. }
  assert (H7 : segRLs tm (hg^^(4*1911+3)) [] (tw^^7) (dw++cw^^2)).
  { eapply (G_append 1911 3 (tw^^6) (cw^^3)); [exact H6|finite_rule]. }
  unfold entry8_calls.
  eapply (G_append (4*1911+3) 1 (tw^^7) (dw++cw^^2)); [exact H7|finite_rule].
Qed.

Definition entry_clean_calls := 2+8*q16 2+8*4^4+2*q4 8.

Lemma entry_clean : segRLs tm (hg^^entry_clean_calls) []
  (zw++jw++lw++mw^^4++rw++aw) (jw^^8++[0;0]).
Proof.
  unfold entry_clean_calls.
  replace (2+8*q16 2+8*4^4+2*q4 8)
    with (2+(8*q16 2+(8*4^4+2*q4 8))) by lia.
  repeat rewrite lpow_add.
  change (segRLs tm (hg^^2++(hg^^(8*q16 2)++(hg^^(8*4^4)++hg^^(2*q4 8))))
    ([]++([]++([]++[]))) (zw++jw++lw++mw^^4++rw++aw) (jw^^8++[0;0])).
  eapply (segRLs_trans (w2:=tw++zw++tw^^5++jw++aw)).
  - change (segRLs tm (hg^^2) []
      ((zw++jw++lw++mw^^4)++(rw++aw))
      ((tw++zw++tw^^5)++(jw++aw))).
    eapply segRLs_concat; [apply G_Mstart|].
    eapply segRLs_concat; [apply H_R|constructor].
  - eapply (segRLs_trans (w2:=tw^^5++zw++tw++jw++aw)).
    + change (segRLs tm (hg^^(8*q16 2)) []
        ((tw++zw++tw^^4)++(tw++jw++aw))
        ((tw^^5++zw)++(tw++jw++aw))).
      eapply segRLs_concat; [apply SHIFTS|constructor].
    + eapply (segRLs_trans (w2:=tw^^8++[0;0])).
      * change (segRLs tm (hg^^(8*4^4)) []
          (tw^^4++((tw++zw++tw)++(jw++aw)))
          (tw^^4++(tw^^3++(tw++[0;0])))).
        eapply segRLs_concat; [apply G_Ts|].
        eapply segRLs_concat; [apply ODD_END|].
        eapply segRLs_concat; [apply F_J|apply F_A].
      * eapply segRLs_concat; [apply G_normalize|constructor].
Qed.

Definition entry_m := 2+16*q4 5+2*30*4^7+q4 8.

Lemma entry_services : segRLs tm (hf^^entry_m) []
  (tw++lw^^6++kw++tw^^3++zw++[1]) (zw++jw^^10++zw++[1]).
Proof.
  unfold entry_m.
  replace (2+16*q4 5+2*30*4^7+q4 8)
    with ((2+16*q4 5)+(2*30*4^7+q4 8)) by lia.
  repeat rewrite lpow_add.
  change (segRLs tm (hf^^(2+16*q4 5)++(hf^^(2*30*4^7)++hf^^(q4 8)))
    ([]++([]++[])) (tw++lw^^6++kw++tw^^3++zw++[1])
    (zw++jw^^10++zw++[1])).
  eapply (segRLs_trans (w2:=tw^^8++tw++lw++zw++zw++[1])).
  - change (segRLs tm (hf^^(2+16*q4 5)) []
      (tw++lw^^6++kw++tw++(tw^^2++zw++[1]))
      (tw^^8++(tw++lw++zw++zw++[1]))).
    apply COLUMN.
    change (segRLs tm (hf^^5) [] ((zw++tw^^2)++(zw++[1]))
      ((tw++lw++zw)++(zw++[1]))).
    eapply segRLs_concat; [apply entry_F5|constructor].
  - eapply (segRLs_trans (w2:=tw^^8++jw^^3++zw++[1])).
    + change (segRLs tm (hf^^(2*30*4^7)) []
        (tw^^8++((tw++lw++zw)++(zw++[1])))
        (tw^^8++(jw^^3++(zw++[1])))).
      eapply segRLs_concat; [apply F_T_calls|].
      eapply segRLs_concat; [apply entry_G30|constructor].
    + change (segRLs tm (hf^^(q4 8)) []
        (tw^^8++(jw^^3++zw++[1]))
        ((zw++jw^^7)++(jw^^3++zw++[1]))).
      eapply segRLs_concat; [apply F_normalize|constructor].
Qed.

Lemma entry_before_anchor : c0 -->*
  P entry_m (zw *> jw^^10 *> zw *> [1] *> 0inf).
Proof.
  follow init_raw.
  assert (H : sideRLs tm (hf^^entry_m)
    (tw *> lw^^6 *> kw *> tw^^3 *> zw *> [1] *> 0inf)
    (zw *> jw^^10 *> zw *> [1] *> 0inf)).
  { repeat rewrite <- Str_app_assoc.
    eapply segRLs_sideRLs_concat; [apply entry_services|constructor]. }
  follow (P_calls 0 _ _ _ H).
  finish.
Qed.

Lemma entry_after_anchor : c0 -->*
  P 0 (tw *> lw^^entry_m *> kw *> tw *> aw *> bw *> tw^^10 *>
    [1;0;1] *> 0inf).
Proof. follow entry_before_anchor. follow100 (anchor_return entry_m 10). finish. Qed.

Lemma entry_m_count : entry_m = 1+(8*q4 9+1+(2*entry10_calls+1)).
Proof. unfold entry_m, entry10_calls; cbn [q4 Nat.pow]; lia. Qed.

Definition entry_a0 := 167+505*1000.

Lemma entry_m_odd : entry_m = 9+2*entry_a0.
Proof. unfold entry_m, entry_a0; cbn [q4 Nat.pow]; lia. Qed.

(* All later work keeps this symbolic, never constructing a million-cell Nat. *)
Opaque entry_m.

Definition entry_H := 2+16*q4 entry_first_calls.
Definition entry_B := entry_H+2*entry_clean_calls*4^(1+entry_m)+q4(2+entry_m).

Lemma entry_m_first : entry_m = 1+entry_first_calls.
Proof. exact entry_m_count. Qed.

Opaque entry_m entry_first_calls entry_clean_calls.

Lemma entry_second_services : segRLs tm (hf^^entry_B) []
  (tw++lw^^entry_m++kw++tw++aw++bw++tw^^10++[1;0;1])
  (zw++jw^^(entry_m+9)++[0;0]++entry_b).
Proof.
  unfold entry_B, entry_H.
  rewrite <- (Nat.add_assoc (2+16*q4 entry_first_calls)
    (2*entry_clean_calls*4^(1+entry_m)) (q4(2+entry_m))).
  rewrite (lpow_add _ (2+16*q4 entry_first_calls)
    (2*entry_clean_calls*4^(1+entry_m)+q4(2+entry_m)) hf).
  rewrite (lpow_add _ (2*entry_clean_calls*4^(1+entry_m)) (q4(2+entry_m)) hf).
  change (segRLs tm
    (hf^^(2+16*q4 entry_first_calls)++
      (hf^^(2*entry_clean_calls*4^(1+entry_m))++hf^^(q4(2+entry_m))))
    ([]++([]++[]))
    (tw++lw^^entry_m++kw++tw++lw++tw^^10++[1;0;1])
    (zw++jw^^(entry_m+9)++[0;0]++entry_b)).
  eapply (segRLs_trans
    (w2:=tw^^(entry_m+2)++zw++jw++lw++mw^^4++rw++aw++entry_b)).
  - rewrite entry_m_first.
    replace (1+entry_first_calls+2) with (entry_first_calls+3) by (lia).
    apply COLUMN. apply entry_first_service.
  - eapply (segRLs_trans (w2:=tw^^(entry_m+2)++jw^^8++[0;0]++entry_b)).
    + replace (entry_m+2) with (1+(1+entry_m)) by (lia).
      change (segRLs tm (hf^^(2*entry_clean_calls*4^(1+entry_m))) []
        (tw^^(1+(1+entry_m))++((zw++jw++lw++mw^^4++rw++aw)++entry_b))
        (tw^^(1+(1+entry_m))++((jw^^8++[0;0])++entry_b))).
      eapply segRLs_concat; [apply F_T_calls|].
      eapply segRLs_concat; [apply entry_clean|constructor].
    + replace (entry_m+2) with (1+(1+entry_m)) by (lia).
      replace (2+entry_m) with (1+(1+entry_m)) by (lia).
      replace (entry_m+9) with ((1+entry_m)+8) by (lia).
      rewrite (lpow_add _ (1+entry_m) 8 jw).
      repeat rewrite <- app_assoc.
      change (segRLs tm (hf^^(q4(1+(1+entry_m)))) []
        (tw^^(1+(1+entry_m))++(jw^^8++[0;0]++entry_b))
        ((zw++jw^^(1+entry_m))++(jw^^8++[0;0]++entry_b))).
      eapply segRLs_concat; [apply F_normalize|constructor].
Qed.

Opaque entry_H entry_B.

Lemma entry_before_zero : c0 -->*
  P entry_B (zw *> jw^^(entry_m+9) *> [0;0] *> entry_b *> 0inf).
Proof.
  follow entry_after_anchor.
  repeat rewrite <- Str_app_assoc.
  repeat rewrite <- app_assoc.
  exact (P_service_zero entry_B
    (tw++lw^^entry_m++kw++tw++aw++bw++tw^^10++[1;0;1])
    (zw++jw^^(entry_m+9)++[0;0]++entry_b) 0inf entry_second_services).
Qed.

Lemma entry_after_zero : c0 -->*
  P 0 (tw *> lw^^entry_B *> kw *> tw *> aw *> tw^^(entry_m+8) *>
    [1;0;1] *> entry_b *> 0inf).
Proof.
  follow entry_before_zero.
  replace (entry_m+9) with (1+(entry_m+8)) by (lia).
  follow100 (zero_return entry_B (entry_m+8) (entry_b *> 0inf)). finish.
Qed.

Definition entry_b0 := 501+183*1000+(522+550*1000)*q4 entry_m.

Lemma second_budget_identity m p : q4 m=1+4*q4 p ->
  2+16*q4 p+2*(876+45*1000)*4^(1+m)+q4(2+m)
  =9+2*(501+183*1000+(522+550*1000)*q4 m).
Proof.
  intro H. pose proof (q4_pow m) as P4.
  rewrite (q4_add 2 m).
  change (2+16*q4 p+2*(876+45*1000)*(4*4^m)+(5+16*q4 m)
    =9+2*(501+183*1000+(522+550*1000)*q4 m)).
  nia.
Qed.

Transparent entry_H entry_B entry_clean_calls.

Lemma entry_B_index : entry_B = 9+2*entry_b0.
Proof.
  assert (C : entry_clean_calls = 876+45*1000).
  { unfold entry_clean_calls; cbn [q4 q16 Nat.pow]; lia. }
  unfold entry_B, entry_H, entry_b0.
  rewrite C. apply second_budget_identity.
  rewrite entry_m_first. reflexivity.
Qed.

Opaque entry_H entry_B entry_clean_calls entry_b0.

(* Verified generic third-entrance services; no concrete large corridor.
   All words are reversed.  In particular u0=11Z, u1=11K, u2=10L
   in the original readable orientation.  Every exterior is protected. *)
Definition third_u0 := zw ++ [1;1].
Definition third_u1 := kw ++ [1;1].
Definition third_u2 := lw ++ bw.

Lemma third_H : segRLs tm hh [] third_u0 third_u1.
Proof. unfold third_u0, third_u1; apply service_tail, H_Z. Qed.

Lemma third_G2 : segRLs tm (hg^^2) [] third_u1 third_u2.
Proof.
  unfold third_u1, third_u2.
  change (segRLs tm (hg++hg) ([]++[]) (kw++[1;1]) (lw++bw)).
  eapply (segRLs_trans (w2:=jw++[1;1])).
  - apply service_tail, G_K.
  - eapply segRLs_concat; [apply G_J|apply F_11].
Qed.

Lemma third_G8F :
  segRLs tm (hg^^entry8_calls++hf) []
    (tw^^8++third_u2) (rw++dw++cw^^2++third_u2).
Proof.
  change (segRLs tm (hg^^entry8_calls++hf) ([]++[])
    (tw^^8++third_u2) (rw++dw++cw^^2++third_u2)).
  eapply (segRLs_trans (w2:=kw++dw++cw^^2++third_u2)).
  - applys_eq (@service_tail _ _ _ third_u2 entry_G8);
      repeat rewrite <- app_assoc; reflexivity.
  - eapply segRLs_concat; [apply F_K|constructor].
Qed.

Definition third_f n :=
  8*q4(n+9) + (1 + (4*4^(n+10) +
    (29+96*q4 n+2*entry8_calls*4^(2+n)))).
Definition third_input n := zw++lw++tw^^(n+9)++third_u0.
Definition third_output n :=
  zw++jw++lw++mw^^n++rw++dw++cw^^2++third_u2.

(* n=m-2.  This is BIN(m+7), OUTER, two actual g calls on the
   older word, then NEAR_WRAP with its ordered g^entry8_calls;f request. *)
Lemma third_supply n :
  segRLs tm (hf^^(third_f n)) [] (third_input n) (third_output n).
Proof.
  unfold third_f, third_input, third_output.
  replace (n+10) with (1+(n+9)) by lia.
  rewrite Nat.add_assoc.
  change (segRLs tm (hf^^(supply_count n (n+9) entry8_calls)) []
    (zw++lw++tw^^(n+9)++third_u0)
    (zw++jw++lw++mw^^n++rw++dw++cw^^2++third_u2)).
  apply (reset_supply n (n+9) 8 entry8_calls third_u0 third_u1 third_u2
    (rw++dw++cw^^2++third_u2));
    [lia|apply third_H|apply third_G2|apply third_G8F].
Qed.

(* The large application only has to provide this scalar equality. *)
Definition third_source a b :=
  tw++lw^^(9+2*b)++kw++tw++lw++tw^^(16+2*a)++third_u0.
Definition third_col a b := tw^^(11+2*b)++third_output (7+2*a).
Definition third_mid a b :=
  tw^^(21+2*a+2*b)++zw++tw^^2++jw++cw^^2++third_u2.
Definition third_end a b :=
  zw++jw^^(26+2*a+2*b)++mw++rw++third_u2.

Lemma third_column a b : third_f (7+2*a)=8+2*b ->
  segRLs tm (hf^^(2+16*q4(8+2*b))) []
    (third_source a b) (third_col a b).
Proof.
  intro H. unfold third_source, third_col, third_input in *.
  replace (9+2*b) with (1+(8+2*b)) by (lia).
  replace (11+2*b) with ((8+2*b)+3) by (lia).
  replace (16+2*a) with ((7+2*a)+9) by (lia).
  apply COLUMN. rewrite <- H. apply third_supply.
Qed.

(* This reuses the already proved THREE-call h/g/h guard HGH_F through
   M_block; the older C^2 and u2 are untouched. *)
Lemma third_m a b :
  segRLs tm (hf^^(2*(2+8*q16(5+a))*4^(10+2*b))) []
    (third_col a b) (third_mid a b).
Proof.
  unfold third_col, third_output, third_mid.
  replace (21+2*a+2*b) with ((11+2*b)+(10+2*a)) by (lia).
  rewrite (lpow_add _ (11+2*b) (10+2*a) tw).
  repeat rewrite <- app_assoc.
  replace (11+2*b) with (1+(10+2*b)) by (lia).
  apply F_T_service.
  replace (5+a) with (2+(3+a)) by (lia).
  replace (7+2*a) with (1+2*(3+a)) by (lia).
  replace (10+2*a) with (4+2*(3+a)) by (lia).
  applys_eq (@service_tail _ _ _ (cw^^2++third_u2) (M_block (3+a)));
    repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma third_finish a b :
  segRLs tm
    (hf^^(2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b))) []
    (third_mid a b) (third_end a b).
Proof.
  unfold third_mid, third_end.
  rewrite (lpow_add _ (2*2892*4^(20+2*a+2*b)) (q4(21+2*a+2*b)) hf).
  change (segRLs tm
    (hf^^(2*2892*4^(20+2*a+2*b))++hf^^(q4(21+2*a+2*b)))
    ([]++[]) (tw^^(21+2*a+2*b)++zw++tw^^2++jw++cw^^2++third_u2)
    (zw++jw^^(26+2*a+2*b)++mw++rw++third_u2)).
  eapply (segRLs_trans
    (w2:=tw^^(21+2*a+2*b)++jw^^6++mw++rw++third_u2)).
  - replace (21+2*a+2*b) with (1+(20+2*a+2*b)) by (lia).
    apply F_T_service.
    applys_eq (@service_tail _ _ _ third_u2 (PACKET 0));
      repeat rewrite <- app_assoc; reflexivity.
  - replace (26+2*a+2*b) with ((20+2*a+2*b)+6) by (lia).
    rewrite (lpow_add _ (20+2*a+2*b) 6 jw).
    replace (21+2*a+2*b) with (1+(20+2*a+2*b)) by (lia).
    applys_eq (@service_tail _ _ _ (jw^^6++mw++rw++third_u2)
      (F_normalize (20+2*a+2*b)));
      repeat rewrite <- app_assoc; reflexivity.
Qed.

Lemma third_services a b : third_f (7+2*a)=8+2*b ->
  segRLs tm (hf^^(9+2*e a b)) [] (third_source a b) (third_end a b).
Proof.
  intro H. rewrite <- tower_budget.
  rewrite <- (Nat.add_assoc
    (2+16*q4(8+2*b)+2*(2+8*q16(5+a))*4^(10+2*b))
    (2*2892*4^(20+2*a+2*b)) (q4(21+2*a+2*b))).
  rewrite <- (Nat.add_assoc (2+16*q4(8+2*b))
    (2*(2+8*q16(5+a))*4^(10+2*b))
    (2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b))).
  rewrite (lpow_add _ (2+16*q4(8+2*b))
    (2*(2+8*q16(5+a))*4^(10+2*b)+
      (2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b))) hf).
  rewrite (lpow_add _ (2*(2+8*q16(5+a))*4^(10+2*b))
    (2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b)) hf).
  change (segRLs tm
    (hf^^(2+16*q4(8+2*b))++
      (hf^^(2*(2+8*q16(5+a))*4^(10+2*b))++
       hf^^(2*2892*4^(20+2*a+2*b)+q4(21+2*a+2*b))))
    ([]++([]++[])) (third_source a b) (third_end a b)).
  eapply segRLs_trans; [apply third_column; exact H|].
  eapply segRLs_trans; [apply third_m|apply third_finish].
Qed.

(* Pure fixed-word recut needed after the root-owned complete 00 return.
   Appending any older side preserves it. *)
Lemma third_recut k :
  aw++tw^^(1+k)++[1;0;1]++bw++rw++lw++bw =
  lw++tw^^k++zw++kw++tw++[0;0]++[1;0;1].
Proof.
  change (lw++((bw++tw^^k)++[1;0;1]++bw++rw++lw++bw) =
    lw++tw^^k++zw++kw++tw++[0;0]++[1;0;1]).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Definition third_after_zero a b :=
  tw++lw^^(9+2*e a b)++kw++tw++aw++
    tw^^(25+2*a+2*b)++[1;0;1]++bw++rw++third_u2.

Lemma third_recut_family a b :
  third_after_zero a b = family_word a b ++ [1;0;1].
Proof.
  unfold third_after_zero, third_u2, family_word.
  replace (25+2*a+2*b) with (1+(24+2*a+2*b)) by (lia).
  rewrite third_recut. repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma third_reset a b u :
  P (9+2*e a b) (third_end a b *> u) -->+
  I a b ([1;0;1] *> u).
Proof.
  unfold I. rewrite <- Str_app_assoc, <- third_recut_family.
  unfold third_end, third_after_zero, third_u2.
  replace (26+2*a+2*b) with (1+(25+2*a+2*b)) by (lia).
  repeat rewrite Str_app_assoc. apply zero_return.
Qed.

Lemma third_run a b u : third_f (7+2*a)=8+2*b ->
  P 0 (third_source a b *> u) -->+ I a b ([1;0;1] *> u).
Proof.
  intro H.
  apply (@evstep_progress_trans tm
    (P 0 (third_source a b *> u))
    (P (9+2*e a b) (third_end a b *> u))
    (I a b ([1;0;1] *> u))).
  - exact (P_service_zero (9+2*e a b)
      (third_source a b) (third_end a b) u (third_services a b H)).
  - exact (third_reset a b u).
Qed.

(* The abstract certificate keeps every large coefficient in binary Z.
   The semantic lemma below never expands q4 at a concrete large index. *)
Lemma third_index_algebra (q0 q2 q9 x : nat) :
  1+3*q0=x -> 1+3*q2=16*x -> 1+3*q9=(4*256*256)*x ->
  8*q9+(1+(4*((16*256*256)*x)+
    (29+96*q0+2*(4*(4*1911+3)+1)*(16*x)))) =
  8+2*(501+183*1000+(522+550*1000)*q2).
Proof.
  intros H0 H2 H9. zify.
  ring_simplify in H0. ring_simplify in H2. ring_simplify in H9.
  ring_simplify.
  match goal with |- ?l = ?r => assert (Hlin : (3*(l-r)=0)%Z) end.
  - transitivity
      (8*((3*Z.of_nat q9+1)-262144*Z.of_nat x)
       +96*((3*Z.of_nat q0+1)-Z.of_nat x)
       -1101044*((3*Z.of_nat q2+1)-16*Z.of_nat x))%Z.
    + ring.
    + rewrite H9,H0,H2. ring.
  - apply Z.mul_eq_0 in Hlin. destruct Hlin as [Hbad|Hlin]; [discriminate|].
    exact (proj1 (Z.sub_move_0_r _ _) Hlin).
Qed.

Lemma third_index n :
  third_f n = 8+2*(501+183*1000+(522+550*1000)*q4(n+2)).
Proof.
  assert (P2 : 4^(n+2)=16*4^n).
  { replace (n+2) with (2+n) by (lia).
    rewrite (Nat.pow_add_r 4 2 n). reflexivity. }
  assert (P2' : 4^(2+n)=16*4^n).
  { rewrite (Nat.pow_add_r 4 2 n). reflexivity. }
  assert (P9 : 4^(n+9)=(4*256*256)*4^n).
  { replace (n+9) with (1+(4+(4+n))) by (lia).
    rewrite (Nat.pow_add_r 4 1 (4+(4+n))),
      (Nat.pow_add_r 4 4 (4+n)), (Nat.pow_add_r 4 4 n).
    change (4*(256*(256*4^n))=(4*256*256)*4^n).
    repeat rewrite Nat.mul_assoc. reflexivity. }
  assert (P10 : 4^(n+10)=(16*256*256)*4^n).
  { replace (n+10) with (2+(4+(4+n))) by (lia).
    rewrite (Nat.pow_add_r 4 2 (4+(4+n))),
      (Nat.pow_add_r 4 4 (4+n)), (Nat.pow_add_r 4 4 n).
    change (16*(256*(256*4^n))=(16*256*256)*4^n).
    repeat rewrite Nat.mul_assoc. reflexivity. }
  pose proof (q4_pow n) as H0.
  pose proof (q4_pow (n+2)) as H2.
  pose proof (q4_pow (n+9)) as H9.
  rewrite P2 in H2. rewrite P9 in H9.
  unfold third_f, entry8_calls. rewrite P10, P2'.
  apply third_index_algebra; assumption.
Qed.

Definition entry_v := [0;0;1;0;0;0;1;0;1;1;0;0;1;1;0;1].

Lemma entry_recut k :
  aw++tw^^(1+k)++[1;0;1]++entry_b =
  lw++tw^^k++third_u0++entry_v.
Proof.
  change (lw++((bw++tw^^k)++[1;0;1]++entry_b) =
    lw++tw^^k++third_u0++entry_v).
  rewrite bw_comm_T. repeat rewrite <- app_assoc. reflexivity.
Qed.

Transparent entry_b0.

Lemma entry_third_guard : third_f (7+2*entry_a0)=8+2*entry_b0.
Proof.
  rewrite third_index.
  replace (7+2*entry_a0+2) with entry_m by (rewrite entry_m_odd; lia).
  unfold entry_b0. reflexivity.
Qed.

Opaque entry_b0.

Lemma entry_third : c0 -->*
  P 0 (third_source entry_a0 entry_b0 *> entry_v *> 0inf).
Proof.
  follow entry_after_zero.
  replace (entry_m+8) with (1+(entry_m+7)) by lia.
  repeat rewrite <- Str_app_assoc.
  repeat rewrite <- app_assoc.
  rewrite entry_recut, entry_B_index.
  replace (entry_m+7) with (16+2*entry_a0) by (rewrite entry_m_odd; lia).
  unfold third_source. repeat rewrite <- app_assoc. finish.
Qed.

Lemma init_family : c0 -->*
  I entry_a0 entry_b0 ([1;0;1] *> entry_v *> 0inf).
Proof.
  follow entry_third.
  apply progress_evstep, third_run, entry_third_guard.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init_family|apply family_nonhalt]. Qed.
End TM13.
