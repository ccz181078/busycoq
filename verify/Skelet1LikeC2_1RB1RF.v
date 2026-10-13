(* 1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD--- never halts.
   Skelet 1-like Class 2.  The table is that of 1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---
   with its states renamed by sigma = (A C)(B D) (no mirror).  It starts in A = sigma(C), so it
   runs the parent machine from 0^inf C> 0^inf: a different orbit of the same macro map.  This
   file is the parent's kill file, verify/Skelet1LikeC2_1RB0LD.v, with the state names in the
   sweep lemmas and in K swapped by sigma, and a new start (init0, base, init).
   A binary down-counter on a list of pairs (10)^p (01)^q s(d) (s(1) = 0001, s(0) = 0010) behind
   a left marker (10)^h 11001, with overflow re-pairing; the head sits in state C at the left end.
   Proof structure: every macro rule (Dec, DecMerge, DecMergeTail, End, EndLast, X2, Ov, X1) is
   a lemma [K h P T -->+ K h' P' T'].  A per-step invariant [J] (a ghost phase of the two-cycle
   period plus, for every pair, bounds on the projected values p + Rt and q - Rt, where Rt is the
   number of touches the pair still gets before the next re-pairing) is preserved by every
   rule ([Jstep]) and holds at the E-start reached after 79,114 steps ([init], [J_base]);
   [progress_nonhalt_cond] concludes.
   Informal proof: the accompanying write-up (proof.md), a delta proof from the parent's
   write-up (the write-up for 1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---:
   INV+(e), section 3.8; the Rocq invariant is described in its
   section 4, "How the .v file is organized").
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62.
Require Import Arith Lia List.
Require Import String.
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Lemma ev_eq {c1 c2 c2'} : c1 -->* c2 -> c2 = c2' -> c1 -->* c2'.
Proof. intros H E. subst. exact H. Qed.

Lemma prog_eq {c1 c2 c2'} : c1 -->+ c2 -> c2 = c2' -> c1 -->+ c2'.
Proof. intros H E. subst. exact H. Qed.

(** * Low-level sweeps (all by [es]).
    Paper words: pair [p,q,d] = (10)^p (01)^q s(d), s(1) = 0001, s(0) = 0010.
    During the long rightward sweep a passed pair [p,q+1,0] is left behind as
    region (paper) 0 (01)^p 110 (01)^q 11, the 0 being the boundary cell. *)

Lemma Start h r : 0inf <{{C}} [1;0]^^h *> [1;1;0;0;1] *> r -->+
  0inf <* <[1;0]^^(4+h) <* <[1;1;1] <* [0] {{D}}> r.
Proof. es. Qed.

Lemma PassR l p q r : l <* [0] {{D}}> [1;0]^^p *> [0;1]^^(S q) *> [0;0;1;0] *> r -->*
  l <* [0] <* <[0;1]^^p <* <[1;1;0] <* <[0;1]^^q <* <[1;1] <* [0] {{D}}> r.
Proof. es. Qed.

Lemma Borrow l p q r : l {{D}}> [1;0]^^p *> [0;1]^^(S (S q)) *> [0;0;0;1] *> r -->*
  l <{{B}} [1;0]^^(S p) *> [0;1]^^(S q) *> [0;0;1;0] *> r.
Proof. es. Qed.

Lemma PassL l p q r : l <* [0] <* <[0;1]^^p <* <[1;1;0] <* <[0;1]^^(S q) <* <[1;1] <* [0] <{{B}} r -->*
  l <* [0] <{{B}} [1;0]^^(S p) *> [0;1]^^(S q) *> [0;0;0;1] *> r.
Proof. es. Qed.

Lemma EndPh h r : 0inf <* <[1;0]^^(4+h) <* <[1;1;1] <* [0] <{{B}} r -->*
  0inf <{{C}} [1;0]^^(4+h) *> [1;1;0;0;1] *> r.
Proof. es. Qed.

Lemma EndT l p q : l <* <[0;1]^^p <* <[1;1;0] <* <[0;1]^^(S q) <* <[1;1] <* [0] {{D}}> 0inf -->*
  l <{{B}} [1;0]^^(S p) *> [0;1]^^(S q) *> [0;0;1;0] *> [1;0;1] *> 0inf.
Proof. es. Qed.

Lemma EndLastT l p : l <* <[0;1]^^p <* <[1;1;0] <* <[1;1] <* [0] {{D}}> 0inf -->*
  l <{{B}} [1;0]^^(p+4) *> [1] *> 0inf.
Proof. es. Qed.

Lemma MergeB l p p' r : l {{D}}> [1;0]^^p *> [0;1] *> [0;0;0;1] *> [1;0]^^p' *> r -->*
  l <{{B}} [1;0]^^(p+p'+3) *> r.
Proof. es. Qed.

Lemma MergeE l p : l {{D}}> [1;0]^^p *> [0;1] *> [0;0;0;1] *> 0inf -->*
  l <{{B}} [1;0]^^(p+2) *> [1] *> 0inf.
Proof. es. Qed.

Lemma OvT l t : l <* [0] {{D}}> [1;0]^^t *> [1] *> 0inf -->*
  l <{{B}} [0;1]^^(S t) *> [0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma OvL l p q r : l <* [0] <* <[0;1]^^(S p) <* <[1;1;0] <* <[0;1]^^q <* <[1;1] <{{B}} r -->*
  l <{{B}} [0;1]^^(S p) *> [0;0;0;1] *> [1;0]^^(S q) *> r.
Proof. es. Qed.

Lemma OvEnd h p r : 0inf <* <[1;0]^^(4+h) <* <[1;1;1] <{{B}} [0;1]^^(S (S p)) *> [0;0;0;1] *> r -->*
  0inf <{{C}} [1;0]^^2 *> [1;1;0;0;1] *> [1;0]^^(h+5) *> [0;1]^^(S p) *> [0;0;1;0] *> r.
Proof. es. Qed.

Lemma X1Sw l p r : l <* [0] <* <[0;1]^^(S p) <* <[1;1;0] <* <[1;1] <* [0] <{{B}} r -->*
  l <{{B}} [0;1]^^(S p) *> [0;0;1;0;1;0;1] *> r.
Proof. es. Qed.

Lemma X2T l p q k : l <* <[0;1]^^p <* <[1;1;0] <* <[0;1]^^(S q) <* <[1;1] <* [0] {{D}}> [1;0;1;1;0;1] *> [0;1]^^(S k) *> 0inf -->*
  l <{{B}} [1;0]^^(S p) *> [0;1]^^(S q) *> [0;0;1;0] *> [1;0]^^3 *> [0;1]^^(S k) *> [0;0;0;1] *> 0inf.
Proof. es. Qed.

(** * The family K (proof.md section 1) *)

Definition sd (d : bool) : list Sym := if d then [0;0;0;1] else [0;0;1;0].

Fixpoint RP (P : list (nat*nat*bool)) (r : side) : side :=
  match P with
  | [] => r
  | (p,q,d) :: P' => [1;0]^^p *> [0;1]^^q *> sd d *> RP P' r
  end.

Inductive Tl := TN | TA (t : nat) | TB (k : nat).

Definition RT (T : Tl) : side :=
  match T with
  | TN => 0inf
  | TA t => [1;0]^^t *> [1] *> 0inf
  | TB k => [1;0;1;1;0;1] *> [0;1]^^k *> 0inf
  end.

Definition K (h : nat) (P : list (nat*nat*bool)) (T : Tl) : Q * tape :=
  0inf <{{C}} [1;0]^^h *> [1;1;0;0;1] *> RP P (RT T).

Definition pre (h : nat) : side := 0inf <* <[1;0]^^(4+h) <* <[1;1;1].

(** region left behind by the rightward sweep over pair (p,q,_) *)
Definition reg (p q : nat) (l : side) : side :=
  l <* [0] <* <[0;1]^^p <* <[1;1;0] <* <[0;1]^^(pred q) <* <[1;1].

Fixpoint LP (Z : list (nat*nat*bool)) (l : side) : side :=
  match Z with
  | [] => l
  | (p,q,d) :: Z' => LP Z' (reg p q l)
  end.

(** what the overflow sweep leaves for pair (p,q,_) *)
Fixpoint OvR (Z : list (nat*nat*bool)) (r : side) : side :=
  match Z with
  | [] => r
  | (p,q,d) :: Z' => [0;1]^^p *> [0;0;0;1] *> [1;0]^^q *> OvR Z' r
  end.

Definition touch (x : nat*nat*bool) : nat*nat*bool :=
  let '(p,q,d) := x in (S p, pred q, negb d).

Definition okR (x : nat*nat*bool) : Prop := let '(p,q,d) := x in d = false /\ 1 <= q.
Definition okL (x : nat*nat*bool) : Prop := let '(p,q,d) := x in d = false /\ 2 <= q.
Definition okO (x : nat*nat*bool) : Prop := let '(p,q,d) := x in 1 <= p /\ 1 <= q.

Lemma RP_app Z W r : RP (Z ++ W) r = RP Z (RP W r).
Proof.
  induction Z as [|[[p q] d] Z IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma LP_app Z W l : LP (Z ++ W) l = LP W (LP Z l).
Proof.
  revert l. induction Z as [|[[p q] d] Z IH]; intros l; cbn; [reflexivity|]. apply IH.
Qed.

Lemma PassesR Z : Forall okR Z -> forall l r,
  l <* [0] {{D}}> RP Z r -->* LP Z l <* [0] {{D}}> r.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros HZ l r; cbn [RP LP]; [finish|].
  inversion HZ as [|? ? Hx HZ']; subst; hnf in Hx; destruct Hx as [Hd Hq]; subst d.
  destruct q as [|q]; [lia|].
  eapply evstep_trans. { apply PassR. }
  apply (IH HZ' (reg p (S q) l) r).
Qed.

Lemma PassesL Z : Forall okL Z -> forall l r,
  LP Z l <* [0] <{{B}} r -->* l <* [0] <{{B}} RP (map touch Z) r.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros HZ l r; cbn [RP LP map]; [finish|].
  inversion HZ as [|? ? Hx HZ']; subst; hnf in Hx; destruct Hx as [Hd Hq]; subst d.
  destruct q as [|[|q]]; [lia|lia|].
  eapply evstep_trans. { apply (IH HZ' (reg p (S (S q)) l)). }
  unfold reg. cbn [pred]. apply PassL.
Qed.

Lemma OvPasses Z : Forall okO Z -> forall l r,
  LP Z l <{{B}} r -->* l <{{B}} OvR Z r.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros HZ l r; cbn [OvR LP]; [finish|].
  inversion HZ as [|? ? Hx HZ']; subst; hnf in Hx; destruct Hx as [Hp Hq].
  destruct p as [|p]; [lia|]. destruct q as [|q]; [lia|].
  eapply evstep_trans. { apply (IH HZ' (reg (S p) (S q) l)). }
  unfold reg. cbn [pred]. apply OvL.
Qed.

Lemma okL_R Z : Forall okL Z -> Forall okR Z.
Proof.
  intros H. eapply Forall_impl; [|exact H]. intros [[p q] d] [H1 H2]. split; [exact H1 | lia].
Qed.

(** * Macro rules (proof.md section 2) *)

Lemma Dec h Z p q R T : Forall okL Z ->
  K h (Z ++ (p, S (S q), true) :: R) T -->+ K (4+h) (map touch Z ++ (S p, S q, false) :: R) T.
Proof.
  intros HZ. unfold K. rewrite !RP_app. cbn [RP sd].
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR, okL_R, HZ. }
  eapply evstep_trans. { apply Borrow. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  apply EndPh.
Qed.

Lemma DecMerge h Z p p' q' d' R T : Forall okL Z ->
  K h (Z ++ (p, 1%nat, true) :: (p', q', d') :: R) T -->+ K (4+h) (map touch Z ++ (p+p'+3, q', d') :: R) T.
Proof.
  intros HZ. unfold K. rewrite !RP_app. cbn [RP sd].
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR, okL_R, HZ. }
  eapply evstep_trans. { apply MergeB. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  apply EndPh.
Qed.

Lemma DecMergeTail h Z p t : Forall okL Z ->
  K h (Z ++ [(p, 1%nat, true)]) (TA t) -->+ K (4+h) (map touch Z) (TA (p+t+3)).
Proof.
  intros HZ. unfold K. rewrite !RP_app. cbn [RP sd RT].
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR, okL_R, HZ. }
  eapply evstep_trans. { apply MergeB. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  apply EndPh.
Qed.

Lemma DecMergeEmpty h Z p : Forall okL Z ->
  K h (Z ++ [(p, 1%nat, true)]) TN -->+ K (4+h) (map touch Z) (TA (p+2)).
Proof.
  intros HZ. unfold K. rewrite !RP_app. cbn [RP sd RT].
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR, okL_R, HZ. }
  eapply evstep_trans. { apply MergeE. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  apply EndPh.
Qed.

Lemma Forall_snoc {A} (P : A -> Prop) Z x : Forall P Z -> P x -> Forall P (Z ++ [x]).
Proof. intros H1 H2. apply Forall_app. split; auto. Qed.

Lemma EndR h Z p q : Forall okL Z ->
  K h (Z ++ [(p, S (S q), false)]) TN -->+ K (4+h) (map touch Z ++ [(S p, S q, false)]) (TA 1).
Proof.
  intros HZ. unfold K.
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR. apply Forall_snoc; [apply okL_R, HZ | cbn; split; [reflexivity | lia]]. }
  rewrite LP_app. cbn [LP RT]. unfold reg at 1. cbn [pred].
  eapply evstep_trans. { apply EndT. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  rewrite RP_app. apply EndPh.
Qed.

Lemma EndLast h Z p : Forall okL Z ->
  K h (Z ++ [(p, 1%nat, false)]) TN -->+ K (4+h) (map touch Z) (TA (p+4)).
Proof.
  intros HZ. unfold K.
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR. apply Forall_snoc; [apply okL_R, HZ | cbn; split; [reflexivity | lia]]. }
  rewrite LP_app. cbn [LP RT]. unfold reg at 1. cbn [pred].
  eapply evstep_trans. { apply EndLastT. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  apply EndPh.
Qed.

Lemma X2 h Z p q k : Forall okL Z ->
  K h (Z ++ [(p, S (S q), false)]) (TB (S k)) -->+
  K (4+h) (map touch Z ++ [(S p, S q, false); (3%nat, S k, true)]) TN.
Proof.
  intros HZ. unfold K.
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR. apply Forall_snoc; [apply okL_R, HZ | cbn; split; [reflexivity | lia]]. }
  rewrite LP_app. cbn [LP RT]. unfold reg at 1. cbn [pred].
  eapply evstep_trans. { apply X2T. }
  eapply evstep_trans. { apply (PassesL Z HZ). }
  rewrite RP_app. apply EndPh.
Qed.

Fixpoint ovp (q : nat) (Z : list (nat*nat*bool)) (t : nat) : list (nat*nat*bool) :=
  match Z with
  | [] => [(q, S t, true)]
  | (p',q',_) :: Z' => (q, p', true) :: ovp q' Z' t
  end.

Lemma ovp_eq Z : forall q t, RP (ovp q Z t) 0inf = [1;0]^^q *> OvR Z ([0;1]^^(S t) *> [0;0;0;1] *> 0inf).
Proof.
  induction Z as [|[[p q'] d] Z IH]; intros q t; cbn [ovp RP OvR sd]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma Ov h p1 q1 Z t : 1 <= q1 -> Forall okR Z -> Forall okO Z ->
  K h ((S (S p1), q1, false) :: Z) (TA t) -->+ K 2 ((h+5, S p1, false) :: ovp q1 Z t) TN.
Proof.
  intros Hq HR HO. unfold K.
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR. constructor; [cbn; split; [reflexivity|lia] | exact HR]. }
  cbn [RT LP].
  eapply evstep_trans. { apply OvT. }
  eapply evstep_trans. { apply (OvPasses Z HO). }
  destruct q1 as [|q1]; [lia|]. unfold reg. cbn [pred].
  eapply evstep_trans. { apply OvL. }
  eapply ev_eq. { apply OvEnd. }
  cbn [RP sd RT]. rewrite ovp_eq. reflexivity.
Qed.

Fixpoint ovpX (q : nat) (Z : list (nat*nat*bool)) (pa : nat) : list (nat*nat*bool) :=
  match Z with
  | [] => [(q, pa, false)]
  | (p',q',_) :: Z' => (q, p', true) :: ovpX q' Z' pa
  end.

Lemma ovpX_eq Z : forall q pa r, RP (ovpX q Z pa) r = [1;0]^^q *> OvR Z ([0;1]^^pa *> [0;0;1;0] *> r).
Proof.
  induction Z as [|[[p q'] d] Z IH]; intros q pa r; cbn [ovpX RP OvR sd]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma tailB_eq n : [0;0;1;0;1;0;1] *> [1;0]^^(S n) *> [1] *> 0inf = [0;0;1;0] *> RT (TB n).
Proof.
  cbn [RT]. cbn [lpow app]. cbn [Str_app]. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
  f_equal. f_equal. f_equal.
  change ([1;0]^^n *> 1 >> 0inf = 1 >> [0;1]^^n *> 0inf).
  apply lpow_rotate.
Qed.

Lemma X1 h p1 q1 Z pa pb : 1 <= q1 -> Forall okR Z -> Forall okO Z ->
  K h ((S (S p1), q1, false) :: Z ++ [(S pa, 1%nat, false); (pb, 1%nat, false)]) TN -->+
  K 2 ((h+5, S p1, false) :: ovpX q1 Z (S pa)) (TB (pb+3)).
Proof.
  intros Hq HR HO. unfold K.
  eapply progress_evstep_trans. { apply Start. }
  eapply evstep_trans. { apply PassesR. constructor; [cbn; split; [reflexivity|lia] |].
    apply Forall_app. split; [exact HR|]. repeat constructor; lia. }
  cbn [LP]. rewrite LP_app. cbn [LP RT]. unfold reg at 1. cbn [pred].
  eapply evstep_trans. { apply EndLastT. }
  unfold reg at 1. cbn [pred].
  eapply evstep_trans. { apply X1Sw. }
  eapply evstep_trans. { apply (OvPasses Z HO). }
  destruct q1 as [|q1]; [lia|]. unfold reg. cbn [pred].
  eapply evstep_trans. { apply OvL. }
  eapply ev_eq. { apply OvEnd. }
  cbn [RP sd]. rewrite ovpX_eq. replace (pb+4) with (S (pb+3)) by lia. rewrite tailB_eq. reflexivity.
Qed.

(** * Start (proof.md section 2): c0 reaches K0' = K(2; (11,13,0); -) in 1,088 steps, and the
    base E-start after overflow 6, K(2; (95,68,0),(34,33,1),(10,15,1),(1,26,1); -), in 79,114
    steps.  Both by direct execution ([esx]). *)

Lemma init0 : c0 -->* K 2 [(11%nat, 13%nat, false)] TN.
Proof. unfold K. cbn [RP RT sd]. esx. Qed.

Definition base : list (nat*nat*bool) :=
  [(95%nat, 68%nat, false); (34%nat, 33%nat, true); (10%nat, 15%nat, true); (1%nat, 26%nat, true)].

Lemma init : c0 -->* K 2 base TN.
Proof. unfold K, base. cbn [RP RT sd]. esx. Qed.


(** * The invariant (round 2).  Arithmetic layer, then the step lemma. *)

Require Import ZifyNat.
Import Coq.Init.Datatypes.

Local Open Scope nat_scope.

Notation tri := (nat * nat * bool)%type.
Definition bv (d : bool) : nat := if d then 1 else 0.

Fixpoint dv (P : list tri) : nat :=
  match P with
  | [] => 0
  | (_,_,d) :: P' => bv d + 2 * dv P'
  end.

Definition dig (x : tri) : bool := let '(_,_,d) := x in d.
Definition dig0 (x : tri) : Prop := dig x = false.



Lemma dv_lt P : dv P < 2 ^ length P.
Proof.
  induction P as [|[[p q] d] P IH]; cbn [dv length]; [cbn; lia|].
  rewrite Nat.pow_succ_r'. destruct d; cbn [bv]; lia.
Qed.

Lemma dv_zeros Z R : Forall dig0 Z -> dv (Z ++ R) = 2 ^ length Z * dv R.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros HZ; cbn [app dv length]; [cbn; lia|].
  inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d. rewrite IH by exact HZ'.
  rewrite Nat.pow_succ_r'. cbn [bv]. nia.
Qed.

Lemma dv_tz Z R : Forall dig0 Z -> dv (map touch Z ++ R) + 1 = 2 ^ length Z + 2 ^ length Z * dv R.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros HZ; cbn [map app dv length touch]; [cbn; lia|].
  inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d. cbn [negb bv].
  specialize (IH HZ'). rewrite Nat.pow_succ_r'. nia.
Qed.

(** every element, with its 1-based index and the list to its right *)
Fixpoint AllI (Pr : nat -> tri -> list tri -> Prop) (i : nat) (P : list tri) : Prop :=
  match P with
  | [] => True
  | x :: Y => Pr i x Y /\ AllI Pr (S i) Y
  end.

Lemma AllI_app Pr Z : forall i R, AllI Pr i (Z ++ R) -> AllI Pr (i + length Z) R.
Proof.
  induction Z as [|x Z IH]; intros i R H; cbn [app length] in *.
  - rewrite Nat.add_0_r. exact H.
  - destruct H as [_ H]. replace (i + S (length Z)) with (S i + length Z) by lia. apply IH, H.
Qed.

Lemma AllI_mono (Pr Pr' : nat -> tri -> list tri -> Prop) P : forall i,
  (forall j x Y, i <= j -> Pr j x Y -> Pr' j x Y) -> AllI Pr i P -> AllI Pr' i P.
Proof.
  induction P as [|x P IH]; intros i Hm H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [apply Hm; [lia | exact H1]|].
  apply IH; [|exact H2]. intros j y Y Hj. apply Hm. lia.
Qed.

Lemma AllI_shift (Pr Pr' : nat -> tri -> list tri -> Prop) P : forall i,
  (forall j x Y, i <= j -> Pr (S j) x Y -> Pr' j x Y) -> AllI Pr (S i) P -> AllI Pr' i P.
Proof.
  induction P as [|x P IH]; intros i Hm H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [apply Hm; [lia | exact H1]|].
  apply IH; [|exact H2]. intros j y Y Hj. apply Hm. lia.
Qed.

(** the touched prefix Z (all digits 0) of a rule; R becomes R' *)
Lemma AllI_touchZ (Pr Pr' : nat -> tri -> list tri -> Prop) R R' : forall Z i,
  Forall dig0 Z ->
  (forall j p q Zr, Forall dig0 Zr -> j + S (length Zr) = i + length Z ->
     Pr j (p,q,false) (Zr ++ R) -> Pr' j (S p, pred q, true) (map touch Zr ++ R')) ->
  AllI Pr i (Z ++ R) -> AllI Pr' (i + length Z) R' -> AllI Pr' i (map touch Z ++ R').
Proof.
  induction Z as [|[[p q] d] Z IH]; intros i HZ Hob HA HR; cbn [app map length] in *.
  - rewrite Nat.add_0_r in HR. exact HR.
  - inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d. destruct HA as [H1 H2].
    cbn [touch negb]. split.
    + apply Hob; [exact HZ' | lia | exact H1].
    + apply IH; [exact HZ' | | exact H2 | ].
      * intros j p' q' Zr HZr Hj. apply Hob; [exact HZr | lia].
      * replace (S i + length Z) with (i + S (length Z)) by lia. exact HR.
Qed.

(** * The per-pair clause.  n = number of pairs to the right, w = 2^n, tv = value of the digits
    from this pair to the top (this pair least significant, so tv = d mod 2).  Rt = tv + (phase
    term) is the number of touches the pair still gets before the next re-pairing if no merge
    happens; p + Rt and q - Rt are invariant under touches. *)

Inductive phase := E1 | E2 | E1t | E2t | T0 | L1 | L2 | LX.

(** clauses that depend on n (not on the index) *)
Definition PN (ph : phase) (c4 : bool) (p q n tv : nat) : Prop :=
  match ph with
  | E1 => match n with
          | 0 => q >= tv + 2 ^ n + 1 /\ p + tv + 2 ^ n >= 3
          | S _ => q >= tv + 3 * 2 ^ n + 1 /\ (p + tv) mod 2 = 1 /\ p + tv + 2 ^ n >= 3 * 2 ^ n
          end
  | E2 => match n with
          | 0 => q >= tv + 1 /\ p + tv >= 3
          | S _ => q >= tv + 2 * 2 ^ n + 1 /\ (p + tv) mod 2 = 1 /\ p + tv >= 3 * 2 ^ n
          end
  | E1t => match n with
          | 0 => q >= tv + 2 ^ n + 1 /\ p + tv + 2 ^ n = 5
          | S _ => q >= tv + 2 * 2 ^ n + 1 /\ (p + tv) mod 2 = 1 /\ p + tv + 2 ^ n >= 3 * 2 ^ n
          end
  | E2t => match n with
          | 0 => q >= tv + 1 /\ p + tv = 5
          | S _ => q >= tv + 2 ^ n + 1 /\ (p + tv) mod 2 = 1 /\ p + tv >= 3 * 2 ^ n
          end
  | T0 => q >= tv + 7 * 2 ^ n + 1 /\ p + tv + 5 * 2 ^ n >= 6 * 2 ^ n /\
          match n with
          | 0 => tv = 0 /\ p mod 2 = 0
          | S _ => (p + tv) mod 2 = 1
          end
  | L1 => q + 2 ^ n >= tv + 2 /\
          match n with
          | 0 => q = tv + 2 ^ n
          | 1 => p + tv + 2 ^ n >= (if c4 then 4 else 5) * 2 ^ n /\
                 (q >= tv + 2 ^ n + 1 \/ (q + tv) mod 2 = 0) /\ (if c4 then q = tv + 2 ^ n else True)
          | S (S _) => p + tv + 2 ^ n >= (if c4 then 4 else 5) * 2 ^ n /\ (q + tv) mod 2 = 0
          end
  | LX => match n with
          | 0 => q = tv + 1
          | 1 => p + tv >= 4 * 2 ^ n /\ q = tv + 1
          | S (S _) => p + tv >= 4 * 2 ^ n /\ (q + tv) mod 2 = 0
          end
  | L2 => p + tv >= (if c4 then 4 else 5) * (2 * 2 ^ n) /\
          match n with
          | 0 => (q >= tv + 1 \/ (q + tv) mod 2 = 0) /\ (if c4 then q = tv else True)
          | S _ => (q + tv) mod 2 = 0
          end
  end.

(** clauses for pairs 1 and 2 (h only matters for pair 1) *)
Definition PI (ph : phase) (h i p q n tv : nat) : Prop :=
  match i with
  | 1 => h mod 2 = 0 /\
         match ph with
         | E1 | E1t => 2 <= n /\ p + tv + 2 ^ n + 3 >= 11 * 2 ^ n /\ h + 4 * (tv + 2 ^ n) + 6 >= 12 * 2 ^ n
         | E2 | E2t => 2 <= n /\ p + tv + 3 >= 11 * 2 ^ n /\ h + 4 * tv + 6 >= 12 * 2 ^ n
         | T0 => 2 <= n /\ p + tv + 5 * 2 ^ n + 3 >= 22 * 2 ^ n /\ h + 4 * (tv + 5 * 2 ^ n) + 6 >= 24 * 2 ^ n
         | L1 => 2 <= n /\ q >= tv + 3 * 2 ^ n /\ h + 4 * (tv + 2 ^ n) + 6 >= 8 * 2 ^ n
         | LX => 3 <= n /\ q >= tv + 2 * 2 ^ n /\ h + 4 * tv + 6 >= 8 * 2 ^ n
         | L2 => 1 <= n /\ q >= tv + 4 * 2 ^ n /\ h + 4 * tv + 6 >= 16 * 2 ^ n
         end
  | 2 => match ph with
         | E1 | E1t => p + tv + 2 ^ n + 1 >= 7 * 2 ^ n
         | E2 | E2t => p + tv + 1 >= 7 * 2 ^ n
         | T0 => p + tv + 5 * 2 ^ n + 1 >= 14 * 2 ^ n
         | L1 => q >= tv + 2 ^ n + 1
         | LX | L2 => q >= tv + 1
         end
  | _ => True
  end.

Definition PC (ph : phase) (c4 : bool) (h i p q n tv : nat) : Prop :=
  1 <= p /\ 1 <= q /\ PN ph c4 p q n tv /\ PI ph h i p q n tv.

Definition Lift (Pr : nat -> nat -> nat -> nat -> nat -> Prop) (i : nat) (x : tri) (Y : list tri) : Prop :=
  let '(p,q,d) := x in Pr i p q (length Y) (dv (x :: Y)).

Definition PCx (ph : phase) (c4 : bool) (h : nat) := Lift (PC ph c4 h).

Ltac dP := unfold PC, PN, PI in *.
Ltac unfL := unfold PCx, Lift in *; cbv beta iota in *.
Ltac unfLg := unfold PCx, Lift; cbv beta iota.
Ltac unfLh H := unfold PCx, Lift in H; cbv beta iota in H.
Ltac splitH := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac cr := cbn - [Nat.modulo] in *; splitH; repeat split; try lia.

Lemma pow_pos n : 1 <= 2 ^ n.
Proof. pose proof (Nat.pow_nonzero 2 n). lia. Qed.

(** a touch (every touched pair of a Dec step) *)
Lemma ob_touch ph c4 h i p q n tv : 1 <= tv -> 2 <= q ->
  PC ph c4 h i p q n tv -> PC ph c4 (4 + h) i (S p) (pred q) n (tv - 1).
Proof.
  intros Ht Hq [H1 [H2 [HN HI]]]. pose proof (pow_pos n). split; [lia|]. split; [lia|]. split.
  - clear HI. unfold PN in *. destruct ph; try destruct c4; destruct n as [|[|n]]; cr.
  - clear HN. unfold PI in *. destruct i as [|[|[|i]]]; try exact I; destruct ph; cr.
Qed.

Lemma pow_S n : 2 ^ S n = 2 * 2 ^ n.
Proof. reflexivity. Qed.

Ltac prePC := match goal with H : PC _ _ _ _ _ _ _ _ |- _ => destruct H as (Hp & Hq0 & HN & HI) end;
  split; [lia|]; split; [lia|]; split.

(** a pair left of a DecMerge (L phases): n+1 -> n pairs to the right,
    tv = u + 2U -> u - 1 + U with u = 2^a (a >= 1), U = u * H *)
Lemma ob_merge ph c4 h i p q n u U :
  (ph = L1 \/ ph = L2 \/ ph = LX) ->
  1 <= n -> 2 <= u -> u mod 2 = 0 -> U mod 2 = 0 -> U + u <= 2 * 2 ^ n ->
  (ph = L1 -> U + u <= 2 ^ n) -> (ph = LX -> 2 <= n) -> (ph = L1 -> c4 = true -> 2 <= n) ->
  (i = 1 -> 2 <= n) -> (ph = LX -> i = 1 -> 3 <= n) -> 2 <= q ->
  PC ph c4 h i p q (S n) (u + 2 * U) -> PC ph c4 (4 + h) i (S p) (pred q) n (u - 1 + U).
Proof.
  intros Hph Hn Hu Hu2 HU2 HUu HL1 HLX Hc4 Hi1 HiX Hq H. pose proof (pow_pos n).
  prePC.
  - clear HI. unfold PN in *. repeat rewrite pow_S in *.
    destruct Hph as [-> | [-> | ->]]; try destruct c4; destruct n as [|[|n]]; cr.
  - clear HN. unfold PI in *. repeat rewrite pow_S in *.
    destruct i as [|[|[|i]]]; try exact I; destruct Hph as [-> | [-> | ->]]; cr.
Qed.

(** a pair left of a DecMergeTail (L2): tv = 2^(n+1) -> 2^(n+1) - 1, and c4 is cleared *)
Lemma ob_mt c4 h i p q n : 2 <= q -> (i = 1 -> 1 <= n) ->
  PC L2 c4 h i p q (S n) (2 * 2 ^ n) -> PC L2 false (4 + h) i (S p) (pred q) n (2 * 2 ^ n - 1).
Proof.
  intros Hq Hi1 H. pose proof (pow_pos n). prePC.
  - clear HI. unfold PN in *. repeat rewrite pow_S in *. destruct c4; destruct n as [|n]; cr.
  - clear HN. unfold PI in *. repeat rewrite pow_S in *. destruct i as [|[|[|i]]]; try exact I; cr.
Qed.

(** the fused pair inherits the right pair's suffix *)
Lemma ob_fuse ph c4 h h' k p p' q' n tv : (ph = L1 \/ ph = L2 \/ ph = LX) -> 3 <= k ->
  PC ph c4 h (S k) p' q' n tv -> PC ph c4 h' k (p + p' + 3) q' n tv.
Proof.
  intros Hph Hk H. pose proof (pow_pos n). prePC.
  - clear HI. unfold PN in *. destruct Hph as [-> | [-> | ->]]; try destruct c4; destruct n as [|[|n]]; cr.
  - unfold PI. destruct k as [|[|[|k]]]; try lia; exact I.
Qed.

(** pairs far from the head: the index and h do not matter *)
Lemma ob_far ph c4 h h' i j p q n tv : 3 <= i -> 3 <= j ->
  PC ph c4 h i p q n tv -> PC ph c4 h' j p q n tv.
Proof.
  intros Hi Hj [H1 [H2 [H3 _]]]. split; [lia|]. split; [lia|]. split; [exact H3|].
  unfold PI. destruct j as [|[|[|j]]]; try lia; exact I.
Qed.

(** End (E1 -> E2, E1t -> E2t) *)
Definition endtr (ph ph' : phase) : Prop := (ph = E1 /\ ph' = E2) \/ (ph = E1t /\ ph' = E2t).

Lemma ob_end ph ph' h i p q n : endtr ph ph' -> 1 <= n -> 2 <= q ->
  PC ph false h i p q n 0 -> PC ph' false (4 + h) i (S p) (pred q) n (2 ^ n - 1).
Proof.
  intros Hph Hn Hq H. pose proof (pow_pos n). prePC.
  - clear HI. unfold PN in *. destruct Hph as [[-> ->]|[-> ->]]; destruct n as [|n]; cr.
  - clear HN. unfold PI in *. destruct i as [|[|[|i]]]; try exact I; destruct Hph as [[-> ->]|[-> ->]]; cr.
Qed.

Lemma ob_end_top ph ph' h i p q : endtr ph ph' -> 3 <= i ->
  PC ph false h i p (S (S q)) 0 0 -> PC ph' false (4 + h) i (S p) (S q) 0 0.
Proof.
  intros Hph Hi H. prePC.
  - clear HI. unfold PN in *. destruct Hph as [[-> ->]|[-> ->]]; cr.
  - unfold PI. destruct i as [|[|[|i]]]; try lia; exact I.
Qed.

(** EndLast (L1 -> L2) *)
Lemma ob_endlast c4 h i p q n : 2 <= q ->
  PC L1 c4 h i p q (S n) 0 -> PC L2 c4 (4 + h) i (S p) (pred q) n (2 * 2 ^ n - 1).
Proof.
  intros Hq H. pose proof (pow_pos n). prePC.
  - clear HI. unfold PN in *. repeat rewrite pow_S in *. destruct c4; destruct n as [|n]; cr.
  - clear HN. unfold PI in *. repeat rewrite pow_S in *. destruct i as [|[|[|i]]]; try exact I; cr.
Qed.

(** X2 (T0 -> E1t) *)
Lemma ob_x2 h i p q n : 1 <= n -> 2 <= q ->
  PC T0 false h i p q n 0 -> PC E1t false (4 + h) i (S p) (pred q) (S n) (3 * 2 ^ n - 1).
Proof.
  intros Hn Hq H. pose proof (pow_pos n). prePC.
  - clear HI. unfold PN in *. repeat rewrite pow_S in *. destruct n as [|n]; cr.
  - clear HN. unfold PI in *. repeat rewrite pow_S in *. destruct i as [|[|[|i]]]; try exact I; cr.
Qed.

Lemma ob_x2_top h i p q : 3 <= i ->
  PC T0 false h i p (S (S q)) 0 0 -> PC E1t false (4 + h) i (S p) (S q) 1 2.
Proof.
  intros Hi H. prePC.
  - clear HI. unfold PN in *. cr.
  - unfold PI. destruct i as [|[|[|i]]]; try lia; exact I.
Qed.

Lemma ob_x2_new h i k : 3 <= i -> 3 <= k -> PC E1t false h i 3 k 0 1.
Proof.
  intros Hi Hk. split; [lia|]. split; [lia|]. split.
  - unfold PN. cr.
  - unfold PI. destruct i as [|[|[|i]]]; try lia; exact I.
Qed.

(** Ov (E2 -> L1/LX, E2t -> L1 with c4, L2 -> E1).  Xp: condition on the old far p (= x). *)
Definition ovtr (ph ph' : phase) (c4' : bool) (Xp : nat -> Prop) : Prop :=
  (ph = E2 /\ ph' = L1 /\ c4' = false /\ Xp = (fun x => x <> 4)) \/
  (ph = E2 /\ ph' = LX /\ c4' = false /\ Xp = (fun x => x = 4)) \/
  (ph = E2t /\ ph' = L1 /\ c4' = true /\ Xp = (fun _ => True)) \/
  (ph = L2 /\ ph' = E1 /\ c4' = false /\ Xp = (fun _ => True)).

Lemma ob_ov_head ph ph' c4' Xp h p1 q1 n : ovtr ph ph' c4' Xp ->
  PC ph false h 1 (S (S p1)) q1 n 0 -> PC ph' c4' 2 1 (h + 5) (S p1) (S n) (2 * (2 * 2 ^ n) - 2).
Proof.
  intros Htr H. pose proof (pow_pos n). prePC.
  - unfold PN, PI in *. repeat rewrite pow_S in *.
    destruct Htr as [(-> & -> & -> & _)|[(-> & -> & -> & _)|[(-> & -> & -> & _)|(-> & -> & -> & _)]]];
      destruct n as [|[|n]]; cr.
  - unfold PN, PI in *. repeat rewrite pow_S in *.
    destruct Htr as [(-> & -> & -> & _)|[(-> & -> & -> & _)|[(-> & -> & -> & _)|(-> & -> & -> & _)]]];
      destruct n as [|[|n]]; cr.
Qed.

Lemma ob_ov_step ph ph' c4' Xp h i pp q p' q' m : ovtr ph ph' c4' Xp -> 1 <= i ->
  PC ph false h i pp q (S m) 0 -> PC ph false h (S i) p' q' m 0 -> (m = 0 -> Xp p') ->
  PC ph' c4' 2 (S i) q p' (S m) (2 * (2 * 2 ^ m) - 1).
Proof.
  intros Htr Hi H H' HX. pose proof (pow_pos m). destruct H as (Hp & Hq & HN & HI).
  destruct H' as (Hp' & Hq' & HN' & HI').
  split; [lia|]. split; [lia|]. split.
  - clear HI HI'. unfold PN in *. repeat rewrite pow_S in *.
    destruct Htr as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]];
      destruct m as [|[|m]]; cr.
  - unfold PI. destruct i as [|[|i]]; [lia| |exact I].
    unfold PN, PI in *. repeat rewrite pow_S in *.
    destruct Htr as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]];
      destruct m as [|[|m]]; cr.
Qed.

Lemma ob_ov_base ph ph' c4' Xp h i pp q t : ovtr ph ph' c4' Xp -> 1 <= i ->
  (ph = L2 -> 2 <= t) -> (ph <> L2 -> t = 1) ->
  PC ph false h i pp q 0 0 -> PC ph' c4' 2 (S i) q (S t) 0 1.
Proof.
  intros Htr Hi Ht1 Ht2 H. unfold PC in H. splitH. split; [lia|]. split; [lia|].
  unfold PN, PI in *.
  destruct Htr as [(-> & -> & -> & ->)|[(-> & -> & -> & ->)|[(-> & -> & -> & ->)|(-> & -> & -> & ->)]]];
    destruct i as [|[|[|i]]]; cr; try (specialize (Ht2 ltac:(discriminate)); lia);
    specialize (Ht1 eq_refl); lia.
Qed.

(** X1 (LX -> T0) *)
Lemma ob_x1_head h p1 q1 n :
  PC LX false h 1 (S (S p1)) q1 (S (S n)) 0 -> PC T0 false 2 1 (h + 5) (S p1) (S n) (2 * 2 ^ n - 2).
Proof.
  intros H. pose proof (pow_pos n). prePC; unfold PN, PI in *; repeat rewrite pow_S in *;
  destruct n as [|[|n]]; cr.
Qed.

Lemma ob_x1_step h i pp q p' q' m : 1 <= i ->
  PC LX false h i pp q (S (S (S m))) 0 -> PC LX false h (S i) p' q' (S (S m)) 0 ->
  PC T0 false 2 (S i) q p' (S m) (2 * 2 ^ m - 1).
Proof.
  intros Hi H H'. pose proof (pow_pos m). unfold PC in H, H'. splitH. split; [lia|]. split; [lia|].
  unfold PN, PI in *. repeat rewrite pow_S in *. destruct m as [|m]; destruct i as [|[|[|i]]]; cr.
Qed.

Lemma ob_x1_base h i pp q pa : 1 <= i ->
  PC LX false h i pp q 2 0 -> PC LX false h (S i) (S pa) 1 1 0 -> PC T0 false 2 (S i) q (S pa) 0 0.
Proof.
  intros Hi H H'. unfold PC in H, H'. splitH. split; [lia|]. split; [lia|].
  unfold PN, PI in *. destruct i as [|[|[|i]]]; cr.
Qed.

(** * List-level preservation, one lemma per rule *)

Lemma dv_zero Z : Forall dig0 Z -> dv Z = 0.
Proof. intros H. pose proof (dv_zeros Z [] H). rewrite app_nil_r in H0. cbn in H0. lia. Qed.

Lemma dv_tz' Z R : Forall dig0 Z -> dv (map touch Z ++ R) = 2 ^ length Z - 1 + 2 ^ length Z * dv R.
Proof. intros H. pose proof (dv_tz Z R H). lia. Qed.

Lemma ovp_len q Z t : length (ovp q Z t) = S (length Z).
Proof. revert q. induction Z as [|[[p q'] d] Z IH]; intros q; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma ovp_dv q Z t : dv (ovp q Z t) + 1 = 2 ^ S (length Z).
Proof.
  revert q. induction Z as [|[[p q'] d] Z IH]; intros q; cbn [ovp dv bv length]; [cbn; lia|].
  specialize (IH q'). rewrite (pow_S (S (length Z))). lia.
Qed.

Lemma ovpX_len q Z pa : length (ovpX q Z pa) = S (length Z).
Proof. revert q. induction Z as [|[[p q'] d] Z IH]; intros q; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma ovpX_dv q Z pa : dv (ovpX q Z pa) + 1 = 2 ^ length Z.
Proof.
  revert q. induction Z as [|[[p q'] d] Z IH]; intros q; cbn [ovpX dv bv length]; [cbn; lia|].
  specialize (IH q'). rewrite (pow_S (length Z)). lia.
Qed.

Fixpoint lastOK (Xp : nat -> Prop) (Z : list tri) : Prop :=
  match Z with
  | [] => True
  | [(p,_,_)] => Xp p
  | _ :: Z' => lastOK Xp Z'
  end.

Lemma lastOK_cons Xp p q d Z : lastOK Xp ((p,q,d) :: Z) -> (Z = [] -> Xp p) /\ lastOK Xp Z.
Proof. destruct Z as [|z Z]; cbn; [tauto|]. intros H. split; [discriminate | exact H]. Qed.

Lemma lastOK_dec Z : lastOK (fun x => x = 4) Z \/ lastOK (fun x => x <> 4) Z.
Proof.
  induction Z as [|[[p q] d] Z IH]; [left; exact I|].
  destruct Z as [|z Z]; [cbn; lia | exact IH].
Qed.

Lemma AllI_ovp ph ph' c4' Xp h t : ovtr ph ph' c4' Xp -> (ph = L2 -> 2 <= t) -> (ph <> L2 -> t = 1) ->
  forall Z i pp q, 1 <= i -> Forall dig0 Z -> lastOK Xp Z -> PC ph false h i pp q (length Z) 0 ->
  AllI (PCx ph false h) (S i) Z -> AllI (PCx ph' c4' 2) (S i) (ovp q Z t).
Proof.
  intros Htr Ht1 Ht2. induction Z as [|[[p' q'] d'] Z IH]; intros i pp q Hi HZ HX H HA.
  - cbn [ovp AllI]. split; [|exact I]. unfL. cbn [length dv bv].
    eapply ob_ov_base; eauto.
  - cbn [ovp AllI]. inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d'.
    destruct HA as [Hh HA]. apply lastOK_cons in HX. destruct HX as [HX1 HX2].
    unfL. cbn [length] in H. rewrite dv_zero in Hh by (constructor; [reflexivity | exact HZ']).
    split.
    + unfL. rewrite ovp_len.
      replace (dv ((q, p', true) :: ovp q' Z t)) with (2 * (2 * 2 ^ length Z) - 1)
        by (cbn [dv bv]; pose proof (ovp_dv q' Z t) as E; rewrite pow_S in E; lia).
      eapply ob_ov_step; eauto. intros E. apply HX1. destruct Z; [reflexivity | discriminate].
    + apply (IH (S i) p'); auto.
Qed.

Lemma AllI_ovpX h pa pb : forall Z i pp q, 1 <= i -> Forall dig0 Z ->
  PC LX false h i pp q (S (S (length Z))) 0 ->
  AllI (PCx LX false h) (S i) (Z ++ [(S pa, 1, false); (pb, 1, false)]) ->
  AllI (PCx T0 false 2) (S i) (ovpX q Z (S pa)).
Proof.
  induction Z as [|[[p' q'] d'] Z IH]; intros i pp q Hi HZ H HA.
  - cbn [ovpX AllI app] in *. split; [|exact I]. destruct HA as [Ha _].
    unfL. cbn [length dv bv] in *. eapply ob_x1_base; eauto.
  - cbn [ovpX AllI app] in *. inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d'.
    destruct HA as [Hh HA]. unfL.
    rewrite length_app in Hh. cbn [length] in Hh.
    rewrite dv_zero in Hh
      by (constructor; [reflexivity|]; apply Forall_app; split; [exact HZ'|]; repeat constructor).
    split.
    + unfL. rewrite ovpX_len.
      replace (dv ((q, p', true) :: ovpX q' Z (S pa))) with (2 * 2 ^ length Z - 1)
        by (cbn [dv bv]; pose proof (ovpX_dv q' Z (S pa)) as E; lia).
      eapply ob_x1_step; eauto. replace (length Z + 2) with (S (S (length Z))) in Hh by lia. exact Hh.
    + apply (IH (S i) p'); auto. replace (length Z + 2) with (S (S (length Z))) in Hh by lia. exact Hh.
Qed.

(** pass-through pairs (digit 0 below a digit 1) have q >= 2 *)
Lemma passq ph c4 h i p q n tv : PC ph c4 h i p q n tv -> 2 <= tv -> tv mod 2 = 0 -> 2 <= q.
Proof.
  intros (Hp & Hq & HN & _) Ht Ht2. pose proof (pow_pos n). unfold PN in HN.
  destruct ph; try destruct c4; destruct n as [|[|n]]; cr.
Qed.

Lemma Z_okL ph c4 h : forall Z i x R, Forall dig0 Z -> dig x = true ->
  AllI (PCx ph c4 h) i (Z ++ x :: R) -> Forall okL Z.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros i x R HZ Hx HA; [constructor|].
  inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d.
  cbn [app AllI] in HA. destruct HA as [Hh HA]. constructor; [|eapply IH; eauto].
  cbn. split; [reflexivity|]. unfL. eapply passq; [exact Hh| |].
  - cbn [dv bv]. rewrite dv_zeros by exact HZ'. destruct x as [[px qx] dx]. cbn in Hx. subst dx.
    cbn [dv bv]. pose proof (pow_pos (length Z)). nia.
  - cbn [dv bv]. lia.
Qed.

(** a digit-1 pair with q = 1 (a run-out): only in L phases, never pairs 1 and 2 *)
Lemma borrow1 ph c4 h k p n tv : 1 <= k -> tv mod 2 = 1 -> PC ph c4 h k p 1 n tv ->
  (ph = L1 \/ ph = L2 \/ ph = LX) /\ 3 <= k /\
  (ph = L1 -> 1 <= n /\ tv + 1 <= 2 ^ n /\ (c4 = true -> 2 <= n)) /\ (ph = LX -> 2 <= n).
Proof.
  intros Hk Ht (Hp & Hq & HN & HI). pose proof (pow_pos n).
  assert (Hph : ph = L1 \/ ph = L2 \/ ph = LX).
  { clear HI. unfold PN in HN. destruct ph; try (left; reflexivity); try (right; left; reflexivity);
      try (right; right; reflexivity); exfalso; destruct n as [|n]; cr. }
  split; [exact Hph|]. split.
  - clear HN. unfold PI in HI. destruct k as [|[|[|k]]]; try lia;
      destruct Hph as [-> | [-> | ->]]; cr.
  - clear HI. unfold PN in HN. split; intros ->; [destruct c4|]; destruct n as [|[|n]]; cr; discriminate.
Qed.

Lemma even2 x : (2 * x) mod 2 = 0.
Proof. lia. Qed.

Lemma pc_len (Pr : nat -> tri -> list tri -> Prop) i P : AllI Pr i P -> True.
Proof. auto. Qed.

Ltac dvs := cbn [dv bv length app map] in *; repeat rewrite length_app in *; repeat rewrite length_map in *;
  cbn [length] in *.

Lemma inv_Dec ph c4 h Z p q R : Forall dig0 Z ->
  AllI (PCx ph c4 h) 1 (Z ++ (p, S (S q), true) :: R) ->
  AllI (PCx ph c4 (4 + h)) 1 (map touch Z ++ (S p, S q, false) :: R).
Proof.
  intros HZ HA. pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx HR].
  apply (AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h)) ((p, S (S q), true) :: R) ((S p, S q, false) :: R)); [exact HZ | | exact HA | ].
  - intros j p0 q0 Zr HZr Hj H. unfL. dvs.
    rewrite dv_zeros in H by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in *.
    pose proof (pow_pos (length Zr)).
    replace (1 + 2 * (2 ^ length Zr - 1 + 2 ^ length Zr * (0 + 2 * dv R)))
      with (2 * (2 ^ length Zr * (1 + 2 * dv R)) - 1) by nia.
    apply (ob_touch ph c4 h j p0 q0); [nia| |exact H]. eapply passq; [exact H| nia | apply even2].
  - cbn [AllI]. split.
    + unfL. cbn [dv bv] in *.
      replace (0 + 2 * dv R) with (1 + 2 * dv R - 1) by lia.
      apply (ob_touch ph c4 h (1 + length Z) p (S (S q)) (length R) (1 + 2 * dv R)); [lia|lia|exact Hx].
    + eapply AllI_mono; [|exact HR]. intros j y Y Hj Hy. destruct y as [[py qy] dy].
      unfL. destruct Hy as (Hp & Hq & HN & HI). split; [lia|]. split; [lia|].
      split; [exact HN|]. unfold PI in *. destruct j as [|[|[|j]]]; try lia; try exact HI; exact I.
Qed.

Lemma snoc_nn (Z : list tri) y : Z ++ [y] <> [].
Proof. destruct Z; discriminate. Qed.

Definition minlen (ph : phase) : nat := match ph with LX => 3 | L2 => 1 | _ => 2 end.

Lemma head_len ph c4 h x Y : PCx ph c4 h 1 x Y -> minlen ph <= length Y.
Proof.
  destruct x as [[p q] d]. intros H. unfLh H. destruct H as (_ & _ & _ & HI). unfold PI in HI.
  destruct ph; cbn [minlen]; cr.
Qed.

Lemma AllI_len ph c4 h P : P <> [] -> AllI (PCx ph c4 h) 1 P -> S (minlen ph) <= length P.
Proof.
  destruct P as [|x Y]; [congruence|]. intros _ [H _]. apply head_len in H. cbn. lia.
Qed.

Lemma q2_V0 ph c4 h i p q n : PC ph c4 h i p q n 0 -> 1 <= n -> (ph = LX -> 2 <= n) -> 2 <= q.
Proof.
  intros (Hp & Hq & HN & _) Hn HX. pose proof (pow_pos n). unfold PN in HN.
  destruct ph; try destruct c4; destruct n as [|[|n]]; cr; specialize (HX eq_refl); lia.
Qed.

Lemma p1_V0 ph c4 h p q n : PC ph c4 h 1 p q n 0 -> (ph = E2 \/ ph = E2t \/ ph = L2 \/ ph = LX) -> 2 <= p.
Proof.
  intros (Hp & Hq & HN & HI) Hph. pose proof (pow_pos n). unfold PN, PI in *.
  destruct Hph as [-> | [-> | [-> | ->]]]; try destruct c4; destruct n as [|[|n]]; cr.
Qed.

Lemma L2_c4_V0 h i p q : PC L2 true h i p q 0 0 -> False.
Proof. intros (Hp & Hq & HN & _). unfold PN in HN. cr. Qed.

Lemma AllI_okRO ph c4 h : forall Z i, Forall dig0 Z -> AllI (PCx ph c4 h) i Z -> Forall okR Z /\ Forall okO Z.
Proof.
  induction Z as [|[[p q] d] Z IH]; intros i HZ HA; [split; constructor|].
  inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d.
  destruct HA as [Hh HA]. destruct (IH (S i) HZ' HA) as [H1 H2]. unfLh Hh. destruct Hh as (Hp & Hq & _).
  split; constructor; auto; cbn; lia.
Qed.

Lemma inv_Merge ph c4 h Z p p' q' d' R0 : Forall dig0 Z ->
  AllI (PCx ph c4 h) 1 (Z ++ (p, 1, true) :: (p', q', d') :: R0) ->
  AllI (PCx ph c4 (4 + h)) 1 (map touch Z ++ (p + p' + 3, q', d') :: R0).
Proof.
  intros HZ HA. pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx [Hy HR]].
  pose proof (dv_lt ((p', q', d') :: R0)) as Hlt. cbn [length] in Hlt.
  set (Hd := dv ((p', q', d') :: R0)) in *.
  assert (Hx' := Hx). unfLh Hx'. cbn [length] in Hx'.
  change (dv ((p, 1, true) :: (p', q', d') :: R0)) with (1 + 2 * Hd) in Hx'.
  destruct (borrow1 ph c4 h (1 + length Z) p (S (length R0)) (1 + 2 * Hd)) as (Hph & Hk & HL1 & HLX);
    [lia | lia | exact Hx' |].
  apply (AllI_touchZ (PCx ph c4 h) (PCx ph c4 (4 + h)) ((p, 1, true) :: (p', q', d') :: R0)
           ((p + p' + 3, q', d') :: R0)); [exact HZ | | exact HA | ].
  - intros j p0 q0 Zr HZr Hj H0. unfLh H0. unfLg. rewrite !length_app, !length_map in *. cbn [length] in *. cbn [dv bv] in H0 |- *.
    rewrite dv_zeros in H0 by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in H0 |- *.
    change (bv d' + 2 * dv R0) with Hd in H0 |- *.
    set (A := 2 ^ length Zr) in *. set (B := 2 ^ length R0) in *.
    assert (HA1 : 1 <= A) by apply pow_pos. assert (HB1 : 1 <= B) by apply pow_pos.
    assert (Hn : 2 ^ (length Zr + S (length R0)) = A * (2 * B)) by (rewrite Nat.pow_add_r; reflexivity).
    rewrite pow_S in Hlt. fold B in Hlt.
    replace (length Zr + S (S (length R0))) with (S (length Zr + S (length R0))) in H0 by lia.
    replace (0 + 2 * (A * (1 + 2 * Hd))) with (2 * A + 2 * (2 * A * Hd)) in H0 by ring.
    replace (1 + 2 * (A - 1 + A * Hd)) with (2 * A - 1 + 2 * A * Hd) by (clear - HA1; nia).
    assert (Hq2 : 2 <= q0).
    { eapply passq; [exact H0 | nia |]. replace (2 * A + 2 * (2 * A * Hd)) with (2 * (A + 2 * A * Hd)) by ring.
      apply even2. }
    eapply ob_merge; [exact Hph | lia | lia | | | | | | | | | exact Hq2 | exact H0].
    + apply even2.
    + replace (2 * A * Hd) with (2 * (A * Hd)) by ring. apply even2.
    + rewrite Hn. nia.
    + intros ->. destruct (HL1 eq_refl) as (_ & Hb & _). rewrite pow_S in Hb. fold B in Hb. rewrite Hn. nia.
    + intros ->. specialize (HLX eq_refl). lia.
    + intros -> Hc. destruct (HL1 eq_refl) as (_ & _ & Hc2). specialize (Hc2 Hc). lia.
    + intros ->. lia.
    + intros -> ->. specialize (HLX eq_refl). lia.
  - cbn [AllI]. split.
    + unfLh Hy. unfLg. change (dv ((p + p' + 3, q', d') :: R0)) with (dv ((p', q', d') :: R0)).
      replace (length Z + 1) with (1 + length Z) by lia.
      eapply ob_fuse; [exact Hph | lia | exact Hy].
    + eapply AllI_shift; [|exact HR]. intros j y Y Hj Hy0. destruct y as [[py qy] dy].
      unfLh Hy0. unfLg. eapply ob_far; [| | exact Hy0]; lia.
Qed.

Lemma inv_MT c4 h Z p : Forall dig0 Z -> AllI (PCx L2 c4 h) 1 (Z ++ [(p, 1, true)]) ->
  AllI (PCx L2 false (4 + h)) 1 (map touch Z) /\ 2 <= length Z.
Proof.
  intros HZ HA. pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx _].
  assert (Hx' := Hx). unfLh Hx'. cbn [length dv bv] in Hx'.
  destruct (borrow1 L2 c4 h (1 + length Z) p 0 (1 + 2 * 0)) as (_ & Hk & _); [lia | lia | exact Hx' |].
  split; [|lia]. rewrite <- (app_nil_r (map touch Z)).
  apply (AllI_touchZ (PCx L2 c4 h) (PCx L2 false (4 + h)) [(p, 1, true)] []); [exact HZ | | exact HA | exact I].
  intros j p0 q0 Zr HZr Hj H0. unfLh H0. unfLg. rewrite !length_app, !length_map in *. cbn [length] in *. cbn [dv bv] in H0 |- *.
  rewrite dv_zeros in H0 by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in H0 |- *.
  pose proof (pow_pos (length Zr)).
  replace (length Zr + 1) with (S (length Zr)) in H0 by lia. rewrite Nat.add_0_r.
  replace (0 + 2 * (2 ^ length Zr * (1 + 2 * 0))) with (2 * 2 ^ length Zr) in H0 by ring.
  replace (1 + 2 * (2 ^ length Zr - 1 + 2 ^ length Zr * 0)) with (2 * 2 ^ length Zr - 1) by lia.
  apply (ob_mt c4); [| lia | exact H0].
  eapply passq; [exact H0 | lia | apply even2].
Qed.

Lemma inv_End ph ph' h Z p q : endtr ph ph' -> Forall dig0 Z ->
  AllI (PCx ph false h) 1 (Z ++ [(p, S (S q), false)]) ->
  AllI (PCx ph' false (4 + h)) 1 (map touch Z ++ [(S p, S q, false)]).
Proof.
  intros Htr HZ HA. pose proof (AllI_len _ _ _ _ (snoc_nn Z _) HA) as Hlen.
  rewrite length_app in Hlen. cbn [length] in Hlen.
  assert (Hm : minlen ph = 2) by (destruct Htr as [[-> _]|[-> _]]; reflexivity).
  pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx _].
  apply (AllI_touchZ (PCx ph false h) (PCx ph' false (4 + h)) [(p, S (S q), false)] [(S p, S q, false)]);
    [exact HZ | | exact HA | ].
  - intros j p0 q0 Zr HZr Hj H0. unfLh H0. unfLg. rewrite !length_app, !length_map in *. cbn [length] in *. cbn [dv bv] in H0 |- *.
    rewrite dv_zeros in H0 by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in H0 |- *.
    pose proof (pow_pos (length Zr)).
    replace (0 + 2 * (2 ^ length Zr * (0 + 2 * 0))) with 0 in H0 by ring.
    replace (1 + 2 * (2 ^ length Zr - 1 + 2 ^ length Zr * (0 + 2 * 0))) with (2 ^ (length Zr + 1) - 1)
      by (rewrite Nat.add_1_r, pow_S; lia).
    apply (ob_end ph ph'); [exact Htr | lia | | exact H0].
    eapply q2_V0; [exact H0 | lia | intros ->; destruct Htr as [[? _]|[? _]]; discriminate].
  - cbn [AllI]. split; [|exact I]. unfLh Hx. unfLg. cbn [length dv bv] in *.
    apply (ob_end_top ph ph'); [exact Htr | lia | exact Hx].
Qed.

Lemma inv_X2 h Z p q k : Forall dig0 Z -> 3 <= k ->
  AllI (PCx T0 false h) 1 (Z ++ [(p, S (S q), false)]) ->
  AllI (PCx E1t false (4 + h)) 1 (map touch Z ++ [(S p, S q, false); (3, k, true)]).
Proof.
  intros HZ Hk HA. pose proof (AllI_len _ _ _ _ (snoc_nn Z _) HA) as Hlen.
  rewrite length_app in Hlen. cbn [length minlen] in Hlen.
  pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx _].
  apply (AllI_touchZ (PCx T0 false h) (PCx E1t false (4 + h)) [(p, S (S q), false)]
           [(S p, S q, false); (3, k, true)]); [exact HZ | | exact HA | ].
  - intros j p0 q0 Zr HZr Hj H0. unfLh H0. unfLg. rewrite !length_app, !length_map in *. cbn [length] in *. cbn [dv bv] in H0 |- *.
    rewrite dv_zeros in H0 by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in H0 |- *.
    pose proof (pow_pos (length Zr)).
    replace (0 + 2 * (2 ^ length Zr * (0 + 2 * 0))) with 0 in H0 by ring.
    replace (1 + 2 * (2 ^ length Zr - 1 + 2 ^ length Zr * (0 + 2 * (1 + 2 * 0))))
      with (3 * 2 ^ (length Zr + 1) - 1) by (rewrite Nat.add_1_r, pow_S; lia).
    replace (length Zr + 2) with (S (length Zr + 1)) by lia.
    apply ob_x2; [lia | | exact H0].
    eapply q2_V0; [exact H0 | lia | discriminate].
  - cbn [AllI]. split; [|split; [|exact I]].
    + unfLh Hx. unfLg. cbn [length dv bv] in *. apply ob_x2_top; [lia | exact Hx].
    + unfLg. cbn [length dv bv]. apply ob_x2_new; lia.
Qed.

Lemma inv_EndLast c4 h Z p : Forall dig0 Z -> AllI (PCx L1 c4 h) 1 (Z ++ [(p, 1, false)]) ->
  AllI (PCx L2 c4 (4 + h)) 1 (map touch Z) /\ 2 <= length Z.
Proof.
  intros HZ HA. pose proof (AllI_len _ _ _ _ (snoc_nn Z _) HA) as Hlen.
  rewrite length_app in Hlen. cbn [length minlen] in Hlen.
  split; [|lia]. rewrite <- (app_nil_r (map touch Z)).
  apply (AllI_touchZ (PCx L1 c4 h) (PCx L2 c4 (4 + h)) [(p, 1, false)] []); [exact HZ | | exact HA | exact I].
  intros j p0 q0 Zr HZr Hj H0. unfLh H0. unfLg. rewrite !length_app, !length_map in *. cbn [length] in *. cbn [dv bv] in H0 |- *.
  rewrite dv_zeros in H0 by exact HZr. rewrite dv_tz' by exact HZr. cbn [dv bv] in H0 |- *.
  pose proof (pow_pos (length Zr)).
  replace (0 + 2 * (2 ^ length Zr * (0 + 2 * 0))) with 0 in H0 by ring.
  replace (length Zr + 1) with (S (length Zr)) in H0 by lia. rewrite Nat.add_0_r.
  replace (1 + 2 * (2 ^ length Zr - 1 + 2 ^ length Zr * 0)) with (2 * 2 ^ length Zr - 1) by lia.
  apply ob_endlast; [| exact H0].
  eapply q2_V0; [exact H0 | lia | discriminate].
Qed.

Lemma inv_Ov ph ph' c4' Xp h p1 q1 Z t : ovtr ph ph' c4' Xp -> (ph = L2 -> 2 <= t) -> (ph <> L2 -> t = 1) ->
  Forall dig0 Z -> lastOK Xp Z ->
  AllI (PCx ph false h) 1 ((S (S p1), q1, false) :: Z) ->
  AllI (PCx ph' c4' 2) 1 ((h + 5, S p1, false) :: ovp q1 Z t).
Proof.
  intros Htr Ht1 Ht2 HZ HX HA. cbn [AllI] in HA |- *. destruct HA as [Hh HA].
  assert (Hh' := Hh). unfLh Hh'. rewrite dv_zero in Hh' by (constructor; [reflexivity | exact HZ]).
  split.
  - unfLg. rewrite ovp_len.
    replace (dv ((h + 5, S p1, false) :: ovp q1 Z t)) with (2 * (2 * 2 ^ length Z) - 2)
      by (cbn [dv bv]; pose proof (ovp_dv q1 Z t) as E; rewrite pow_S in E; lia).
    eapply ob_ov_head; [exact Htr | exact Hh'].
  - eapply (AllI_ovp ph ph' c4' Xp h t Htr Ht1 Ht2 Z 1 (S (S p1)) q1); auto.
Qed.

Lemma inv_X1 h p1 q1 Z pa pb : Forall dig0 Z ->
  AllI (PCx LX false h) 1 ((S (S p1), q1, false) :: Z ++ [(S pa, 1, false); (pb, 1, false)]) ->
  AllI (PCx T0 false 2) 1 ((h + 5, S p1, false) :: ovpX q1 Z (S pa)).
Proof.
  intros HZ HA. cbn [AllI] in HA |- *. destruct HA as [Hh HA].
  assert (Hh' := Hh). unfLh Hh'.
  rewrite dv_zero in Hh'
    by (constructor; [reflexivity|]; apply Forall_app; split; [exact HZ|]; repeat constructor).
  rewrite length_app in Hh'. cbn [length] in Hh'. replace (length Z + 2) with (S (S (length Z))) in Hh' by lia.
  split.
  - unfLg. rewrite ovpX_len.
    replace (dv ((h + 5, S p1, false) :: ovpX q1 Z (S pa))) with (2 * 2 ^ length Z - 2)
      by (cbn [dv bv]; pose proof (ovpX_dv q1 Z (S pa)) as E; lia).
    exact (ob_x1_head _ _ _ _ Hh').
  - eapply (AllI_ovpX h pa pb Z 1 (S (S p1)) q1); auto.
Qed.

(** * The invariant J on abstract states, and one macro step (TM part) *)

Record st := mkst { sh : nat; sP : list (nat*nat*bool); sT : Tl; sph : phase; sc4 : bool }.

Definition Cf (s : st) : Q * tape := K (sh s) (sP s) (sT s).

Definition TC (ph : phase) (c4 : bool) (T : Tl) : Prop :=
  match ph with
  | E1 | E1t | LX => T = TN /\ c4 = false
  | L1 => T = TN
  | E2 | E2t => T = TA 1 /\ c4 = false
  | T0 => (exists k, T = TB k /\ 3 <= k) /\ c4 = false
  | L2 => exists t, T = TA t /\ 2 <= t
  end.

Definition J (s : st) : Prop :=
  sP s <> [] /\ TC (sph s) (sc4 s) (sT s) /\ AllI (PCx (sph s) (sc4 s) (sh s)) 1 (sP s).

Lemma split1 (P : list tri) :
  (exists Z x R, P = Z ++ x :: R /\ Forall dig0 Z /\ dig x = true) \/ Forall dig0 P.
Proof.
  induction P as [|[[p q] d] P IH]; [right; constructor|].
  destruct d.
  - left. exists (@nil (nat*nat*bool)), (p,q,true), P. auto.
  - destruct IH as [(Z & x & R & -> & HZ & Hx) | H].
    + left. exists ((p,q,false) :: Z), x, R. split; [reflexivity|].
      split; [constructor; [reflexivity|exact HZ] | exact Hx].
    + right. constructor; [reflexivity | exact H].
Qed.

Lemma Z_okL_V0 ph c4 h y : ph <> LX -> forall Z i, Forall dig0 (Z ++ [y]) ->
  AllI (PCx ph c4 h) i (Z ++ [y]) -> Forall okL Z.
Proof.
  intros Hph. induction Z as [|[[p q] d] Z IH]; intros i HZ HA; [constructor|].
  inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d.
  cbn [app AllI] in HA. destruct HA as [Hh HA]. constructor; [|eapply IH; eauto].
  cbn. split; [reflexivity|]. unfLh Hh. rewrite dv_zero in Hh by (constructor; [reflexivity | exact HZ']).
  eapply q2_V0; [exact Hh | rewrite length_app; cbn; lia | intros E; contradiction].
Qed.

Lemma lastOK_True Z : lastOK (fun _ => True) Z.
Proof. induction Z as [|[[p q] d] Z IH]; [exact I|]. destruct Z; [exact I | exact IH]. Qed.

Lemma Forall_snoc_inv (Pr : tri -> Prop) Z y : Forall Pr (Z ++ [y]) -> Forall Pr Z /\ Pr y.
Proof. intros H. apply Forall_app in H. destruct H as [H1 H2]. inversion H2. auto. Qed.

Lemma last_pc ph c4 h Z p q d : Forall dig0 (Z ++ [(p,q,d)]) -> AllI (PCx ph c4 h) 1 (Z ++ [(p,q,d)]) ->
  d = false /\ PC ph c4 h (1 + length Z) p q 0 0.
Proof.
  intros HZ HA. apply Forall_snoc_inv in HZ. destruct HZ as [_ Hd]. unfold dig0, dig in Hd. subst d.
  split; [reflexivity|]. pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hy _].
  unfLh Hy. exact Hy.
Qed.

Lemma first_pc ph c4 h p q d Z : Forall dig0 ((p,q,d) :: Z) -> AllI (PCx ph c4 h) 1 ((p,q,d) :: Z) ->
  d = false /\ PC ph c4 h 1 p q (length Z) 0 /\ Forall dig0 Z /\ AllI (PCx ph c4 h) 2 Z.
Proof.
  intros HZ [Hh HA]. inversion HZ as [|? ? Hd HZ']; subst. unfold dig0, dig in Hd. subst d.
  split; [reflexivity|]. unfLh Hh. rewrite dv_zero in Hh by (constructor; [reflexivity | exact HZ']).
  auto.
Qed.

Ltac pnc H := let H' := fresh in destruct H as (_ & _ & H' & _); unfold PN in H'; cbn - [Nat.modulo] in H'.

Lemma Jstep : forall s, J s -> exists s', Cf s -->+ Cf s' /\ J s'.
Proof.
  intros [h P T ph c4] (HP & HT & HA). unfold Cf. cbn [sh sP sT sph sc4] in *.
  destruct (split1 P) as [(Z & [[p q] d] & R & -> & HZ & Hd) | H0].
  - (* some digit is 1: a Dec-family step *)
    cbn in Hd. subst d.
    assert (HZL : Forall okL Z) by (apply (Z_okL ph c4 h Z 1 (p, q, true) R); [exact HZ | reflexivity | exact HA]).
    pose proof (AllI_app _ _ _ _ HA) as HB. cbn [AllI] in HB. destruct HB as [Hx HR].
    assert (Hx' := Hx). unfLh Hx'.
    destruct q as [|[|q]].
    + exfalso. destruct Hx' as (_ & Hq & _). lia.
    + destruct (borrow1 ph c4 h (1 + length Z) p (length R) (dv ((p, 1, true) :: R)))
        as (Hph & Hk & HL1 & HLX); [lia | cbn [dv bv]; lia | exact Hx' |].
      destruct R as [|[[p' q'] d'] R0].
      * destruct T as [|t|k].
        -- exfalso. destruct Hph as [-> | [-> | ->]].
           ++ destruct (HL1 eq_refl) as (Hn & _). cbn in Hn. lia.
           ++ destruct HT as (t & Ht & _). discriminate.
           ++ specialize (HLX eq_refl). cbn in HLX. lia.
        -- assert (ph = L2) as ->.
           { destruct Hph as [-> | [-> | ->]]; cbn in HT; try reflexivity;
               try discriminate; destruct HT; discriminate. }
           destruct HT as (t' & Ht & Ht2). injection Ht as <-.
           destruct (inv_MT c4 h Z p HZ HA) as [HA' Hlen].
           exists (mkst (4 + h) (map touch Z) (TA (p + t + 3)) L2 false). cbn [sh sP sT sph sc4]. split.
           ++ apply DecMergeTail. exact HZL.
           ++ split; [destruct Z; [cbn in Hlen; lia | discriminate]|].
              split; [exists (p + t + 3); split; [reflexivity | lia] | exact HA'].
        -- exfalso. destruct Hph as [-> | [-> | ->]]; cbn in HT;
             repeat match goal with H : _ /\ _ |- _ => destruct H | H : exists _, _ |- _ => destruct H end;
             discriminate.
      * exists (mkst (4 + h) (map touch Z ++ (p + p' + 3, q', d') :: R0) T ph c4). cbn [sh sP sT sph sc4].
        split.
        -- apply DecMerge. exact HZL.
        -- split; [destruct Z; discriminate|]. split; [exact HT|]. eapply inv_Merge; eauto.
    + exists (mkst (4 + h) (map touch Z ++ (S p, S q, false) :: R) T ph c4). cbn [sh sP sT sph sc4]. split.
      * apply Dec. exact HZL.
      * split; [destruct Z; discriminate|]. split; [exact HT|]. apply inv_Dec; assumption.
  - (* all digits 0 *)
    destruct ph.
    + (* E1: End *)
      destruct HT as [-> ->]. destruct (exists_last HP) as (Z & [[p q] d] & ->).
      destruct (last_pc _ _ _ _ _ _ _ H0 HA) as [-> Hy].
      assert (Hq : 2 <= q) by (pnc Hy; lia). destruct q as [|[|q]]; [lia|lia|].
      assert (HZL : Forall okL Z) by (eapply Z_okL_V0; [| exact H0 | exact HA]; discriminate).
      apply Forall_snoc_inv in H0. destruct H0 as [HZ _].
      exists (mkst (4 + h) (map touch Z ++ [(S p, S q, false)]) (TA 1) E2 false). cbn [sh sP sT sph sc4].
      split; [apply EndR; exact HZL|]. split; [apply snoc_nn|]. split; [split; reflexivity|].
      eapply inv_End; [left; split; reflexivity | exact HZ | exact HA].
    + (* E2: Ov *)
      destruct HT as [-> ->]. destruct P as [|[[p1 q1] d1] Z]; [congruence|].
      destruct (first_pc _ _ _ _ _ _ _ H0 HA) as (-> & Hh & HZ & HA2).
      assert (Hp1 := p1_V0 _ _ _ _ _ _ Hh ltac:(left; reflexivity)).
      destruct p1 as [|[|p1]]; [lia|lia|].
      destruct (AllI_okRO _ _ _ Z 2 HZ HA2) as [HR HO].
      assert (Hq1 : 1 <= q1) by (destruct Hh as (_ & Hq & _); exact Hq).
      destruct (lastOK_dec Z) as [HX | HX].
      * exists (mkst 2 ((h + 5, S p1, false) :: ovp q1 Z 1) TN LX false). cbn [sh sP sT sph sc4].
        split; [apply Ov; assumption|]. split; [discriminate|]. split; [split; reflexivity|].
        eapply (inv_Ov E2 LX false (fun x => x = 4)); [right; left; auto | discriminate | auto | exact HZ | exact HX | exact HA].
      * exists (mkst 2 ((h + 5, S p1, false) :: ovp q1 Z 1) TN L1 false). cbn [sh sP sT sph sc4].
        split; [apply Ov; assumption|]. split; [discriminate|]. split; [reflexivity|].
        eapply (inv_Ov E2 L1 false (fun x => x <> 4)); [left; auto | discriminate | auto | exact HZ | exact HX | exact HA].
    + (* E1t: End *)
      destruct HT as [-> ->]. destruct (exists_last HP) as (Z & [[p q] d] & ->).
      destruct (last_pc _ _ _ _ _ _ _ H0 HA) as [-> Hy].
      assert (Hq : 2 <= q) by (pnc Hy; lia). destruct q as [|[|q]]; [lia|lia|].
      assert (HZL : Forall okL Z) by (eapply Z_okL_V0; [| exact H0 | exact HA]; discriminate).
      apply Forall_snoc_inv in H0. destruct H0 as [HZ _].
      exists (mkst (4 + h) (map touch Z ++ [(S p, S q, false)]) (TA 1) E2t false). cbn [sh sP sT sph sc4].
      split; [apply EndR; exact HZL|]. split; [apply snoc_nn|]. split; [split; reflexivity|].
      eapply inv_End; [right; split; reflexivity | exact HZ | exact HA].
    + (* E2t: Ov to an L-slot after a T2 start *)
      destruct HT as [-> ->]. destruct P as [|[[p1 q1] d1] Z]; [congruence|].
      destruct (first_pc _ _ _ _ _ _ _ H0 HA) as (-> & Hh & HZ & HA2).
      assert (Hp1 := p1_V0 _ _ _ _ _ _ Hh ltac:(right; left; reflexivity)).
      destruct p1 as [|[|p1]]; [lia|lia|].
      destruct (AllI_okRO _ _ _ Z 2 HZ HA2) as [HR HO].
      assert (Hq1 : 1 <= q1) by (destruct Hh as (_ & Hq & _); exact Hq).
      exists (mkst 2 ((h + 5, S p1, false) :: ovp q1 Z 1) TN L1 true). cbn [sh sP sT sph sc4].
      split; [apply Ov; assumption|]. split; [discriminate|]. split; [reflexivity|].
      eapply (inv_Ov E2t L1 true (fun _ => True)); [right; right; left; auto | discriminate | auto | exact HZ | apply lastOK_True | exact HA].
    + (* T0: X2 *)
      destruct HT as [(k & -> & Hk) ->]. destruct (exists_last HP) as (Z & [[p q] d] & ->).
      destruct (last_pc _ _ _ _ _ _ _ H0 HA) as [-> Hy].
      assert (Hq : 2 <= q) by (pnc Hy; lia). destruct q as [|[|q]]; [lia|lia|].
      destruct k as [|k]; [lia|].
      assert (HZL : Forall okL Z) by (eapply Z_okL_V0; [| exact H0 | exact HA]; discriminate).
      apply Forall_snoc_inv in H0. destruct H0 as [HZ _].
      exists (mkst (4 + h) (map touch Z ++ [(S p, S q, false); (3, S k, true)]) TN E1t false).
      cbn [sh sP sT sph sc4].
      split; [apply X2; exact HZL|]. split; [destruct Z; discriminate|]. split; [split; reflexivity|].
      apply inv_X2; [exact HZ | lia | exact HA].
    + (* L1: EndLast *)
      cbn in HT. subst T. destruct (exists_last HP) as (Z & [[p q] d] & ->).
      destruct (last_pc _ _ _ _ _ _ _ H0 HA) as [-> Hy].
      assert (Hq : q = 1) by (pnc Hy; lia). subst q.
      assert (HZL : Forall okL Z) by (eapply Z_okL_V0; [| exact H0 | exact HA]; discriminate).
      apply Forall_snoc_inv in H0. destruct H0 as [HZ _].
      destruct (inv_EndLast c4 h Z p HZ HA) as [HA' Hlen].
      exists (mkst (4 + h) (map touch Z) (TA (p + 4)) L2 c4). cbn [sh sP sT sph sc4].
      split; [apply EndLast; exact HZL|]. split; [destruct Z; [cbn in Hlen; lia | discriminate]|].
      split; [exists (p + 4); split; [reflexivity | lia] | exact HA'].
    + (* L2: Ov *)
      destruct HT as (t & -> & Ht).
      destruct c4.
      { exfalso. destruct (exists_last HP) as (Z & [[p q] d] & ->).
        destruct (last_pc _ _ _ _ _ _ _ H0 HA) as [-> Hy]. exact (L2_c4_V0 _ _ _ _ Hy). }
      destruct P as [|[[p1 q1] d1] Z]; [congruence|].
      destruct (first_pc _ _ _ _ _ _ _ H0 HA) as (-> & Hh & HZ & HA2).
      assert (Hp1 := p1_V0 _ _ _ _ _ _ Hh ltac:(right; right; left; reflexivity)).
      destruct p1 as [|[|p1]]; [lia|lia|].
      destruct (AllI_okRO _ _ _ Z 2 HZ HA2) as [HR HO].
      assert (Hq1 : 1 <= q1) by (destruct Hh as (_ & Hq & _); exact Hq).
      exists (mkst 2 ((h + 5, S p1, false) :: ovp q1 Z t) TN E1 false). cbn [sh sP sT sph sc4].
      split; [apply Ov; assumption|]. split; [discriminate|]. split; [split; reflexivity|].
      eapply (inv_Ov L2 E1 false (fun _ => True)); [right; right; right; auto | intros _; exact Ht | intros E; congruence | exact HZ | apply lastOK_True | exact HA].
    + (* LX: X1 *)
      destruct HT as [-> ->].
      pose proof (AllI_len _ _ _ _ HP HA) as Hlen. cbn [minlen] in Hlen.
      destruct (exists_last HP) as (P1 & [[pb qb] db] & ->).
      assert (HP1 : P1 <> []) by (destruct P1; [cbn in Hlen; lia | discriminate]).
      destruct (exists_last HP1) as (P2 & [[pa qa] da] & ->).
      destruct P2 as [|[[p1 q1] d1] Z]; [cbn in Hlen; lia|].
      rewrite <- !app_assoc in H0, HA |- *. cbn [app] in H0, HA |- *.
      destruct (first_pc _ _ _ _ _ _ _ H0 HA) as (-> & Hh & HZab & HA2).
      apply Forall_app in HZab. destruct HZab as [HZ Hab].
      inversion Hab as [|? ? Hda Hab']; subst. inversion Hab' as [|? ? Hdb _]; subst.
      unfold dig0, dig in Hda, Hdb. subst da db.
      pose proof (AllI_app _ _ _ _ HA2) as HB. cbn [AllI] in HB. destruct HB as [Ha [Hb _]].
      unfLh Ha. unfLh Hb. cbn [length dv bv] in Ha, Hb.
      assert (Hqa : qa = 1) by (pnc Ha; lia). assert (Hqb : qb = 1) by (pnc Hb; lia). subst qa qb.
      assert (Hpa : 1 <= pa) by (destruct Ha as (Hp & _); exact Hp). destruct pa as [|pa]; [lia|].
      assert (Hp1 := p1_V0 _ _ _ _ _ _ Hh ltac:(right; right; right; reflexivity)).
      destruct p1 as [|[|p1]]; [lia|lia|].
      assert (HZab' : Forall dig0 (Z ++ [(S pa, 1, false); (pb, 1, false)]))
        by (apply Forall_app; split; [exact HZ | repeat constructor]).
      destruct (AllI_okRO _ _ _ _ 2 HZab' HA2) as [HR HO].
      apply Forall_app in HR. apply Forall_app in HO. destruct HR as [HR _]. destruct HO as [HO _].
      assert (Hq1 : 1 <= q1) by (destruct Hh as (_ & Hq & _); exact Hq).
      exists (mkst 2 ((h + 5, S p1, false) :: ovpX q1 Z (S pa)) (TB (pb + 3)) T0 false).
      cbn [sh sP sT sph sc4]. split; [apply X1; assumption|].
      split; [discriminate|]. split; [split; [exists (pb + 3); split; [reflexivity | lia] | reflexivity]|].
      eapply inv_X1; [exact HZ | exact HA].
Qed.

Lemma J_base : J (mkst 2 base TN E1 false).
Proof.
  unfold J, base. cbn [sh sP sT sph sc4]. split; [discriminate|]. split; [split; reflexivity|].
  cbn [AllI]. unfold PCx, Lift, PC, PN, PI. cbn. repeat split; lia.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (c' := K 2 base TN); [exact init|].
  change (K 2 base TN) with (Cf (mkst 2 base TN E1 false)).
  apply progress_nonhalt_cond with (P := J); [exact Jstep | exact J_base].
Qed.

(*
```
1RB1RF_1LC0LE_1RD0LB_1RA0RC_1RE1LB_0RD---       (= sigma of 1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---, sigma = (A C)(B D))

[p,q,d] := (10)^p (01)^q s(d),  s(1) = 0001, s(0) = 0010                 [RP]
K(h; P; T) := 0^inf <C (10)^h 11001 [p_1,q_1,d_1] ... [p_L,q_L,d_L] T 0^inf   [K]
T in { -, (10)^t 1, (101)^2 (01)^k }                                       [TN, TA t, TB k]
k := least j with d_j = 1;  Z := pairs 1..k-1 (all d = 0, q >= 2)
touch (p,q,d) := (p+1, q-1, 1-d)

Dec            K(h; Z ++ (p,q+2,1) :: R; T)        -->+ K(h+4; touch Z ++ (p+1,q+1,0) :: R; T)
DecMerge       K(h; Z ++ (p,1,1) :: (p',q',d') :: R; T) -->+ K(h+4; touch Z ++ (p+p'+3,q',d') :: R; T)
DecMergeTail   K(h; Z ++ [(p,1,1)]; (10)^t 1)      -->+ K(h+4; touch Z; (10)^(p+t+3) 1)
DecMergeEmpty  K(h; Z ++ [(p,1,1)]; -)             -->+ K(h+4; touch Z; (10)^(p+2) 1)
End            K(h; Z ++ [(p,q+2,0)]; -)           -->+ K(h+4; touch Z ++ [(p+1,q+1,0)]; (10)^1 1)
EndLast        K(h; Z ++ [(p,1,0)]; -)             -->+ K(h+4; touch Z; (10)^(p+4) 1)
X2             K(h; Z ++ [(p,q+2,0)]; (101)^2 (01)^(k+1))
                                                   -->+ K(h+4; touch Z ++ [(p+1,q+1,0); (3,k+1,1)]; -)
Ov             K(h; (p1+2,q1,0) :: Y; (10)^t 1)    -->+ K(2; (h+5,p1+1,0) :: ovp q1 Y t; -)
               Y all d = 0, p,q >= 1, q1 >= 1;  ovp q [] t = [(q,t+1,1)],
               ovp q ((p',q',_) :: Y) t = (q,p',1) :: ovp q' Y t
X1             K(h; (p1+2,q1,0) :: Y ++ [(pa+1,1,0); (pb,1,0)]; -)
                                                   -->+ K(2; (h+5,p1+1,0) :: ovpX q1 Y (pa+1); (101)^2 (01)^(pb+3))
               ovpX q [] pa = [(q,pa,0)], ovpX q ((p',q',_) :: Y) pa = (q,p',1) :: ovpX q' Y pa
invariant J (per pair, n = pairs to the right, tv = digit value from the pair up,
  Rt = tv + phase term): see Definitions PN, PI, TC, J; preserved by every rule (Jstep).
start: c0 -->(1,088) K(2; (11,13,0); -) -->(78,026) K(2; (95,68,0),(34,33,1),(10,15,1),(1,26,1); -)
```
*)
