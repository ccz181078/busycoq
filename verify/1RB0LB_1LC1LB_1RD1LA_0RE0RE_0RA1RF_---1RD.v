(** BB(6) holdout 1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD ("fractal in bouncer"): it never halts.

    Written by Claude (Anthropic), working autonomously with the permission of the account owner.

    Outline.
    1. Token model (Part 1). At every left record the tape is 0^inf A> w 0^inf, where w is a word over the tokens
       x = 011, y = 111, D = 01. One round trip maps w to [tstep w] (a running-XOR sweep with defect and wall rules).
       [tstep_sim]: tstep w = Some w' -> C w -->+ C w'.  [init]: c0 -->* C w1.
    2. Tail system (Part 2). Segment lists W (bit lists separated by D) with one round [Gs]; T(1) = [0010].
       Parity profile Q_S(z) = sum s_i (1+z)^(|S|-1-i) over GF(2) turns segment lifetimes into polynomial identities.
       Induction over epochs 2^k (lift lemma + sparse identities for (1+z)^eps Q_{B_m}) shows T(n) is defined for all n.
    3. Doubling (Part 3). The real token word after 2i+1 rounds is Delta(T(i+9)): the bulk is the doubled head of
       T(i+9) and the suffix after the first D is T(2m). Two real rounds = one tail round. Hence tstep never fails.
*)
From BusyCoq Require Import Individual62.
Require Import Lia Bool String List Arith Setoid Morphisms Permutation.
Import ListNotations.

(** ************************** Part 1: the TM implements the token model ************************** *)
(** FIB1 = 1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD
    Part 1: the TM implements the token model.
    Tokens: x = 011, y = 111, D = 01 (tape order). At a left record the head is in state A on the first cell of the word. *)

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD"%string).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Open Scope list_scope.

(** ===== Local lemmas (left-side words are head-outward) ===== *)
Definition g (c:bool) : list sym := if c then [0;1;1] else [0;0;1].
Definition f (c:bool) : list sym := if c then [0;1;1] else [1;1;1].
Definition st (c:bool) : Q := if c then E else A.
Definition X (b:bool) : list sym := if b then [0;1;1] else [1;1;1].

Lemma WALL_start r: const 0 {{A}}> [0;1;1] *> r -->+ const 0 <* [0;1] <* g true {{E}}> r.
Proof. cbn; triv. Qed.

Lemma CHUNK l r c b:
  l <* g c {{st c}}> X b *> r -->+ l <* f (xorb c b) <* g (xorb c b) {{st (xorb c b)}}> r.
Proof. destruct c, b; cbn; triv. Qed.

Lemma DEFECT_E l r:
  l <* f true <* g true {{E}}> [0;1] *> r -->+ l <* [1;1;0;1;1] <* g false {{A}}> r.
Proof. cbn; triv. Qed.

Lemma DEFECT_A l r:
  l <* g false {{A}}> [0;1] *> r -->+ l <* [0;1;1] <* [1;1] {{D}}> r.
Proof. cbn; triv. Qed.

Lemma WIPE_chunk l r b:
  l {{D}}> X b *> r -->+ l <* [1;1;0] {{D}}> r.
Proof. destruct b; cbn; triv. Qed.

Lemma WIPE_end l:
  l {{D}}> const 0 -->+ l <* [0] <{{B}} [1;1;1] *> const 0.
Proof. cbn; triv. Qed.

Lemma WALL_R1 l:
  l <* g true {{E}}> const 0 -->+ l <{{B}} [0;1;1;1;1;1] *> const 0.
Proof. cbn; triv. Qed.

Lemma WALL_R0 l:
  l <* f true <* f false <* f false <* g false {{A}}> const 0 -->+
  l <{{B}} [0;1;1;1;1;1;1;1;0;1;1;1;1;1] *> const 0.
Proof. cbn; triv. Qed.

Lemma LEFT_x l r: l <* f true <{{B}} r -->+ l <{{B}} [0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma LEFT_y l r: l <* f false <{{B}} r -->+ l <{{B}} [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma LEFT_Dy l r: l <* [1;1;0;1;1] <{{B}} r -->+ l <{{B}} [0;1;1;1;1] *> r.
Proof. cbn; triv. Qed.

Lemma WALL_return r:
  const 0 <* [0;1] <{{B}} r -->+ const 0 {{A}}> [0;1;1] *> r.
Proof. cbn; triv. Qed.

(** ===== Tokens and the token step ===== *)
Inductive tok := tx | ty | tD.

Definition enc_tok (t:tok) : list sym :=
  match t with tx => [0;1;1] | ty => [1;1;1] | tD => [0;1] end.
Fixpoint enc (w:list tok) : list sym :=
  match w with [] => [] | t::w' => enc_tok t ++ enc w' end.

(** pre-sweep items (newest first): PX = output x, PY = output y, PDY = output "D y" *)
Inductive item := PX | PY | PDY.
Definition iw (i:item) : list sym :=
  match i with PX => f true | PY => f false | PDY => [1;1;0;1;1] end.
Definition itoks (i:item) : list tok :=
  match i with PX => [tx] | PY => [ty] | PDY => [tD;ty] end.

Fixpoint Wl (l:side) (its:list item) : side :=
  match its with [] => l | i::its' => Wl l its' <* iw i end.
Fixpoint render (its:list item) : list tok :=
  match its with [] => [] | i::its' => render its' ++ itoks i end.

Definition isD (t:tok) : bool := match t with tD => true | _ => false end.

Fixpoint rsweep (its:list item) (c:bool) (w:list tok) : option (list tok) :=
  match w with
  | [] =>
      if c then Some (tx :: render its ++ [tx;ty])
      else match its with
           | PY::PY::PX::its' => Some (tx :: render its' ++ [tD;ty;ty;tx;ty])
           | _ => None
           end
  | tx::w' => rsweep ((if c then PY else PX)::its) (negb c) w'
  | ty::w' => rsweep ((if c then PX else PY)::its) c w'
  | tD::w' =>
      if c then
        match its with
        | PX::its' => rsweep (PDY::its') false w'
        | _ => None
        end
      else if existsb isD w' then None
      else Some (tx :: render its ++ repeat tx (length w' + 2) ++ [ty])
  end.

Definition tstep (w:list tok) : option (list tok) :=
  match w with tx::w' => rsweep [] true w' | _ => None end.

Definition C (w:list tok) := const 0 {{A}}> enc w *> const 0.

(** ===== Simulation ===== *)
Lemma enc_app u v: enc (u ++ v) = enc u ++ enc v.
Proof. induction u; cbn; [reflexivity|]. rewrite IHu, app_assoc. reflexivity. Qed.

Lemma LEFT_items its: forall l r,
  Wl l its <{{B}} r -->* l <{{B}} enc (render its) *> r.
Proof.
  induction its as [|i its IH]; intros l r.
  - cbn. apply evstep_refl.
  - cbn [Wl render]. rewrite enc_app, Str_app_assoc.
    eapply evstep_trans; [|apply IH].
    destruct i; cbn [iw itoks enc enc_tok]; rewrite ?app_nil_r.
    + apply progress_evstep, LEFT_x.
    + apply progress_evstep, LEFT_y.
    + apply progress_evstep, LEFT_Dy.
Qed.

Lemma finish its R:
  Wl (const 0 <* [0;1]) its <{{B}} enc R *> const 0 -->+ C (tx :: render its ++ R).
Proof.
  eapply evstep_progress_trans.
  - apply LEFT_items.
  - unfold C. cbn [enc enc_tok]. rewrite enc_app, !Str_app_assoc.
    apply WALL_return.
Qed.

Lemma concat_repeat_snoc {T} (a:list T) n: concat (repeat a n) ++ a = a ++ concat (repeat a n).
Proof.
  induction n as [|n IH]; cbn; [rewrite app_nil_r; reflexivity|].
  rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma wipe_run w l: existsb isD w = false ->
  l {{D}}> enc w *> const 0 -->* l <* concat (repeat [1;1;0] (length w)) {{D}}> const 0.
Proof.
  revert l. induction w as [|t w IH]; intros l H.
  - cbn. apply evstep_refl.
  - assert (Hr: l <* concat (repeat [1;1;0] (length (t::w))) =
                (l <* [1;1;0]) <* concat (repeat [1;1;0] (length w))).
    { cbn [length repeat concat]. rewrite <- Str_app_assoc, concat_repeat_snoc. reflexivity. }
    rewrite Hr.
    destruct t; cbn in H; try discriminate;
    cbn [enc enc_tok]; rewrite Str_app_assoc.
    + eapply evstep_trans. { apply progress_evstep, (WIPE_chunk l _ true). } apply IH, H.
    + eapply evstep_trans. { apply progress_evstep, (WIPE_chunk l _ false). } apply IH, H.
Qed.

Lemma Wl_eq l its: Wl l its = concat (map iw its) *> l.
Proof.
  induction its as [|i its IH]; cbn; [reflexivity|].
  rewrite IH, Str_app_assoc. reflexivity.
Qed.

Lemma Wl_app l a b: Wl l (a ++ b) = Wl (Wl l b) a.
Proof. induction a as [|i a IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma render_app a b: render (a ++ b) = render b ++ render a.
Proof. induction a as [|i a IH]; cbn; [rewrite app_nil_r; reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma render_PX n: render (repeat PX n) = repeat tx n.
Proof.
  induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH.
  replace [tx] with (repeat tx 1) by reflexivity.
  rewrite <- repeat_app. replace (n+1) with (S n) by lia. reflexivity.
Qed.

Lemma shift_list k: [0] ++ concat (repeat [1;1;0] k) ++ [1;1] = concat (repeat [0;1;1] (S k)).
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (concat (repeat [0;1;1] (S (S k)))) with ([0;1;1] ++ concat (repeat [0;1;1] (S k))).
  rewrite <- IH. simpl. reflexivity.
Qed.

Lemma wipe_shape (l:side) k:
  l <* [0;1;1] <* [1;1] <* concat (repeat [1;1;0] k) <* [0] =
  Wl l (repeat PX (k+2)).
Proof.
  rewrite Wl_eq, map_repeat. rewrite <- !Str_app_assoc. f_equal.
  change (iw PX) with [0;1;1].
  rewrite <- (app_assoc [0]), shift_list. replace (k+2) with (S k + 1) by lia.
  rewrite repeat_app, concat_app. cbn [repeat concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rsweep_sim w: forall its c w',
  rsweep its c w = Some w' ->
  Wl (const 0 <* [0;1]) its <* g c {{st c}}> enc w *> const 0 -->+ C w'.
Proof.
  induction w as [|t w IH]; intros its c w' H.
  - cbn in H. destruct c.
    + inversion H; subst. cbn [enc].
      eapply progress_trans. { apply WALL_R1. }
      replace [0;1;1;1;1;1] with (enc [tx;ty]) by reflexivity.
      apply finish.
    + destruct its as [|[] [|[] [|[] its']]]; try discriminate.
      inversion H; subst. cbn [enc Wl].
      eapply progress_trans. { apply WALL_R0. }
      replace [0;1;1;1;1;1;1;1;0;1;1;1;1;1] with (enc [tD;ty;ty;tx;ty]) by reflexivity.
      apply finish.
  - destruct t.
    + cbn in H. cbn [enc enc_tok]. rewrite Str_app_assoc.
      eapply progress_trans.
      { replace [0;1;1] with (X true) by reflexivity. apply CHUNK. }
      replace (xorb c true) with (negb c) by (destruct c; reflexivity).
      specialize (IH _ _ _ H). destruct c; exact IH.
    + cbn in H. cbn [enc enc_tok]. rewrite Str_app_assoc.
      eapply progress_trans.
      { replace [1;1;1] with (X false) by reflexivity. apply CHUNK. }
      replace (xorb c false) with c by (destruct c; reflexivity).
      specialize (IH _ _ _ H). destruct c; exact IH.
    + cbn [rsweep] in H. destruct c.
      * destruct its as [|[] its']; try discriminate.
        cbn [enc enc_tok Wl]. rewrite Str_app_assoc.
        eapply progress_trans. { apply DEFECT_E. }
        apply (IH (PDY::its') false w' H).
      * destruct (existsb isD w) eqn:ED; try discriminate.
        inversion H; subst. clear H.
        cbn [enc enc_tok]. rewrite Str_app_assoc.
        eapply progress_trans. { apply DEFECT_A. }
        eapply evstep_progress_trans. { apply wipe_run, ED. }
        eapply progress_trans. { apply WIPE_end. }
        rewrite wipe_shape, <- Wl_app.
        replace [1;1;1] with (enc [ty]) by reflexivity.
        eapply progress_evstep_trans. 2:{ apply evstep_refl. }
        replace (tx :: render its ++ repeat tx (length w + 2) ++ [ty])
          with (tx :: render (repeat PX (length w + 2) ++ its) ++ [ty]).
        2:{ rewrite render_app, render_PX, <- app_assoc. reflexivity. }
        apply finish.
Qed.

Lemma tstep_sim w w': tstep w = Some w' -> C w -->+ C w'.
Proof.
  destruct w as [|[] w]; cbn [tstep]; try discriminate.
  intro H. unfold C. cbn [enc enc_tok]. rewrite Str_app_assoc.
  eapply progress_trans. { apply WALL_start. }
  apply (rsweep_sim w [] true w' H).
Qed.


Open Scope list_scope.
Definition w1 : list tok := [tx;tx;ty;ty;ty;ty;tx;tx;ty;ty;tx;tx;tx;tx;ty;ty;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;tx;ty].

Lemma init: c0 -[ tm ]->* C w1.
Proof.
  unfold C, w1. cbn [enc enc_tok app].
  solve_init.
Qed.

Fixpoint iter (n:nat) (w:list tok) : option (list tok) :=
  match n with O => Some w | S n' => match tstep w with Some w' => iter n' w' | None => None end end.

Theorem nonhalt_of_tokens: (forall n, iter n w1 <> None) -> ~ halts tm c0.
Proof.
  intro H.
  eapply multistep_nonhalt. { apply init. }
  apply progress_nonhalt_cond with (C := C) (P := fun w => forall n, iter n w <> None).
  - intros w Hw.
    destruct (tstep w) as [w'|] eqn:E.
    + exists w'. split. { apply tstep_sim, E. }
      intro n. specialize (Hw (S n)). cbn in Hw. rewrite E in Hw. exact Hw.
    + exfalso. apply (Hw (S O)). cbn. rewrite E. reflexivity.
  - exact H.
Qed.


(** ************************** Part 2: the tail system never halts ************************** *)
Open Scope nat_scope.
Module Tail.

(* ---- FIB1Poly ---- *)
(** GF(2) power series as coefficient functions, and the parity profile Q of a bit list. *)

Definition poly := nat -> bool.
Definition peq (p q : poly) := forall i, p i = q i.
Infix "==" := peq (at level 70).

Definition pzero : poly := fun _ => false.
Definition pone : poly := fun i => Nat.eqb i 0.
Definition pxor (p q : poly) : poly := fun i => xorb (p i) (q i).
Definition pshl (a:nat) (p:poly) : poly := fun i => if Nat.leb a i then p (i - a) else false.
Definition pshr (a:nat) (p:poly) : poly := fun i => p (i + a).
Definition mz (p:poly) : poly := pxor p (pshl 1 p).
Fixpoint mzn (n:nat) (p:poly) : poly := match n with O => p | S n' => mz (mzn n' p) end.
Definition pbit (b:bool) : poly := if b then pone else pzero.

Lemma peq_refl p : p == p. Proof. intro; reflexivity. Qed.
Lemma peq_sym p q : p == q -> q == p. Proof. intros H i; rewrite H; reflexivity. Qed.
Lemma peq_trans p q r : p == q -> q == r -> p == r. Proof. intros H1 H2 i; rewrite H1; apply H2. Qed.

Lemma pxor_proper p p' q q' : p == p' -> q == q' -> pxor p q == pxor p' q'.
Proof. intros H1 H2 i; unfold pxor; rewrite H1, H2; reflexivity. Qed.
Lemma pshl_proper a p p' : p == p' -> pshl a p == pshl a p'.
Proof. intros H i; unfold pshl; destruct (Nat.leb a i); [apply H|reflexivity]. Qed.
Lemma pshr_proper a p p' : p == p' -> pshr a p == pshr a p'.
Proof. intros H i; apply H. Qed.
Lemma mz_proper p p' : p == p' -> mz p == mz p'.
Proof. intros H. apply pxor_proper; [exact H| apply pshl_proper, H]. Qed.
Lemma mzn_proper n p p' : p == p' -> mzn n p == mzn n p'.
Proof. induction n; cbn; intros H; [exact H| apply mz_proper, IHn, H]. Qed.

#[global] Instance peq_equiv : Equivalence peq.
Proof. split; [exact peq_refl|exact peq_sym|exact peq_trans]. Qed.
#[global] Instance pxor_morph : Proper (peq ==> peq ==> peq) pxor.
Proof. intros ? ? H1 ? ? H2; apply pxor_proper; assumption. Qed.
#[global] Instance pshl_morph a : Proper (peq ==> peq) (pshl a).
Proof. intros ? ? H; apply pshl_proper, H. Qed.
#[global] Instance pshr_morph a : Proper (peq ==> peq) (pshr a).
Proof. intros ? ? H; apply pshr_proper, H. Qed.
#[global] Instance mz_morph : Proper (peq ==> peq) mz.
Proof. intros ? ? H; apply mz_proper, H. Qed.
#[global] Instance mzn_morph n : Proper (peq ==> peq) (mzn n).
Proof. intros ? ? H; apply mzn_proper, H. Qed.

Lemma pxor_comm p q : pxor p q == pxor q p. Proof. intro i; apply xorb_comm. Qed.
Lemma pxor_assoc p q r : pxor (pxor p q) r == pxor p (pxor q r).
Proof. intro i; unfold pxor; rewrite xorb_assoc; reflexivity. Qed.
Lemma pxor_zero_r p : pxor p pzero == p. Proof. intro i; unfold pxor, pzero; apply xorb_false_r. Qed.
Lemma pxor_zero_l p : pxor pzero p == p. Proof. intro i; unfold pxor, pzero; apply xorb_false_l. Qed.
Lemma pxor_self p : pxor p p == pzero. Proof. intro i; unfold pxor, pzero; apply xorb_nilpotent. Qed.

Lemma pshl_xor a p q : pshl a (pxor p q) == pxor (pshl a p) (pshl a q).
Proof. intro i; unfold pshl, pxor; destruct (Nat.leb a i); reflexivity. Qed.
Lemma pshl_add a b p : pshl a (pshl b p) == pshl (a+b) p.
Proof.
  intro i; unfold pshl.
  destruct (Nat.leb_spec a i), (Nat.leb_spec (a+b) i), (Nat.leb_spec b (i-a)); try lia; try reflexivity.
  f_equal; lia.
Qed.
Lemma pshl_0 p : pshl 0 p == p.
Proof. intro i; unfold pshl; cbn; f_equal; lia. Qed.
Lemma pshl_zero a : pshl a pzero == pzero.
Proof. intro i; unfold pshl, pzero; destruct (Nat.leb a i); reflexivity. Qed.

Lemma mz_xor p q : mz (pxor p q) == pxor (mz p) (mz q).
Proof. intro i; unfold mz, pxor, pshl; destruct (Nat.leb 1 i); [|rewrite !xorb_false_r]; try reflexivity.
  rewrite !xorb_assoc; f_equal; rewrite <- !xorb_assoc; f_equal; apply xorb_comm. Qed.
Lemma mz_shl a p : mz (pshl a p) == pshl a (mz p).
Proof.
  intro i; unfold mz, pxor, pshl.
  destruct (Nat.leb_spec 1 i), (Nat.leb_spec a i), (Nat.leb_spec a (i-1)), (Nat.leb_spec 1 (i-a)); try lia;
    rewrite ?xorb_false_r, ?xorb_false_l;
    first [ reflexivity
          | (replace (i - 1 - a) with (i - a - 1) by lia; reflexivity)
          | (assert (i = a) by lia; subst; reflexivity)
          | idtac ].
  all: try (replace (i - a) with 0 by lia; reflexivity).
Qed.
Lemma mzn_xor n p q : mzn n (pxor p q) == pxor (mzn n p) (mzn n q).
Proof.
  induction n; cbn; [apply peq_refl|].
  eapply peq_trans; [apply mz_proper, IHn|apply mz_xor].
Qed.
Lemma mzn_shl n a p : mzn n (pshl a p) == pshl a (mzn n p).
Proof.
  induction n; cbn; [apply peq_refl|].
  eapply peq_trans; [apply mz_proper, IHn|apply mz_shl].
Qed.
Lemma mzn_add a b p : mzn (a+b) p == mzn a (mzn b p).
Proof. induction a; cbn; [apply peq_refl| apply mz_proper, IHa]. Qed.
Lemma mzn_zero n : mzn n pzero == pzero.
Proof.
  induction n; cbn; [apply peq_refl|].
  eapply peq_trans; [apply mz_proper, IHn|]. intro i; unfold mz, pxor, pshl, pzero; destruct (Nat.leb 1 i); reflexivity.
Qed.

(** Frobenius: (1+z)^(2^k) = 1 + z^(2^k). *)
Lemma frob k p : mzn (2^k) p == pxor p (pshl (2^k) p).
Proof.
  revert p; induction k; intro p.
  - cbn. apply peq_refl.
  - replace (2^S k) with (2^k + 2^k) by (cbn; lia).
    eapply peq_trans; [apply mzn_add|].
    eapply peq_trans; [apply mzn_proper, IHk|].
    eapply peq_trans; [apply IHk|].
    intro i; unfold pxor, pshl.
    destruct (Nat.leb_spec (2^k) i), (Nat.leb_spec (2^k+2^k) i), (Nat.leb_spec (2^k) (i-2^k)); try lia;
      rewrite ?xorb_false_r; try reflexivity.
    + replace (i - 2^k - 2^k) with (i - (2^k+2^k)) by lia.
      destruct (p i), (p (i-2^k)), (p (i - (2^k+2^k))); reflexivity.
    + destruct (p i), (p (i-2^k)); reflexivity.
Qed.

(** ===== Bit lists ===== *)
Fixpoint parity (l:list bool) : bool := match l with [] => false | a::l' => xorb a (parity l') end.

Fixpoint pxl (c:bool) (l:list bool) : list bool :=
  match l with [] => [] | a::l' => xorb c a :: pxl (xorb c a) l' end.
Definition F (l:list bool) : list bool := firstn (length l) (false :: pxl false l).

Fixpoint Qf (acc:poly) (l:list bool) : poly :=
  match l with [] => acc | a::l' => Qf (pxor (mz acc) (pbit a)) l' end.
Definition Q (l:list bool) : poly := Qf pzero l.

Lemma Qf_proper l : forall p p', p == p' -> Qf p l == Qf p' l.
Proof.
  induction l; cbn; intros p p' H; [exact H|].
  apply IHl, pxor_proper; [apply mz_proper, H|apply peq_refl].
Qed.

Lemma mz_zero : mz pzero == pzero.
Proof. intro i; unfold mz, pxor, pshl, pzero; destruct (Nat.leb 1 i); reflexivity. Qed.
Lemma mzn_mz n p : mzn n (mz p) == mz (mzn n p).
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

#[global] Instance Qf_morph l : Proper (peq ==> peq) (fun p => Qf p l).
Proof. intros ? ? H; apply Qf_proper, H. Qed.

Lemma Qf_lin l : forall acc, Qf acc l == pxor (mzn (length l) acc) (Q l).
Proof.
  induction l as [|a l IH]; intro acc.
  - unfold Q; cbn. rewrite pxor_zero_r. reflexivity.
  - unfold Q; cbn [Qf length mzn]. rewrite IH. rewrite (IH (pxor (mz pzero) (pbit a))).
    rewrite mz_zero, pxor_zero_l, !mzn_xor, mzn_mz, pxor_assoc. reflexivity.
Qed.

Lemma Qf_app u : forall acc v, Qf acc (u ++ v) = Qf (Qf acc u) v.
Proof. induction u; cbn; intros; [reflexivity|apply IHu]. Qed.

Lemma Q_app u v : Q (u ++ v) == pxor (mzn (length v) (Q u)) (Q v).
Proof. unfold Q at 1. rewrite Qf_app. apply Qf_lin. Qed.

Fixpoint bx (u v : list bool) : list bool :=
  match u, v with
  | a::u', b::v' => xorb a b :: bx u' v'
  | [], _ => v
  | _, [] => u
  end.

Lemma Qf_xor u : forall v p q, length u = length v ->
  Qf (pxor p q) (bx u v) == pxor (Qf p u) (Qf q v).
Proof.
  induction u as [|a u IH]; intros [|b v] p q H; cbn in *; try lia; [reflexivity|].
  rewrite <- IH by lia. apply Qf_proper.
  rewrite mz_xor. intro i; unfold pxor, pbit, pone, pzero; destruct a, b; cbn;
    destruct (Nat.eqb i 0), (mz p i), (mz q i); reflexivity.
Qed.

Lemma Q_xor u v : length u = length v -> Q (bx u v) == pxor (Q u) (Q v).
Proof. intro H. unfold Q. rewrite <- Qf_xor by exact H. apply Qf_proper. intro; reflexivity. Qed.

Lemma Qf_zeros a : forall acc, acc == pzero -> Qf acc (repeat false a) == pzero.
Proof.
  induction a; intros acc H; cbn; [exact H|]. apply IHa.
  rewrite H, mz_zero. intro i; reflexivity.
Qed.

Lemma Q_zeros a : Q (repeat false a) == pzero.
Proof. apply Qf_zeros. reflexivity. Qed.

Lemma Q_zeros_app a v : Q (repeat false a ++ v) == Q v.
Proof. rewrite Q_app, Q_zeros, mzn_zero, pxor_zero_l. reflexivity. Qed.

Lemma Q_app_zeros v a : Q (v ++ repeat false a) == mzn a (Q v).
Proof. rewrite Q_app, Q_zeros, pxor_zero_r, repeat_length. reflexivity. Qed.

Lemma Qf_0 l : forall acc, Qf acc l 0 = xorb (acc 0) (parity l).
Proof.
  induction l as [|a l IH]; intro acc; cbn [Qf parity]; [rewrite xorb_false_r; reflexivity|].
  rewrite IH. cbv [pxor mz pshl pbit pone pzero Nat.leb Nat.eqb].
  destruct a, (acc 0), (parity l); reflexivity.
Qed.

Lemma Q_0 l : Q l 0 = parity l.
Proof. unfold Q. rewrite Qf_0. reflexivity. Qed.

(** F and its action on Q *)
Lemma pxl_snoc c l a : pxl c (l ++ [a]) = pxl c l ++ [xorb (xorb c (parity l)) a].
Proof.
  revert c; induction l as [|b l IH]; intro c; cbn; [rewrite xorb_false_r; reflexivity|].
  rewrite IH. destruct c, b, (parity l), a; reflexivity.
Qed.

Lemma parity_app u v : parity (u ++ v) = xorb (parity u) (parity v).
Proof. induction u; cbn; [reflexivity|]. rewrite IHu, xorb_assoc. reflexivity. Qed.

Lemma pxl_length c l : length (pxl c l) = length l.
Proof. revert c; induction l; cbn; intros; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma F_length l : length (F l) = length l.
Proof. unfold F. rewrite firstn_length. cbn. rewrite pxl_length. lia. Qed.

Lemma pxl_last l : false :: pxl false l = F l ++ [parity l].
Proof.
  induction l as [|a l IH] using rev_ind; [reflexivity|].
  unfold F. rewrite pxl_snoc, app_length. cbn [xorb length].
  replace (length l + 1) with (S (length l)) by lia.
  replace (false :: pxl false l ++ [xorb (parity l) a]) with ((false :: pxl false l) ++ [xorb (parity l) a]) by reflexivity.
  rewrite firstn_app. cbn [length]. rewrite pxl_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (cbn; rewrite pxl_length; lia).
  rewrite parity_app. cbn. rewrite xorb_false_r. reflexivity.
Qed.

Lemma F_snoc l a : F (l ++ [a]) = F l ++ [parity l].
Proof.
  rewrite <- pxl_last. unfold F. rewrite pxl_snoc, app_length. cbn [xorb length].
  replace (length l + 1) with (S (length l)) by lia.
  replace (false :: pxl false l ++ [xorb (parity l) a]) with ((false :: pxl false l) ++ [xorb (parity l) a]) by reflexivity.
  rewrite firstn_app. cbn [length]. rewrite pxl_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (cbn; rewrite pxl_length; lia). reflexivity.
Qed.

Lemma pshr1_mz q : pshr 1 (mz q) == pxor (mz (pshr 1 q)) (pbit (q 0)).
Proof.
  intro i. cbv [pshr mz pxor pshl pbit pone pzero]. destruct i as [|i].
  - simpl. destruct (q 0), (q 1); reflexivity.
  - replace (Nat.leb 1 (S i + 1)) with true by (symmetry; apply Nat.leb_le; lia).
    replace (Nat.leb 1 (S i)) with true by (symmetry; apply Nat.leb_le; lia).
    replace (S i + 1 - 1) with (S i) by lia. replace (S i - 1 + 1) with (S i) by lia.
    destruct (q 0); simpl; rewrite ?xorb_false_r; reflexivity.
Qed.

Lemma Q_single x : Q [x] == pbit x.
Proof. unfold Q; cbn. rewrite mz_zero, pxor_zero_l. reflexivity. Qed.

Lemma pshr_xor a p q : pshr a (pxor p q) == pxor (pshr a p) (pshr a q).
Proof. intro i; reflexivity. Qed.

Lemma pshr1_pbit b : pshr 1 (pbit b) == pzero.
Proof. intro i; cbv [pshr pbit pone pzero]; destruct b; [|reflexivity]. destruct (Nat.eqb_spec (i+1) 0); [lia|reflexivity]. Qed.

Lemma Q_F l : Q (F l) == pshr 1 (Q l).
Proof.
  induction l as [|a l IH] using rev_ind.
  - unfold F, Q. cbn. intro; reflexivity.
  - rewrite F_snoc, !Q_app. cbn [length mzn]. rewrite IH, !Q_single.
    rewrite pshr_xor, pshr1_pbit, pxor_zero_r, pshr1_mz, Q_0. reflexivity.
Qed.

Fixpoint Fn (r:nat) (l:list bool) : list bool := match r with O => l | S r' => F (Fn r' l) end.

Lemma Q_Fn r l : Q (Fn r l) == pshr r (Q l).
Proof.
  induction r; cbn.
  - intro i; unfold pshr. rewrite PeanoNat.Nat.add_0_r. reflexivity.
  - rewrite Q_F, IHr. intro i; unfold pshr. rewrite <- PeanoNat.Nat.add_assoc. reflexivity.
Qed.

Lemma parity_Fn r l : parity (Fn r l) = Q l r.
Proof. rewrite <- Q_0, Q_Fn. unfold pshr. reflexivity. Qed.

(** ===== Sparse polynomials: lists of exponents (mod 2 multiplicity) ===== *)
Fixpoint den (LL:list nat) : poly :=
  match LL with [] => pzero | e::LL' => pxor (fun i => Nat.eqb i e) (den LL') end.

Lemma den_app L1 L2 : den (L1 ++ L2) == pxor (den L1) (den L2).
Proof. induction L1; cbn. { rewrite pxor_zero_l. reflexivity. } rewrite IHL1, pxor_assoc. reflexivity. Qed.

Lemma den_dup LL : den (LL ++ LL) == pzero.
Proof. rewrite den_app, pxor_self. reflexivity. Qed.

Lemma den_perm L1 L2 : Permutation L1 L2 -> den L1 == den L2.
Proof.
  induction 1; cbn.
  - reflexivity.
  - rewrite IHPermutation. reflexivity.
  - rewrite <- !pxor_assoc. rewrite (pxor_comm (fun i => Nat.eqb i y)). reflexivity.
  - rewrite IHPermutation1. exact IHPermutation2.
Qed.

Lemma den_shl a LL : den (map (fun e => e + a) LL) == pshl a (den LL).
Proof.
  induction LL as [|e LL IH]; cbn. { rewrite pshl_zero. reflexivity. }
  rewrite IH, pshl_xor. apply pxor_proper; [|reflexivity].
  intro i. unfold pshl. destruct (Nat.leb_spec a i), (Nat.eqb_spec i (e+a)), (Nat.eqb_spec (i-a) e); try lia; reflexivity.
Qed.

Lemma den_shr a LL : Forall (fun e => a <= e) LL -> den (map (fun e => e - a) LL) == pshr a (den LL).
Proof.
  induction 1 as [|e LL He HL IH]; cbn. { intro; reflexivity. }
  rewrite IH, pshr_xor. apply pxor_proper; [|reflexivity].
  intro i. unfold pshr. destruct (Nat.eqb_spec i (e-a)), (Nat.eqb_spec (i+a) e); try lia; reflexivity.
Qed.

Lemma den_single e : den [e] == fun i => Nat.eqb i e.
Proof. cbn. rewrite pxor_zero_r. reflexivity. Qed.

Lemma pone_den : pone == den [0].
Proof. rewrite den_single. intro; reflexivity. Qed.

(** (1+z)^n * 1 has degree n; "on n" = 1+z+...+z^(n-1) *)
Definition on (n:nat) : poly := fun i => Nat.ltb i n.

Lemma den2 a b i : den [a; b] i = xorb (Nat.eqb i a) (Nat.eqb i b).
Proof. cbv [den pxor pzero]. rewrite xorb_false_r. reflexivity. Qed.

Lemma mz_on n : mz (on n) == den [0; n].
Proof.
  intro i. rewrite den2. unfold mz, pxor, pshl, on.
  destruct (Nat.leb_spec 1 i), (Nat.ltb_spec i n), (Nat.ltb_spec (i-1) n), (Nat.eqb_spec i 0), (Nat.eqb_spec i n);
    try lia; reflexivity.
Qed.

Lemma repeat_snoc {T} (a:T) n : repeat a (S n) = repeat a n ++ [a].
Proof. induction n; cbn; [reflexivity|]. cbn in IHn. rewrite IHn. reflexivity. Qed.

Lemma Q_ones n : pshl 1 (Q (repeat true n)) == pxor (mzn n pone) pone.
Proof.
  induction n as [|n IH].
  - cbn. unfold Q; cbn. rewrite pshl_zero. intro i; unfold pxor; destruct (pone i); reflexivity.
  - rewrite repeat_snoc, Q_app, Q_single. cbn [length mzn].
    rewrite pshl_xor, <- mz_shl, IH, mz_xor.
    generalize (mzn n pone) as p. intros p i. cbv [pxor mz pshl pbit pone].
    destruct (Nat.leb_spec 1 i), (Nat.eqb_spec i 0), (Nat.eqb_spec (i-1) 0); try lia;
      destruct (p i), (p (i-1)); reflexivity.
Qed.

(* ---- FIB1Tail ---- *)
(** The tail system on segment lists, and the lift lemma. *)

Definition G1 (sg:list bool) : list bool := false :: pxl false sg.

Fixpoint beql (u v : list bool) : bool :=
  match u, v with
  | [], [] => true
  | a::u', b::v' => Bool.eqb a b && beql u' v'
  | _, _ => false
  end.
Lemma beql_spec u v : beql u v = true <-> u = v.
Proof.
  revert v; induction u as [|a u IH]; intros [|b v]; cbn; split; intro H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2]. apply Bool.eqb_prop in H1. apply IH in H2. subst. reflexivity.
  - inversion H; subst. apply andb_true_iff. split; [apply eqb_reflx|apply IH; reflexivity].
Qed.

Fixpoint Gs (W : list (list bool)) : option (list (list bool)) :=
  match W with
  | [] => None
  | [sg] =>
      if parity sg then Some [G1 sg ++ [true;false]]
      else if beql (skipn (length sg - 2) (G1 sg)) [true;false;false]
           then Some [firstn (length sg - 2) (G1 sg); [false;false;true;false]]
           else None
  | sg :: W' =>
      if parity sg then
        match Gs W' with Some W'' => Some (F sg :: W'') | None => None end
      else
        match W' with
        | [sg'] => Some [G1 sg ++ repeat true (length sg') ++ [true;true;false]]
        | _ => None
        end
  end.

Lemma Gs_cons2 a b RR : Gs (a :: b :: RR) =
  if parity a then option_map (cons (F a)) (Gs (b :: RR))
  else match RR with [] => Some [G1 a ++ repeat true (length b) ++ [true;true;false]] | _ => None end.
Proof.
  change (Gs (a :: b :: RR)) with
    (if parity a then match Gs (b :: RR) with Some W'' => Some (F a :: W'') | None => None end
     else match b :: RR with [sg'] => Some [G1 a ++ repeat true (length sg') ++ [true;true;false]] | _ => None end).
  destruct (parity a); [destruct (Gs (b :: RR)); reflexivity|]. destruct RR; reflexivity.
Qed.

(** ===== bx (xor with zero padding) lemmas ===== *)
Lemma bx_nil_r u : bx u [] = u.
Proof. destruct u; reflexivity. Qed.

Lemma length_bx u v : length (bx u v) = max (length u) (length v).
Proof. revert v; induction u; intros [|b v]; cbn; try reflexivity; try lia. rewrite IHu. reflexivity. Qed.

Lemma bx_app_l u w v : length v <= length u -> bx (u ++ w) v = bx u v ++ w.
Proof.
  revert v; induction u as [|a u IH]; intros [|b v] H; cbn in *; try lia; try reflexivity.
  - rewrite bx_nil_r. reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_bx n u v : length v <= n -> firstn n (bx u v) = bx (firstn n u) v.
Proof.
  revert u v; induction n; intros u v H.
  - destruct v; cbn in *; rewrite ?bx_nil_r; try reflexivity; lia.
  - destruct u, v; cbn in *; rewrite ?firstn_nil, ?bx_nil_r; try reflexivity;
      try (rewrite firstn_all2 by lia; reflexivity); rewrite IHn by lia; reflexivity.
Qed.

Lemma skipn_bx n u v : length v <= n -> skipn n (bx u v) = skipn n u.
Proof.
  revert u v; induction n; intros u v H.
  - destruct v; cbn in *; rewrite ?bx_nil_r; try reflexivity; lia.
  - destruct u, v; cbn in *; rewrite ?skipn_nil, ?bx_nil_r; try reflexivity;
      try (rewrite skipn_all2 by lia; reflexivity); apply IHn; lia.
Qed.

Lemma bx_zeros u a : a <= length u -> bx u (repeat false a) = u.
Proof.
  revert u; induction a; intros [|x u] H; cbn in *; rewrite ?bx_nil_r; try reflexivity; try lia.
  rewrite xorb_false_r, IHa by lia. reflexivity.
Qed.

Lemma bx_pad u v a : length v + a <= length u -> bx u (v ++ repeat false a) = bx u v.
Proof.
  revert u; induction v as [|b v IH]; intros u H; cbn in *.
  - rewrite bx_zeros by lia. destruct u; reflexivity.
  - destruct u as [|x u]; cbn in *; [lia|]. rewrite IH by lia. reflexivity.
Qed.

Lemma parity_bx u v : parity (bx u v) = xorb (parity u) (parity v).
Proof.
  revert v; induction u as [|a u IH]; intros [|b v]; cbn; try reflexivity.
  - rewrite xorb_false_r. reflexivity.
  - rewrite IH. destruct a, b, (parity u), (parity v); reflexivity.
Qed.

Lemma parity_zeros a : parity (repeat false a) = false.
Proof. induction a; cbn; auto. Qed.

Lemma pxl_bx u v c d : length u = length v -> pxl (xorb c d) (bx u v) = bx (pxl c u) (pxl d v).
Proof.
  revert v c d; induction u as [|a u IH]; intros [|b v] c d H; cbn in *; try lia; try reflexivity.
  f_equal; [destruct a, b, c, d; reflexivity|].
  replace (xorb (xorb c d) (xorb a b)) with (xorb (xorb c a) (xorb d b)) by (destruct a, b, c, d; reflexivity).
  apply IH. lia.
Qed.

Lemma G1_bx u v : length u = length v -> G1 (bx u v) = bx (G1 u) (G1 v).
Proof. intro H. unfold G1. cbn. f_equal. apply (pxl_bx u v false false H). Qed.

Lemma pxl_zeros_l a u : pxl false (repeat false a ++ u) = repeat false a ++ pxl false u.
Proof. induction a; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.

Lemma G1_zeros_l a u : G1 (repeat false a ++ u) = repeat false a ++ G1 u.
Proof.
  unfold G1. rewrite pxl_zeros_l.
  replace (false :: repeat false a ++ pxl false u) with (repeat false (S a) ++ pxl false u) by reflexivity.
  rewrite repeat_snoc, <- app_assoc. reflexivity.
Qed.

Lemma pxl_c_parity c u : c = false -> forall a, pxl (xorb c (parity u)) (repeat false a) = repeat (xorb c (parity u)) a.
Proof. intros _ a. induction a; cbn; [reflexivity|]. rewrite xorb_false_r, IHa. reflexivity. Qed.

Lemma pxl_app c u w : pxl c (u ++ w) = pxl c u ++ pxl (xorb c (parity u)) w.
Proof.
  revert c; induction u as [|a u IH]; intro c; cbn; [rewrite xorb_false_r; reflexivity|].
  rewrite IH. f_equal. f_equal. f_equal. destruct c, a, (parity u); reflexivity.
Qed.

Lemma pxl_zeros c a : pxl c (repeat false a) = repeat c a.
Proof. induction a; cbn; [reflexivity|]. rewrite xorb_false_r, IHa. reflexivity. Qed.

Lemma G1_last sg : G1 sg = F sg ++ [parity sg].
Proof. apply pxl_last. Qed.

Lemma G1_pad Y a : parity Y = false -> G1 (Y ++ repeat false a) = F Y ++ repeat false (S a).
Proof.
  intro HY. unfold G1. rewrite pxl_app, pxl_zeros. cbn [xorb]. rewrite HY.
  change (false :: pxl false Y ++ repeat false a) with ((false :: pxl false Y) ++ repeat false a).
  rewrite pxl_last, HY, <- app_assoc. reflexivity.
Qed.

Lemma G1_length sg : length (G1 sg) = S (length sg).
Proof. unfold G1. cbn. rewrite pxl_length. reflexivity. Qed.

(** ===== Lift ===== *)
Definition LS (c:nat) (Y sg:list bool) : list bool := bx (repeat false c ++ sg) Y.

Lemma LS_length c Y sg : length Y <= c + length sg -> length (LS c Y sg) = c + length sg.
Proof. intro H. unfold LS. rewrite length_bx, app_length, repeat_length. lia. Qed.

Lemma LS_parity c Y sg : parity (LS c Y sg) = xorb (parity sg) (parity Y).
Proof. unfold LS. rewrite parity_bx, parity_app, parity_zeros. reflexivity. Qed.

Lemma LS_G1 c Y sg : length Y = c + 2 -> parity Y = false -> 2 <= length sg ->
  G1 (LS c Y sg) = LS c (F Y) (G1 sg).
Proof.
  intros HL HP HS. unfold LS.
  rewrite <- (bx_pad (repeat false c ++ sg) Y (length sg - 2)) by (rewrite app_length, repeat_length; lia).
  rewrite G1_bx by (rewrite !app_length, !repeat_length; lia).
  rewrite G1_zeros_l, G1_pad by exact HP.
  replace (S (length sg - 2)) with (length sg - 1) by lia.
  rewrite bx_pad. 1: reflexivity.
  rewrite F_length, app_length, repeat_length, G1_length. lia.
Qed.

Lemma F_as_G1 sg : F sg = firstn (length sg) (G1 sg).
Proof. reflexivity. Qed.

Lemma firstn_LS c Y sg n : length Y <= c + n -> firstn (c + n) (LS c Y sg) = LS c Y (firstn n sg).
Proof.
  intro H. unfold LS. rewrite firstn_bx by exact H. f_equal.
  rewrite firstn_app, repeat_length, firstn_all2 by (rewrite repeat_length; lia).
  replace (c + n - c) with n by lia. reflexivity.
Qed.

Lemma skipn_LS c Y sg n : length Y <= c + n -> skipn (c + n) (LS c Y sg) = skipn n sg.
Proof.
  intro H. unfold LS. rewrite skipn_bx by exact H.
  rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia).
  replace (c + n - c) with n by lia. reflexivity.
Qed.

Lemma LS_app c Y sg w : length Y <= c + length sg -> LS c Y (sg ++ w) = LS c Y sg ++ w.
Proof.
  intro H. unfold LS. rewrite app_assoc. apply bx_app_l. rewrite app_length, repeat_length. lia.
Qed.

Lemma F_length' Y : length (F Y) = length Y.
Proof. apply F_length. Qed.

Definition liftW (c:nat) (Y:list bool) (W:list (list bool)) : list (list bool) :=
  match W with [] => [] | H::RR => LS c Y H :: RR end.

Lemma lift_step c Y W : length Y = c + 2 -> parity Y = false ->
  (match W with H :: _ => 4 <= length H | [] => False end) ->
  Gs (liftW c Y W) = option_map (liftW c (F Y)) (Gs W).
Proof.
  intros HL HP HW. destruct W as [|H RR]; [contradiction|]. cbn [liftW].
  assert (HLS: length (LS c Y H) = c + length H) by (apply LS_length; lia).
  assert (HFY: length (F Y) = c + 2) by (rewrite F_length; exact HL).
  destruct RR as [|sg' RR].
  - cbn [Gs]. rewrite LS_parity, HP, xorb_false_r.
    destruct (parity H).
    + cbn [option_map liftW]. f_equal. f_equal. rewrite LS_G1 by (auto; lia).
      rewrite LS_app by (rewrite HFY, G1_length; lia). reflexivity.
    + rewrite HLS, LS_G1 by (auto; lia).
      replace (c + length H - 2) with (c + (length H - 2)) by lia.
      rewrite skipn_LS by lia.
      destruct (beql (skipn (length H - 2) (G1 H)) [true;false;false]); [|reflexivity].
      cbn [option_map liftW]. rewrite firstn_LS by lia. reflexivity.
  - rewrite !Gs_cons2, LS_parity, HP, xorb_false_r.
    destruct (parity H).
    + destruct (Gs (sg' :: RR)); cbn [option_map liftW]; [|reflexivity].
      f_equal. f_equal. rewrite !F_as_G1, HLS, LS_G1 by (auto; lia).
      rewrite firstn_LS by lia. reflexivity.
    + destruct RR; cbn [option_map liftW]; [|reflexivity].
      f_equal. f_equal. rewrite LS_G1 by (auto; lia).
      rewrite LS_app by (rewrite HFY, G1_length; lia). reflexivity.
Qed.

(* ---- FIB1Arith ---- *)
(** Constants of the epoch recursion and the two sparse-polynomial identities (PROOF.md steps 2 and 5). *)

Fixpoint bb (m:nat) : nat :=
  match m with 0 => 2 | 1 => 3 | S (S m' as m1) => 2^m1 + bb m' end.

Definition ee (m:nat) := 2^m - bb m.
Definition JJ (m:nat) := ee m + 1.
Definition cc (m:nat) := 2^(S m) - bb m.
Definition eps (m:nat) := if Nat.odd m then 1 else 2.

Lemma pow_S m : 2^(S m) = 2 * 2^m.
Proof. reflexivity. Qed.

Lemma bb_closed m : 3 * bb m = 2^(S m) + (if Nat.odd m then 5 else 4).
Proof.
  induction m as [m IH] using lt_wf_ind.
  destruct m as [|[|m]]; [reflexivity|reflexivity|].
  change (bb (S (S m))) with (2^(S m) + bb m).
  specialize (IH m ltac:(lia)).
  replace (Nat.odd (S (S m))) with (Nat.odd m) by (rewrite !Nat.odd_succ, Nat.even_succ; reflexivity).
  rewrite !pow_S in *. destruct (Nat.odd m); lia.
Qed.

Lemma pow_ge1 m : 1 <= 2^m.
Proof. induction m; cbn; lia. Qed.

Lemma bb_le m : 2 <= m -> bb m <= 2^m.
Proof.
  intro H. pose proof (bb_closed m). rewrite pow_S in H0.
  assert (4 <= 2^m) by (replace m with (2 + (m-2)) by lia; rewrite Nat.pow_add_r; pose proof (pow_ge1 (m-2)); cbn; lia).
  destruct (Nat.odd m); lia.
Qed.

Lemma bb_lt m : 3 <= m -> bb m < 2^m.
Proof.
  intro H. pose proof (bb_closed m). rewrite pow_S in H0.
  assert (8 <= 2^m) by (replace m with (3 + (m-3)) by lia; rewrite Nat.pow_add_r; pose proof (pow_ge1 (m-3)); cbn; lia).
  destruct (Nat.odd m); lia.
Qed.

Lemma bb_ge m : 2 <= m -> 4 <= bb m.
Proof.
  intro H. pose proof (bb_closed m). rewrite pow_S in H0.
  assert (4 <= 2^m) by (replace m with (2 + (m-2)) by lia; rewrite Nat.pow_add_r; pose proof (pow_ge1 (m-2)); cbn; lia).
  destruct (Nat.odd m); lia.
Qed.

Lemma eps_SS m : eps (S (S m)) = eps m.
Proof. unfold eps. rewrite !Nat.odd_succ, Nat.even_succ. reflexivity. Qed.

Lemma eps_range m : eps m = 1 \/ eps m = 2.
Proof. unfold eps; destruct (Nat.odd m); auto. Qed.

(** 3b - 6 + eps = 2^(m+1) *)
Lemma bb_eps m : 2 <= m -> 3 * bb m - 6 + eps m = 2^(S m).
Proof. intro H. pose proof (bb_closed m). unfold eps. destruct (Nat.odd m); lia. Qed.

(** 3J + 3 = 2^m + eps *)
Lemma JJ_eps m : 2 <= m -> 3 * JJ m + 3 = 2^m + eps m.
Proof.
  intro H. pose proof (bb_closed m). pose proof (bb_le m H). unfold JJ, ee, eps. rewrite pow_S in H0.
  destruct (Nat.odd m); lia.
Qed.

Lemma bb_SS m : bb (S (S m)) = 2^(S m) + bb m.
Proof. reflexivity. Qed.

(** ===== Exponent lists ===== *)
Definition E0 (m:nat) : list nat := if Nat.odd m then [0] else [0;1].
Definition Pl (m:nat) : list nat := E0 m ++ [cc m] ++ map (fun i => cc m - 2^i) (seq 0 (S m)).
Definition QYl (k:nat) : list nat :=
  [2 * 2^k - 1] ++ map (fun j => 2^k - 1 - 2^j) (seq 0 k) ++ map (fun j => 2 * 2^k - 1 - 2^j) (seq 0 k).

Lemma den_map_ext (f g : nat -> nat) (l : list nat) : (forall x, In x l -> f x = g x) -> den (map f l) == den (map g l).
Proof. intro H. rewrite (map_ext_in f g l H). reflexivity. Qed.

Lemma seq_S_end n : seq 0 (S n) = seq 0 n ++ [n].
Proof. rewrite seq_S. reflexivity. Qed.

Lemma pow_mono a b : a <= b -> 2^a <= 2^b.
Proof. intro H. apply Nat.pow_le_mono_r; lia. Qed.

Lemma in_seq0 x n : In x (seq 0 n) -> x < n.
Proof. rewrite in_seq. lia. Qed.

Ltac den_pointwise := intro; rewrite ?den_app; unfold pxor.

(** Step 2 identity: P_(m+2) = P_m + z^(1-b_m)(1+z^K) Q_Y, in the shifted-list form. K = 2^(m+1), s = b_m - 1. *)
Lemma birth_identity m : 2 <= m ->
  pxor (den (Pl m))
       (pxor (den (map (fun e => e - (bb m - 1)) (QYl (S m))))
             (pshl (2^(S m)) (den (map (fun e => e - (bb m - 1)) (QYl (S m))))))
  == den (Pl (S (S m))).
Proof.
  intro Hm. set (K := 2^(S m)). set (c := cc m).
  pose proof (bb_le m Hm) as Hb. pose proof (bb_ge m Hm) as Hb4.
  assert (HK: K = 2 * 2^m) by reflexivity.
  assert (Hc: c = K - bb m) by reflexivity.
  assert (Hcm: 2^m <= c) by lia.
  (* rewrite the three shifted lists *)
  assert (L1: den (map (fun e => e - (bb m - 1)) (QYl (S m))) ==
              den ([c + K] ++ map (fun j => c - 2^j) (seq 0 (S m)) ++ map (fun j => c + K - 2^j) (seq 0 (S m)))).
  { unfold QYl. rewrite !map_app, ?map_map. cbn [map].
    rewrite !den_app. apply pxor_proper; [|apply pxor_proper].
    - replace (2 * 2^(S m) - 1 - (bb m - 1)) with (c + K) by (fold K; lia). reflexivity.
    - rewrite ?map_map. apply den_map_ext. intros j Hj. apply in_seq0 in Hj.
      pose proof (pow_mono j m ltac:(lia)). fold K. lia.
    - rewrite ?map_map. apply den_map_ext. intros j Hj. apply in_seq0 in Hj.
      pose proof (pow_mono j m ltac:(lia)). fold K. lia. }
  rewrite L1.
  assert (L2: pshl K (den ([c + K] ++ map (fun j => c - 2^j) (seq 0 (S m)) ++ map (fun j => c + K - 2^j) (seq 0 (S m)))) ==
              den ([c + 2*K] ++ map (fun j => c + K - 2^j) (seq 0 (S m)) ++ map (fun j => c + 2*K - 2^j) (seq 0 (S m)))).
  { rewrite <- den_shl. rewrite !map_app, ?map_map. cbn [map].
    rewrite !den_app. apply pxor_proper; [|apply pxor_proper].
    - replace (c + K + K) with (c + 2*K) by lia. reflexivity.
    - apply den_map_ext. intros j Hj. apply in_seq0 in Hj. pose proof (pow_mono j m ltac:(lia)). lia.
    - apply den_map_ext. intros j Hj. apply in_seq0 in Hj. pose proof (pow_mono j m ltac:(lia)). lia. }
  rewrite L2.
  (* target *)
  assert (L3: den (Pl (S (S m))) ==
              den (E0 m ++ [c + 2*K] ++ map (fun j => c + 2*K - 2^j) (seq 0 (S m)) ++ [c + K; c])).
  { unfold Pl. unfold E0 at 1. rewrite Nat.odd_succ, Nat.even_succ. fold (E0 m).
    replace (cc (S (S m))) with (c + 2*K).
    2:{ unfold cc. rewrite bb_SS. fold K. rewrite (pow_S (S (S m))), (pow_S (S m)). fold K. lia. }
    rewrite (seq_S_end (S (S m))), (seq_S_end (S m)), !map_app. cbn [map].
    replace (c + 2*K - 2^(S m)) with (c + K) by (fold K; lia).
    replace (c + 2*K - 2^(S (S m))) with c by (rewrite (pow_S (S m)); fold K; lia).
    rewrite <- app_assoc. reflexivity. }
  rewrite L3. unfold Pl. fold c.
  set (M1 := map (fun i => c - 2^i) (seq 0 (S m))).
  set (M2 := map (fun j => c + K - 2^j) (seq 0 (S m))).
  set (M3 := map (fun j => c + 2*K - 2^j) (seq 0 (S m))).
  rewrite !den_app. intro i. cbn [den]. unfold pxor, pzero.
  destruct (den (E0 m) i), (den M1 i), (den M2 i), (den M3 i), (Nat.eqb i c), (Nat.eqb i (c+K)), (Nat.eqb i (c+2*K));
    reflexivity.
Qed.

(** ===== Step 5: merge identity ===== *)
Definition E1 (m:nat) : list nat := if Nat.odd m then [] else [1].

Lemma pshr_pshl a p : pshr a (pshl a p) == p.
Proof. intro i. unfold pshr, pshl. destruct (Nat.leb_spec a (i+a)); [|lia]. f_equal; lia. Qed.

Lemma pshl_pshr a p : (forall i, i < a -> p i = false) -> pshl a (pshr a p) == p.
Proof.
  intros H i. unfold pshr, pshl. destruct (Nat.leb_spec a i).
  - f_equal; lia.
  - symmetry; apply H; lia.
Qed.

Lemma low_split e q : (forall i, i < e -> q i = true) -> q == pxor (on e) (pshl e (pshr e q)).
Proof.
  intros H i. unfold pxor, on, pshl, pshr. destruct (Nat.ltb_spec i e), (Nat.leb_spec e i); try lia.
  - rewrite H by lia. reflexivity.
  - replace (i - e + e) with i by lia. reflexivity.
Qed.

Lemma mz_single a : mz (fun i => Nat.eqb i a) == den [a; S a].
Proof.
  intro i. rewrite den2. unfold mz, pxor, pshl.
  destruct (Nat.leb_spec 1 i), (Nat.eqb_spec i a), (Nat.eqb_spec (i-1) a), (Nat.eqb_spec i (S a)); try lia; reflexivity.
Qed.

Lemma mz_den LL : mz (den LL) == den (LL ++ map S LL).
Proof.
  induction LL as [|a LL IH].
  - cbn. rewrite mz_zero. reflexivity.
  - change (den (a::LL)) with (pxor (fun i => Nat.eqb i a) (den LL)).
    rewrite mz_xor, mz_single, IH.
    change ((a :: LL) ++ map S (a :: LL)) with ([a] ++ LL ++ [S a] ++ map S LL).
    rewrite !den_app. intro i. cbn [den]. unfold pxor, pzero.
    destruct (Nat.eqb i a), (Nat.eqb i (S a)), (den LL i), (den (map S LL) i); reflexivity.
Qed.

Lemma mzn_eps_on m e : mzn (eps m) (on e) == den (E0 m ++ map (fun x => x + e) (E0 m)).
Proof.
  unfold eps, E0. destruct (Nat.odd m); cbn [mzn].
  - rewrite mz_on. reflexivity.
  - rewrite mz_on, mz_den. cbn. intro i. unfold pxor, pzero. destruct (Nat.eqb i 0), (Nat.eqb i e), (Nat.eqb i 1), (Nat.eqb i (S e));
      reflexivity.
Qed.

Lemma X_formula m QB : 2 <= m -> mzn (eps m) QB == den (Pl m) -> (forall i, i < ee m -> QB i = true) ->
  mzn (eps m) (pshr (ee m) QB) == den (E1 m ++ [2^m] ++ map (fun i => 2^m - 2^i) (seq 0 m)).
Proof.
  intros Hm HP Hlow.
  pose proof (bb_le m Hm) as Hb.
  assert (He: ee m + 2^m = cc m) by (unfold ee, cc; rewrite pow_S; lia).
  rewrite <- (pshr_pshl (ee m) (mzn (eps m) (pshr (ee m) QB))).
  rewrite <- mzn_shl.
  assert (HQB: pshl (ee m) (pshr (ee m) QB) == pxor QB (on (ee m))).
  { rewrite (low_split (ee m) QB Hlow) at 2. intro i; unfold pxor. destruct (on (ee m) i), (pshl (ee m) (pshr (ee m) QB) i); reflexivity. }
  rewrite HQB, mzn_xor, HP, mzn_eps_on.
  assert (Hsum: pxor (den (Pl m)) (den (E0 m ++ map (fun x => x + ee m) (E0 m))) ==
                den ([cc m] ++ map (fun i => cc m - 2^i) (seq 0 m) ++ map (fun x => x + ee m) (E1 m))).
  { unfold Pl. rewrite seq_S_end, map_app.
    change (map (fun i => cc m - 2^i) [m]) with [cc m - 2^m]. replace (cc m - 2^m) with (ee m) by lia.
    rewrite !den_app. set (D := den (map (fun i => cc m - 2^i) (seq 0 m))).
    pose proof (pow_ge1 m).
    unfold E0, E1; destruct (Nat.odd m); cbn [map den]; intro i; unfold pxor, pzero; destruct (D i);
      repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end; try lia; reflexivity. }
  rewrite Hsum, <- den_shr.
  2:{ rewrite Forall_forall. intros x Hx. rewrite !in_app_iff in Hx. destruct Hx as [Hx|[Hx|Hx]].
      - destruct Hx as [<-|[]]. lia.
      - apply in_map_iff in Hx as [i [<- Hi]]. apply in_seq0 in Hi. pose proof (pow_mono i m ltac:(lia)). lia.
      - unfold E1 in Hx. destruct (Nat.odd m); cbn in Hx; [contradiction|]. destruct Hx as [<-|[]]. lia. }
  rewrite !map_app, map_map. cbn [map].
  replace (cc m - ee m) with (2^m) by lia.
  assert (HM: den (map (fun x => cc m - 2^x - ee m) (seq 0 m)) == den (map (fun i => 2^m - 2^i) (seq 0 m))).
  { apply den_map_ext. intros x Hx. apply in_seq0 in Hx. pose proof (pow_mono x m ltac:(lia)). lia. }
  rewrite !den_app, HM. unfold E1. destruct (Nat.odd m); cbn [map den].
  - intro i. unfold pxor, pzero. destruct (Nat.eqb i (2^m)), (den (map (fun i0 => 2^m - 2^i0) (seq 0 m)) i); reflexivity.
  - replace (1 + ee m - ee m) with 1 by lia.
    intro i. unfold pxor, pzero. destruct (Nat.eqb i (2^m)), (Nat.eqb i 1), (den (map (fun i0 => 2^m - 2^i0) (seq 0 m)) i); reflexivity.
Qed.

Lemma mzn_epsm1_pone m : mzn (eps m - 1) pone == den (E0 m).
Proof.
  unfold eps, E0. destruct (Nat.odd m); cbn [Nat.sub mzn].
  - rewrite pone_den. reflexivity.
  - rewrite pone_den, mz_den. reflexivity.
Qed.

Lemma merge_identity m QH : 2 <= m -> QH 0 = false ->
  mzn (eps m) QH == den (E1 m ++ [2^m] ++ map (fun i => 2^m - 2^i) (seq 0 m)) ->
  pxor (mzn (3 * JJ m + 2) (mz (pshr 1 QH))) (Q (repeat true (3 * JJ m + 2))) == den (QYl m).
Proof.
  intros Hm H0 HX.
  pose proof (JJ_eps m Hm) as HJ. pose proof (eps_range m) as Heps.
  rewrite <- (pshr_pshl 1 (pxor _ _)), <- (pshr_pshl 1 (den (QYl m))).
  apply pshr_proper.
  rewrite pshl_xor, Q_ones, <- mzn_shl, <- mz_shl, pshl_pshr by (intros i Hi; replace i with 0 by lia; exact H0).
  replace (mz QH) with (mzn 1 QH) by reflexivity.
  rewrite <- mzn_add.
  replace (3 * JJ m + 2 + 1) with (2^m + eps m) by lia.
  replace (3 * JJ m + 2) with (2^m + (eps m - 1)) by lia.
  rewrite !mzn_add, !frob, HX, mzn_epsm1_pone.
  rewrite <- !den_shl.
  unfold QYl. rewrite !map_app, ?map_map. cbn [map].
  assert (HA: den (map (fun x => 2^m - 1 - 2^x + 1) (seq 0 m)) == den (map (fun i => 2^m - 2^i) (seq 0 m))).
  { apply den_map_ext. intros x Hx. apply in_seq0 in Hx. assert (2^x < 2^m) by (apply Nat.pow_lt_mono_r; lia). lia. }
  assert (HB: den (map (fun x => 2 * 2^m - 1 - 2^x + 1) (seq 0 m)) == den (map (fun i => 2^m - 2^i + 2^m) (seq 0 m))).
  { apply den_map_ext. intros x Hx. apply in_seq0 in Hx. assert (2^x < 2^m) by (apply Nat.pow_lt_mono_r; lia). lia. }
  rewrite !den_app, HA, HB.
  set (M := den (map (fun i => 2^m - 2^i) (seq 0 m))).
  set (M' := den (map (fun i => 2^m - 2^i + 2^m) (seq 0 m))).
  pose proof (pow_ge1 m).
  unfold E0, E1; destruct (Nat.odd m); cbn [map den]; intro i; unfold pxor, pzero, pone; destruct (M i), (M' i);
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end; try lia; reflexivity.
Qed.

Lemma den_above i LL : Forall (fun x => i < x) LL -> den LL i = false.
Proof.
  induction 1 as [|x LL Hx HL IH]; cbn; [reflexivity|]. unfold pxor. rewrite IH.
  destruct (Nat.eqb_spec i x); [lia|reflexivity].
Qed.

Lemma ee_pos m : 3 <= m -> 1 <= ee m /\ (Nat.even m = true -> 2 <= ee m).
Proof.
  intro H. pose proof (bb_closed m) as Hc. unfold ee. rewrite pow_S in Hc.
  assert (8 <= 2^m) by (replace m with (3 + (m-3)) by lia; rewrite Nat.pow_add_r; pose proof (pow_ge1 (m-3)); cbn; lia).
  rewrite <- Nat.negb_odd. destruct (Nat.odd m); cbn; split; intros; try discriminate; lia.
Qed.

Lemma Pl_low m i : 3 <= m -> i <= ee m -> den (Pl m) i = xorb (den (E0 m) i) (Nat.eqb i (ee m)).
Proof.
  intros Hm Hi. pose proof (bb_le m ltac:(lia)) as Hb.
  assert (He: ee m + 2^m = cc m) by (unfold ee, cc; rewrite pow_S; lia).
  assert (Heq: den (Pl m) == pxor (den (E0 m)) (pxor (den [cc m]) (pxor (den (map (fun i0 => cc m - 2^i0) (seq 0 m))) (den [ee m])))).
  { unfold Pl. rewrite seq_S_end, map_app.
    change (map (fun i => cc m - 2^i) [m]) with [cc m - 2^m]. replace (cc m - 2^m) with (ee m) by lia.
    rewrite !den_app. reflexivity. }
  rewrite (Heq i). unfold pxor. rewrite (den_above i (map (fun i0 => cc m - 2^i0) (seq 0 m))).
  2:{ rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx as [j [<- Hj]]. apply in_seq0 in Hj.
      assert (2^j <= 2^(m-1)) by (apply pow_mono; lia).
      assert (2 * 2^(m-1) = 2^m) by (replace m with (S (m-1)) at 2 by lia; reflexivity).
      assert (1 <= 2^(m-1)) by apply pow_ge1. lia. }
  cbn [den]. unfold pxor, pzero.
  assert (1 <= 2^m) by apply pow_ge1.
  destruct (Nat.eqb_spec i (cc m)); [lia|]. destruct (den (E0 m) i), (Nat.eqb i (ee m)); reflexivity.
Qed.

Lemma life_from_P m QB : 3 <= m -> mzn (eps m) QB == den (Pl m) ->
  (forall i, i < ee m -> QB i = true) /\ QB (ee m) = false.
Proof.
  intros Hm HP. pose proof (ee_pos m Hm) as [He1 He2].
  assert (HPl: forall i, i <= ee m -> mzn (eps m) QB i = xorb (den (E0 m) i) (Nat.eqb i (ee m))).
  { intros i Hi. rewrite HP. apply Pl_low; auto. }
  assert (Heven: Nat.odd m = false -> 2 <= ee m) by (intro Ho; apply He2; rewrite <- Nat.negb_odd, Ho; reflexivity).
  clear HP He2. set (e := ee m) in *. clearbody e.
  unfold eps, E0 in *. destruct (Nat.odd m) eqn:Eo; cbn [mzn] in HPl.
  - (* odd: mz QB *)
    assert (Hlow: forall i, i < e -> QB i = true).
    { induction i as [|i IH]; intro Hi.
      - specialize (HPl 0 ltac:(lia)). replace (Nat.eqb 0 e) with false in HPl by (symmetry; apply Nat.eqb_neq; lia).
        unfold mz, pxor, pshl in HPl. cbn in HPl. rewrite xorb_false_r in HPl. exact HPl.
      - specialize (HPl (S i) ltac:(lia)). replace (Nat.eqb (S i) e) with false in HPl by (symmetry; apply Nat.eqb_neq; lia).
        unfold mz, pxor, pshl in HPl. cbn in HPl.
        replace (i - 0) with i in HPl by lia. rewrite IH in HPl by lia.
        destruct (QB (S i)); [reflexivity|discriminate]. }
    split; [exact Hlow|].
    specialize (HPl (e) ltac:(lia)). unfold mz, pxor, pshl in HPl.
    destruct e as [|e']; [lia|]. cbn in HPl. replace (e' - 0) with e' in HPl by lia.
    rewrite (Hlow e') in HPl by lia. rewrite Nat.eqb_refl in HPl.
    destruct (QB (S e')); [discriminate|reflexivity].
  - (* even: mz (mz QB) *)
    specialize (Heven eq_refl). rename Heven into He2.
    assert (Hmm: forall i, mz (mz QB) i = xorb (QB i) (if Nat.leb 2 i then QB (i-2) else false)).
    { intro i. unfold mz, pxor, pshl. destruct i as [|[|i]]; cbn; [rewrite !xorb_false_r; reflexivity| |].
      - destruct (QB 0), (QB 1); reflexivity.
      - replace (i - 0) with i by lia. destruct (QB i), (QB (S i)), (QB (S (S i))); reflexivity. }
    assert (Hlow: forall i, i < e -> QB i = true).
    { intro i. induction i as [i IH] using lt_wf_ind. intro Hi.
      specialize (HPl i ltac:(lia)). rewrite Hmm in HPl.
      destruct (Nat.eqb_spec i (e)); [lia|]. rewrite xorb_false_r in HPl.
      destruct i as [|[|i]].
      - cbn in HPl. rewrite xorb_false_r in HPl. exact HPl.
      - cbn in HPl. rewrite xorb_false_r in HPl. exact HPl.
      - cbn in HPl. replace (i - 0) with i in HPl by lia. rewrite (IH i) in HPl by lia.
        destruct (QB (S (S i))); [reflexivity|discriminate]. }
    split; [exact Hlow|].
    specialize (HPl e ltac:(lia)). rewrite Hmm, Nat.eqb_refl in HPl.
    replace (Nat.leb 2 e) with true in HPl by (symmetry; apply Nat.leb_le; lia).
    rewrite (Hlow (e-2)) in HPl by lia.
    replace (den [0;1] e) with false in HPl by (rewrite den2; destruct (Nat.eqb_spec e 0), (Nat.eqb_spec e 1); try lia; reflexivity).
    destruct (QB e); [discriminate|reflexivity].
Qed.

(* ---- FIB1Dyn ---- *)
(** Dynamics of the tail system: iteration, invariants, lift iteration, leading zeros. *)

Definition T1 : list (list bool) := [[false;false;true;false]].

Fixpoint Gn (n:nat) (W:list (list bool)) : option (list (list bool)) :=
  match n with O => Some W | S n' => match Gs W with Some W' => Gn n' W' | None => None end end.

Definition Tn (n:nat) := Gn (n-1) T1.

Lemma Gn_add a : forall b W, Gn (a+b) W = match Gn a W with Some W' => Gn b W' | None => None end.
Proof.
  induction a; intros b W; cbn; [reflexivity|].
  destruct (Gs W); [apply IHa|reflexivity].
Qed.

Lemma Gn_S n W : Gn (S n) W = match Gn n W with Some W' => Gs W' | None => None end.
Proof.
  replace (S n) with (n + 1) by lia. rewrite Gn_add.
  destruct (Gn n W); [|reflexivity]. cbn. destruct (Gs l); reflexivity.
Qed.

Lemma Tn_S n : 1 <= n -> Tn (S n) = match Tn n with Some W => Gs W | None => None end.
Proof. intro H. unfold Tn. replace (S n - 1) with (S (n-1)) by lia. apply Gn_S. Qed.

Lemma Tn_add n j : 1 <= n -> Tn (n + j) = match Tn n with Some W => Gn j W | None => None end.
Proof. intro H. unfold Tn. replace (n + j - 1) with ((n-1) + j) by lia. apply Gn_add. Qed.

Lemma Fn_S' r Y : Fn (S r) Y = Fn r (F Y).
Proof. induction r; cbn in *; [reflexivity|]. rewrite <- IHr. reflexivity. Qed.

Lemma Fn_length r Y : length (Fn r Y) = length Y.
Proof. induction r; cbn; [reflexivity|]. rewrite F_length. exact IHr. Qed.

Definition fstlen (W:list (list bool)) : nat := match W with H::_ => length H | [] => 0 end.

Lemma lift_iter c j : forall Y W, length Y = c + 2 ->
  (forall r, r < j -> parity (Fn r Y) = false) ->
  (forall r, r < j -> exists W', Gn r W = Some W' /\ 4 <= fstlen W') ->
  Gn j (liftW c Y W) = option_map (liftW c (Fn j Y)) (Gn j W).
Proof.
  induction j as [|j IH]; intros Y W HL HP HW; [reflexivity|].
  destruct (HW 0 ltac:(lia)) as [W0 [E0' H0]]. cbn in E0'. inversion E0'; subst W0.
  cbn [Gn]. rewrite lift_step.
  2: exact HL. 2: exact (HP 0 ltac:(lia)). 2: { destruct W; cbn in H0 |- *; [lia|lia]. }
  destruct (Gs W) as [W1|] eqn:EG; cbn [option_map]; [|reflexivity].
  rewrite Fn_S'. apply IH.
  - rewrite F_length. exact HL.
  - intros r Hr. rewrite <- Fn_S'. apply HP. lia.
  - intros r Hr. destruct (HW (S r) ltac:(lia)) as [W' [E' H']]. cbn in E'. rewrite EG in E'. eauto.
Qed.

(** ===== invariants: total length, last segment ends 1,0 ===== *)
Fixpoint total (W:list (list bool)) : nat :=
  match W with [] => 0 | [s] => length s | s::W' => length s + 1 + total W' end.

Lemma total_cons s W : W <> [] -> total (s :: W) = length s + 1 + total W.
Proof. destruct W; [congruence|reflexivity]. Qed.

Definition endsTF (W:list (list bool)) : Prop := exists p, last W [] = p ++ [true;false].

Lemma Gs_nonempty W W' : Gs W = Some W' -> W' <> [].
Proof.
  destruct W as [|s [|s' W]]; intro HG; [discriminate| |].
  - cbn in HG. destruct (parity s); [inversion HG; discriminate|].
    destruct (beql _ _); [inversion HG; discriminate|discriminate].
  - rewrite Gs_cons2 in HG. destruct (parity s).
    + destruct (Gs (s' :: W)); cbn in HG; [inversion HG; discriminate|discriminate].
    + destruct W; [inversion HG; discriminate|discriminate].
Qed.

Lemma beql_len u v : beql u v = true -> length u = length v.
Proof. intro H. apply beql_spec in H. subst. reflexivity. Qed.

Lemma Gs_total W W' : Gs W = Some W' -> total W' = total W + 3.
Proof.
  revert W'; induction W as [|s W IH]; intros W' HG; [discriminate|].
  destruct W as [|s' W].
  - cbn [Gs] in HG. destruct (parity s).
    + inversion HG; subst. cbn [total length]. rewrite ?app_length, ?pxl_length, ?G1_length. cbn [length]. lia.
    + destruct (beql _ _) eqn:Eb; [|discriminate]. inversion HG; subst. cbn [total].
      apply beql_len in Eb. rewrite skipn_length in Eb. cbn [length] in Eb. rewrite ?pxl_length, ?G1_length in Eb.
      cbn [total length]. rewrite ?firstn_length. cbn [length]. rewrite ?pxl_length, ?G1_length. lia.
  - rewrite Gs_cons2 in HG. destruct (parity s).
    + destruct (Gs (s' :: W)) as [W1|] eqn:E1; cbn in HG; [|discriminate]. inversion HG; subst.
      pose proof (Gs_nonempty _ _ E1) as Hne.
      rewrite total_cons by exact Hne. rewrite total_cons by discriminate.
      rewrite (IH W1 eq_refl), F_length. lia.
    + destruct W; [|discriminate]. inversion HG; subst. cbn [total length]. rewrite ?app_length, ?pxl_length, ?G1_length, ?repeat_length. cbn [length]. lia.
Qed.

Lemma Tn_total n : forall W, 1 <= n -> Tn n = Some W -> total W = 3 * n + 1.
Proof.
  induction n as [|n IH]; intros W Hn HT; [lia|].
  destruct n as [|n].
  - cbn in HT. inversion HT. reflexivity.
  - rewrite Tn_S in HT by lia. destruct (Tn (S n)) as [W0|] eqn:E0; [|discriminate].
    rewrite (Gs_total _ _ HT), (IH W0 ltac:(lia) eq_refl). lia.
Qed.

Lemma single_len n s : 1 <= n -> Tn n = Some [s] -> length s = 3 * n + 1.
Proof. intros Hn HT. apply (Tn_total n [s] Hn HT). Qed.

Lemma Gs_ends W W' : Gs W = Some W' -> exists p, last W' [] = p ++ [true;false].
Proof.
  revert W'; induction W as [|s W IH]; intros W' HG; [discriminate|].
  destruct W as [|s' W].
  - cbn [Gs] in HG. destruct (parity s).
    + inversion HG; subst. exists (G1 s). reflexivity.
    + destruct (beql _ _); [|discriminate]. inversion HG; subst. cbn. exists [false;false]. reflexivity.
  - rewrite Gs_cons2 in HG. destruct (parity s).
    + destruct (Gs (s' :: W)) as [W1|] eqn:E1; cbn in HG; [|discriminate]. inversion HG; subst.
      destruct (IH W1 eq_refl) as [p Hp]. exists p. pose proof (Gs_nonempty _ _ E1).
      destruct W1; [congruence|]. cbn [last] in *. exact Hp.
    + destruct W; [|discriminate]. inversion HG; subst. cbn [last].
      exists (G1 s ++ repeat true (length s') ++ [true]). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma Tn_ends n W : 1 <= n -> Tn n = Some W -> exists p, last W [] = p ++ [true;false].
Proof.
  intros Hn HT. destruct n as [|n]; [lia|]. destruct n as [|n].
  - cbn in HT. inversion HT; subst. exists [false;false]. reflexivity.
  - rewrite Tn_S in HT by lia. destruct (Tn (S n)); [|discriminate]. eapply Gs_ends; eauto.
Qed.

(** ===== nth characterizations ===== *)
Lemma nth_pxl_c Y : forall i c, i < length Y -> nth i (pxl c Y) false = xorb c (parity (firstn (S i) Y)).
Proof.
  induction Y as [|a Y IH]; intros i c Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn [pxl nth firstn parity].
  - rewrite xorb_false_r. reflexivity.
  - rewrite IH by lia. cbn [parity firstn]. rewrite xorb_assoc. reflexivity.
Qed.

Lemma nth_firstn {T} (l:list T) i n d : nth i (firstn n l) d = if Nat.ltb i n then nth i l d else d.
Proof.
  revert i n; induction l as [|a l IH]; intros i n.
  - rewrite firstn_nil. destruct i, (Nat.ltb _ n); reflexivity.
  - destruct n, i; cbn [firstn nth]; try reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma nth_G1 i Y : i <= length Y -> nth i (G1 Y) false = parity (firstn i Y).
Proof.
  intro Hi. destruct i as [|i]; [reflexivity|]. unfold G1. cbn [nth].
  rewrite nth_pxl_c by lia. reflexivity.
Qed.

Lemma nth_F i Y : i < length Y -> nth i (F Y) false = parity (firstn i Y).
Proof.
  intro Hi. rewrite F_as_G1. rewrite nth_firstn. destruct (Nat.ltb_spec i (length Y)); [|lia].
  apply nth_G1. lia.
Qed.

Lemma parity_firstn_S i Y : i < length Y -> parity (firstn (S i) Y) = xorb (parity (firstn i Y)) (nth i Y false).
Proof.
  revert i; induction Y as [|a Y IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i].
  - cbn. destruct a; reflexivity.
  - change (parity (firstn (S (S i)) (a :: Y))) with (xorb a (parity (firstn (S i) Y))).
    change (parity (firstn (S i) (a :: Y))) with (xorb a (parity (firstn i Y))).
    change (nth (S i) (a :: Y) false) with (nth i Y false).
    rewrite IH by lia. rewrite xorb_assoc. reflexivity.
Qed.

(** leading-zero profile: n+1 zeros, then a 1, total length at least n+3 *)
Definition ZP (n:nat) (H:list bool) : Prop :=
  (forall i, i <= n -> nth i H false = false) /\ nth (S n) H false = true /\ n + 3 <= length H.

Lemma parity_firstn_zeros n H : (forall i, i <= n -> nth i H false = false) -> forall i, i <= S n -> i <= length H -> parity (firstn i H) = false.
Proof.
  intros HZ i Hi HL. induction i as [|i IH]; [reflexivity|].
  rewrite parity_firstn_S by lia. rewrite IH by lia. rewrite HZ by lia. reflexivity.
Qed.

Lemma ZP_F n H : ZP n H -> n + 4 <= length H -> ZP (S n) (F H).
Proof.
  intros [HZ [H1 HL]] HL'. split; [|split].
  - intros i Hi. rewrite nth_F by lia. apply (parity_firstn_zeros n H HZ); lia.
  - rewrite nth_F by lia. rewrite parity_firstn_S by lia. rewrite (parity_firstn_zeros n H HZ) by lia. rewrite H1. reflexivity.
  - rewrite F_length. lia.
Qed.

Lemma ZP_G1 n H w : ZP n H -> ZP (S n) (G1 H ++ w).
Proof.
  intros [HZ [H1 HL]]. assert (HG: length (G1 H) = S (length H)) by apply G1_length. split; [|split].
  - intros i Hi. rewrite app_nth1 by lia. rewrite nth_G1 by lia. apply (parity_firstn_zeros n H HZ); lia.
  - rewrite app_nth1 by lia. rewrite nth_G1 by lia. rewrite parity_firstn_S by lia.
    rewrite (parity_firstn_zeros n H HZ) by lia. rewrite H1. reflexivity.
  - rewrite app_length. lia.
Qed.

Lemma ZP_split n H : ZP n H -> n + 6 <= length H -> ZP (S n) (firstn (length H - 2) (G1 H)).
Proof.
  intros HZP HL. pose proof (ZP_G1 n H [] HZP) as [HZ [H1 HL1]]. rewrite app_nil_r in *.
  split; [|split].
  - intros i Hi. rewrite nth_firstn. destruct (Nat.ltb_spec i (length H - 2)); [apply HZ; lia|reflexivity].
  - rewrite nth_firstn. destruct (Nat.ltb_spec (S (S n)) (length H - 2)); [exact H1|lia].
  - rewrite firstn_length, G1_length. lia.
Qed.

Lemma nth_LS i c Y H : i < c -> length Y <= c + length H -> nth i (LS c Y H) false = nth i Y false.
Proof.
  intros Hi HL. unfold LS.
  assert (forall u v k, nth k (bx u v) false = xorb (nth k u false) (nth k v false)).
  { induction u as [|a u IHu]; intros [|b v] k; destruct k; cbn; rewrite ?xorb_false_r, ?xorb_false_l; auto.
    all: destruct v; cbn; auto. }
  rewrite H0. rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
Qed.

Lemma ZP_LS n c Y H : ZP n Y -> S n < c -> length Y <= c + length H -> n + 3 <= c + length H -> ZP n (LS c Y H).
Proof.
  intros [HZ [H1 HL]] Hc HL2 HL3. split; [|split].
  - intros i Hi. rewrite nth_LS by lia. apply HZ, Hi.
  - rewrite nth_LS by lia. exact H1.
  - rewrite LS_length by lia. lia.
Qed.

Lemma ZP_Fn n r Y : ZP n Y -> n + r + 3 <= length Y -> ZP (n + r) (Fn r Y).
Proof.
  revert n; induction r as [|r IH]; intros n HZ HL.
  - rewrite Nat.add_0_r. exact HZ.
  - cbn [Fn]. replace (n + S r) with (S (n + r)) by lia. apply ZP_F.
    + apply IH; [exact HZ|lia].
    + rewrite Fn_length. lia.
Qed.

(* ---- FIB1Epoch ---- *)
(** The epoch induction (PROOF.md section 4). *)

Definition Tseg1 : list bool := [false;false;true;false].

Definition Good (n:nat) : Prop :=
  exists W, Tn n = Some W /\ ZP n (hd [] W) /\
   ((exists s, W = [s]) \/
    (exists H m Wm, W = H :: Wm /\ 1 <= m < n /\ Tn m = Some Wm /\
        (parity H = false -> exists j, 1 <= j /\ m = JJ j))).

Definition Epoch (k:nat) : Prop :=
  (forall n, 1 <= n <= 2^k -> Good n) /\
  (exists Y, Tn (2^k+1) = Some [Y ++ [true;false]] /\ length Y = 3 * 2^k + 2 /\ Q Y == den (QYl k) /\ ZP (2^k+1) Y) /\
  (forall m, 2 <= m <= k -> exists B, Tn (bb m) = Some [B; Tseg1] /\ length B = 3 * bb m - 4 /\
                                   mzn (eps m) (Q B) == den (Pl m)) /\
  (forall m, 1 <= m -> JJ m + 1 <= 2^k + 1 -> (exists s, Tn (JJ m) = Some [s]) /\ (exists s, Tn (JJ m + 1) = Some [s])).

(** ===== helpers ===== *)
Lemma Gs_alive a W : parity a = true -> W <> [] -> Gs (a :: W) = option_map (cons (F a)) (Gs W).
Proof. intros Hp HW. destruct W as [|b RR]; [congruence|]. rewrite Gs_cons2, Hp. reflexivity. Qed.

Lemma LS_T1 c Y : length Y = c + 2 -> LS c Y Tseg1 = Y ++ [true;false].
Proof.
  intro HL. unfold LS, Tseg1.
  replace (repeat false c ++ [false;false;true;false]) with ((repeat false (c+2)) ++ [true;false]).
  2:{ rewrite repeat_app, <- app_assoc. reflexivity. }
  rewrite bx_app_l by (rewrite repeat_length; lia).
  f_equal. revert Y HL. generalize (c+2). intros n Y HL. subst n.
  induction Y as [|y Y IH]; [reflexivity|]. cbn. rewrite IH by reflexivity. destruct y; reflexivity.
Qed.

Lemma Q_LS c Y B : length Y = c + 2 -> 2 <= length B ->
  Q (LS c Y B) == pxor (Q B) (mzn (length B - 2) (Q Y)).
Proof.
  intros HL HB. unfold LS.
  rewrite <- (bx_pad (repeat false c ++ B) Y (length B - 2)) by (rewrite app_length, repeat_length; lia).
  rewrite Q_xor by (rewrite !app_length, !repeat_length; lia).
  rewrite Q_zeros_app, Q_app_zeros. reflexivity.
Qed.

Lemma QY_low k r : 1 <= k -> r < 2^(k-1) - 1 -> den (QYl k) r = false.
Proof.
  intros Hk Hr. apply den_above. unfold QYl. rewrite Forall_forall. intros x Hx.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  rewrite !in_app_iff in Hx. destruct Hx as [[<-|[]]|[Hx|Hx]]; [lia| |];
  apply in_map_iff in Hx as [j [<- Hj]]; apply in_seq0 in Hj;
  assert (2^j <= 2^(k-1)) by (apply pow_mono; lia); lia.
Qed.

Lemma Q_deg l i : length l <= i -> Q l i = false.
Proof.
  revert i. induction l as [|a l IH] using rev_ind; intros i Hi.
  - reflexivity.
  - rewrite app_length in Hi. cbn [length] in Hi.
    rewrite (Q_app l [a] i). unfold pxor. cbn [length mzn]. rewrite (Q_single a i).
    unfold mz, pxor, pshl, pbit, pone, pzero.
    rewrite (IH i) by lia. destruct (Nat.leb_spec 1 i); [|lia]. rewrite (IH (i-1)) by lia.
    destruct a; cbn; [destruct (Nat.eqb_spec i 0); [lia|reflexivity]|reflexivity].
Qed.

Lemma Good_some n : Good n -> exists W, Tn n = Some W /\ n + 3 <= fstlen W.
Proof. intros [W [HT [[_ [_ HL]] _]]]. exists W. split; [exact HT|]. destruct W; cbn in *; lia. Qed.

Lemma Tn_1 : Tn 1 = Some T1.
Proof. reflexivity. Qed.

Lemma lift_phase k Y : 4 <= k -> (forall n, 1 <= n <= 2^k -> Good n) ->
  Tn (2^k+1) = Some [Y ++ [true;false]] -> length Y = 3*2^k+2 -> Q Y == den (QYl k) ->
  forall j, 1 <= j <= bb (k-1) -> Tn (2^k + j) = option_map (liftW (3*2^k) (Fn (j-1) Y)) (Tn j).
Proof.
  intros Hk HG HT HL HQ j Hj.
  pose proof (bb_lt (k-1) ltac:(lia)) as Hb.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  replace (2^k + j) with ((2^k+1) + (j-1)) by lia.
  rewrite Tn_add, HT by lia.
  replace [Y ++ [true;false]] with (liftW (3*2^k) Y T1).
  2:{ change (liftW (3*2^k) Y T1) with [LS (3*2^k) Y Tseg1]. rewrite LS_T1 by lia. reflexivity. }
  rewrite lift_iter.
  - unfold Tn. replace (j - 1) with (j - 1) by reflexivity. reflexivity.
  - lia.
  - intros r Hr. rewrite parity_Fn, (HQ r). apply QY_low; lia.
  - intros r Hr. destruct (Good_some (S r) (HG (S r) ltac:(lia))) as [W' [HW' HL']].
    exists W'. split; [|lia]. unfold Tn in HW'. replace (S r - 1) with r in HW' by lia. exact HW'.
Qed.

Lemma Good_lift k Y j : 4 <= k -> length Y = 3*2^k+2 -> ZP (2^k+1) Y -> Q Y == den (QYl k) ->
  1 <= j <= bb (k-1) -> Tn (2^k + j) = option_map (liftW (3*2^k) (Fn (j-1) Y)) (Tn j) ->
  Good j -> Good (2^k + j).
Proof.
  intros Hk HL HZY HQ Hj HT [W [HW [HZ Hc]]].
  pose proof (bb_lt (k-1) ltac:(lia)) as Hb.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  rewrite HW in HT. cbn [option_map] in HT.
  destruct W as [|H RR]; [destruct HZ as [_ [_ HZ]]; cbn in HZ; lia|].
  cbn [hd] in HZ. pose proof HZ as [_ [_ HLH]].
  assert (HYj: ZP (2^k + j) (Fn (j-1) Y)).
  { replace (2^k + j) with ((2^k + 1) + (j-1)) by lia. apply ZP_Fn; [exact HZY|lia]. }
  assert (HLj: length (Fn (j-1) Y) = 3*2^k+2) by (rewrite Fn_length; exact HL).
  assert (Hpar: parity (Fn (j-1) Y) = false) by (rewrite parity_Fn, (HQ (j-1)); apply QY_low; lia).
  exists (liftW (3*2^k) (Fn (j-1) Y) (H :: RR)). split; [exact HT|]. split.
  - cbn [liftW hd]. apply ZP_LS; [exact HYj|lia|lia|lia].
  - destruct Hc as [[s Hs]|[H' [m [Wm [HE [Hm [HTm Hd]]]]]]].
    + left. inversion Hs; subst. exists (LS (3*2^k) (Fn (j-1) Y) s). reflexivity.
    + right. inversion HE; subst. exists (LS (3*2^k) (Fn (j-1) Y) H'), m, Wm.
      split; [reflexivity|]. split; [lia|]. split; [exact HTm|].
      intro HP. apply Hd. rewrite LS_parity, Hpar, xorb_false_r in HP. exact HP.
Qed.

Lemma QYl_ge k : 1 <= k -> Forall (fun x => 2^(k-1) - 1 <= x) (QYl k).
Proof.
  intros Hk. unfold QYl. rewrite Forall_forall. intros x Hx.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  rewrite !in_app_iff in Hx. destruct Hx as [[<-|[]]|[Hx|Hx]]; [lia| |];
  apply in_map_iff in Hx as [j [<- Hj]]; apply in_seq0 in Hj;
  assert (2^j <= 2^(k-1)) by (apply pow_mono; lia); lia.
Qed.

Lemma birth k Y B : 4 <= k -> (forall n, 1 <= n <= 2^k -> Good n) ->
  Tn (2^k+1) = Some [Y ++ [true;false]] -> length Y = 3*2^k+2 -> Q Y == den (QYl k) ->
  Tn (bb (k-1)) = Some [B; Tseg1] -> length B = 3 * bb (k-1) - 4 -> mzn (eps (k-1)) (Q B) == den (Pl (k-1)) ->
  Tn (bb (S k)) = Some [LS (3*2^k) (Fn (bb (k-1) - 1) Y) B; Tseg1] /\
  length (LS (3*2^k) (Fn (bb (k-1) - 1) Y) B) = 3 * bb (S k) - 4 /\
  mzn (eps (S k)) (Q (LS (3*2^k) (Fn (bb (k-1) - 1) Y) B)) == den (Pl (S k)).
Proof.
  intros Hk HG HT HL HQ HTB HLB HPB.
  pose proof (bb_lt (k-1) ltac:(lia)) as Hb. pose proof (bb_ge (k-1) ltac:(lia)) as Hb4.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  assert (Hbb: bb (S k) = 2^k + bb (k-1)).
  { replace (S k) with (S (S (k-1))) by lia. rewrite bb_SS. replace (S (k-1)) with k by lia. reflexivity. }
  assert (HLY': length (Fn (bb (k-1) - 1) Y) = 3*2^k + 2) by (rewrite Fn_length; exact HL).
  split; [|split].
  - rewrite Hbb, (lift_phase k Y Hk HG HT HL HQ (bb (k-1)) ltac:(lia)), HTB. reflexivity.
  - rewrite LS_length by lia. lia.
  - rewrite Q_LS by lia. rewrite Q_Fn, HQ, mzn_xor.
    replace (eps (S k)) with (eps (k-1)) by (replace (S k) with (S (S (k-1))) by lia; rewrite eps_SS; reflexivity).
    rewrite HPB, <- mzn_add.
    replace (eps (k-1) + (length B - 2)) with (2^k).
    2:{ rewrite HLB. pose proof (bb_eps (k-1) ltac:(lia)). replace (S (k-1)) with k in H by lia. lia. }
    rewrite frob, <- den_shr.
    2:{ eapply Forall_impl; [|apply QYl_ge; lia]. intros x Hx; cbn in Hx. lia. }
    pose proof (birth_identity (k-1) ltac:(lia)) as HBI.
    replace (S (k-1)) with k in HBI by lia.
    exact HBI.
Qed.

Lemma JJ_le k : 1 <= k -> JJ (S k) <= 2^k.
Proof.
  intro Hk. pose proof (JJ_eps (S k)). pose proof (eps_range (S k)). pose proof (pow_ge1 k).
  destruct (Nat.eq_dec k 1) as [->|Hk1].
  - cbn. unfold JJ, ee. cbn. lia.
  - specialize (H ltac:(lia)). rewrite pow_S in H. lia.
Qed.

Lemma Good_nonempty n W : Good n -> Tn n = Some W -> W <> [].
Proof.
  intros [W' [HT [[_ [_ HL]] _]]] HW. rewrite HW in HT. inversion HT; subst. intro E; subst. cbn in HL. lia.
Qed.

Lemma life k B' : 4 <= k -> (forall n, 1 <= n <= 2^k -> Good n) ->
  Tn (bb (S k)) = Some [B'; Tseg1] -> mzn (eps (S k)) (Q B') == den (Pl (S k)) ->
  forall t, t <= ee (S k) -> exists Wt, Tn (1 + t) = Some Wt /\ Tn (bb (S k) + t) = Some (Fn t B' :: Wt).
Proof.
  intros Hk HG HT HP. pose proof (life_from_P (S k) (Q B') ltac:(lia) HP) as [Hlow _].
  pose proof (JJ_le k ltac:(lia)) as HJ. unfold JJ in HJ.
  induction t as [|t IH]; intro Ht.
  - exists T1. split; [reflexivity|]. rewrite Nat.add_0_r, HT. reflexivity.
  - destruct (IH ltac:(lia)) as [Wt [HWt HTt]].
    destruct (Good_some (2 + t) (HG (2+t) ltac:(lia))) as [Wt' [HWt' _]].
    exists Wt'. split; [exact HWt'|].
    replace (bb (S k) + S t) with (S (bb (S k) + t)) by lia.
    rewrite Tn_S by (pose proof (bb_ge (S k)); lia). rewrite HTt.
    rewrite Gs_alive.
    + replace (Gs Wt) with (Tn (2 + t)). { rewrite HWt'. reflexivity. }
      replace (2 + t) with (S (1 + t)) by lia. rewrite Tn_S by lia. rewrite HWt. reflexivity.
    + rewrite parity_Fn. apply Hlow. lia.
    + apply (Good_nonempty (1+t)); [apply HG; lia|exact HWt].
Qed.

Lemma bb_lower m : 2^(S m) + 4 <= 3 * bb m.
Proof. pose proof (bb_closed m). destruct (Nat.odd m); lia. Qed.

Lemma bbS_ee k : 1 <= k -> bb (S k) + ee (S k) = 2^(S k).
Proof. intro Hk. pose proof (bb_le (S k) ltac:(lia)). unfold ee. lia. Qed.

Lemma merge k B' : 4 <= k -> (forall n, 1 <= n <= 2^k -> Good n) ->
  (forall m, 1 <= m -> JJ m + 1 <= 2^k + 1 -> (exists s, Tn (JJ m) = Some [s]) /\ (exists s, Tn (JJ m + 1) = Some [s])) ->
  Tn (bb (S k)) = Some [B'; Tseg1] -> length B' = 3 * bb (S k) - 4 -> ZP (bb (S k)) B' ->
  mzn (eps (S k)) (Q B') == den (Pl (S k)) ->
  exists Y', Tn (2^(S k)+1) = Some [Y' ++ [true;false]] /\ length Y' = 3 * 2^(S k) + 2 /\
             Q Y' == den (QYl (S k)) /\ ZP (2^(S k)+1) Y'.
Proof.
  intros Hk HG HD HT HLB HZB HP.
  pose proof (life_from_P (S k) (Q B') ltac:(lia) HP) as [Hlow Hdead].
  pose proof (JJ_le k ltac:(lia)) as HJ.
  pose proof (bbS_ee k ltac:(lia)) as Hbe.
  pose proof (bb_closed (S k)) as Hc. pose proof (JJ_eps (S k) ltac:(lia)) as HJe. pose proof (eps_range (S k)) as Her.
  destruct (life k B' Hk HG HT HP (ee (S k)) ltac:(lia)) as [Wj [HWj HTd]].
  destruct (HD (S k) ltac:(lia) ltac:(lia)) as [[s Hs] _].
  replace (1 + ee (S k)) with (JJ (S k)) in HWj by (unfold JJ; lia).
  rewrite Hs in HWj. inversion HWj; subst Wj. clear HWj.
  pose proof (single_len (JJ (S k)) s ltac:(unfold JJ; lia) Hs) as Hls.
  set (H := Fn (ee (S k)) B') in *.
  assert (HpH: parity H = false) by (unfold H; rewrite parity_Fn; exact Hdead).
  exists (G1 H ++ repeat true (3 * JJ (S k) + 2)).
  split; [|split; [|split]].
  - replace (2^(S k) + 1) with (S (bb (S k) + ee (S k))) by lia.
    rewrite Tn_S by lia. rewrite HTd, Gs_cons2, HpH. f_equal. f_equal.
    rewrite Hls. rewrite <- !app_assoc. f_equal.
    replace (3 * JJ (S k) + 2) with (S (3 * JJ (S k) + 1)) by lia. rewrite repeat_snoc, <- app_assoc. reflexivity.
  - rewrite app_length, G1_length, repeat_length. unfold H. rewrite Fn_length, HLB.
    unfold JJ in *. pose proof (bb_ge (S k) ltac:(lia)). rewrite pow_S in *. lia.
  - rewrite Q_app, G1_last, HpH, Q_app, Q_single. cbn [length mzn]. unfold H at 1. rewrite Q_F.
    replace (pbit false) with pzero by reflexivity. rewrite pxor_zero_r, repeat_length.
    apply merge_identity; [lia| |].
    + rewrite Q_0. exact HpH.
    + unfold H. rewrite Q_Fn. apply X_formula; [lia|exact HP|exact Hlow].
  - replace (2^(S k) + 1) with (S (bb (S k) + ee (S k))) by lia.
    apply ZP_G1. unfold H. apply ZP_Fn; [exact HZB|].
    rewrite HLB. unfold ee. pose proof (bb_lower (S k)). pose proof (bb_le (S k) ltac:(lia)).
    pose proof (pow_S (S k)). pose proof (pow_ge1 (S k)). lia.
Qed.

Lemma JJ_formula m : 2 <= m -> 3 * JJ m = 2^m + eps m - 3.
Proof. intro H. pose proof (JJ_eps m H). lia. Qed.

Lemma JJ_small m k : m <= S k -> 1 <= k -> JJ m <= 2^k.
Proof.
  intros Hm Hk. destruct (Nat.le_gt_cases m 1) as [H1|H1].
  - destruct m as [|[|]]; [| |lia]; unfold JJ, ee; cbn; pose proof (pow_ge1 k); lia.
  - pose proof (JJ_formula m ltac:(lia)). pose proof (eps_range m). pose proof (pow_mono m (S k) Hm).
    rewrite pow_S in H2. lia.
Qed.

Lemma JJ_big m k : 1 <= k -> S (S (S k)) <= m -> 2^(S k) < JJ m.
Proof.
  intros Hk Hm. pose proof (JJ_formula m ltac:(lia)). pose proof (eps_range m). pose proof (pow_mono _ _ Hm).
  rewrite !pow_S in H1. assert (2 <= 2^k) by (pose proof (pow_mono 1 k Hk); cbn in H2; lia). rewrite pow_S. lia.
Qed.

Lemma JJ_SS k : 2 <= k -> JJ (S (S k)) = 2^k + JJ k.
Proof.
  intro Hk. pose proof (JJ_formula k Hk). pose proof (JJ_formula (S (S k)) ltac:(lia)).
  rewrite eps_SS, !pow_S in H0. pose proof (eps_range k). lia.
Qed.

Lemma Epoch_step k : 4 <= k -> Epoch k -> Epoch (S k).
Proof.
  intros Hk [HA [[Y [HT [HL [HQ HZY]]]] [HC HD]]].
  pose proof (bb_lt (k-1) ltac:(lia)) as Hb. pose proof (bb_ge (k-1) ltac:(lia)) as Hb4.
  assert (HK: 2^k = 2 * 2^(k-1)) by (replace k with (S (k-1)) at 1 by lia; reflexivity).
  assert (HK2: 2^(S k) = 2 * 2^k) by reflexivity.
  assert (Hbb: bb (S k) = 2^k + bb (k-1)).
  { replace (S k) with (S (S (k-1))) by lia. rewrite bb_SS. replace (S (k-1)) with k by lia. reflexivity. }
  pose proof (lift_phase k Y Hk HA HT HL HQ) as Hlift.
  assert (HGL: forall j, 1 <= j <= bb (k-1) -> Good (2^k + j)).
  { intros j Hj. apply (Good_lift k Y j Hk HL HZY HQ Hj (Hlift j Hj)). apply HA. lia. }
  destruct (HC (k-1) ltac:(lia)) as [B [HTB [HLB HPB]]].
  destruct (birth k Y B Hk HA HT HL HQ HTB HLB HPB) as [HTB' [HLB' HPB']].
  set (B' := LS (3*2^k) (Fn (bb (k-1) - 1) Y) B) in *.
  assert (HZB': ZP (bb (S k)) B').
  { destruct (HGL (bb (k-1)) ltac:(lia)) as [W [HW [HZ _]]]. rewrite <- Hbb, HTB' in HW.
    inversion HW; subst W. rewrite Hbb. exact HZ. }
  pose proof (life_from_P (S k) (Q B') ltac:(lia) HPB') as [Hlow Hdead].
  pose proof (bbS_ee k ltac:(lia)) as Hbe.
  split; [|split; [|split]].
  - (* (A) *)
    intros n Hn.
    destruct (Nat.le_gt_cases n (2^k)) as [H1|H1]; [apply HA; lia|].
    destruct (Nat.le_gt_cases n (2^k + bb (k-1))) as [H2|H2].
    + replace n with (2^k + (n - 2^k)) by lia. apply HGL. lia.
    + set (t := n - bb (S k)).
      assert (Ht: t <= ee (S k)) by (unfold t; lia).
      destruct (life k B' Hk HA HTB' HPB' t Ht) as [Wt [HWt HTt]].
      exists (Fn t B' :: Wt). replace n with (bb (S k) + t) by (unfold t; lia).
      split; [exact HTt|]. split.
      * cbn [hd]. apply ZP_Fn; [exact HZB'|]. rewrite HLB'.
        pose proof (bb_lower (S k)). pose proof (bb_le (S k) ltac:(lia)). unfold ee in Ht. rewrite pow_S in *. lia.
      * right. exists (Fn t B'), (1 + t), Wt. split; [reflexivity|]. split; [pose proof (bb_ge (S k)); lia|].
        split; [exact HWt|].
        intro HP. exists (S k). split; [lia|].
        destruct (Nat.lt_ge_cases t (ee (S k))) as [Hlt|Hge].
        -- rewrite parity_Fn, Hlow in HP by exact Hlt. discriminate.
        -- unfold JJ. lia.
  - (* (B) *)
    apply (merge k B' Hk HA HD HTB' HLB' HZB' HPB').
  - (* (C) *)
    intros m Hm. destruct (Nat.eq_dec m (S k)) as [->|Hne].
    + exists B'. auto.
    + apply HC. lia.
  - (* (D) *)
    intros m Hm HJm.
    destruct (Nat.le_gt_cases (JJ m + 1) (2^k + 1)) as [Hold|Hnew]; [apply HD; auto|].
    assert (Hm2: m = S (S k)).
    { destruct (Nat.le_gt_cases m (S k)) as [Hle|Hgt].
      - pose proof (JJ_small m k Hle ltac:(lia)). lia.
      - destruct (Nat.eq_dec m (S (S k))) as [E|Hne]; [exact E|].
        pose proof (JJ_big m k ltac:(lia) ltac:(lia)). lia. }
    subst m. rewrite JJ_SS by lia.
    destruct (HD k ltac:(lia) ltac:(pose proof (JJ_small k k ltac:(lia) ltac:(lia)); lia)) as [[s1 Hs1] [s2 Hs2]].
    assert (HJk: JJ k + 1 <= bb (k-1)).
    { pose proof (JJ_formula k ltac:(lia)). pose proof (eps_range k). pose proof (bb_lower (k-1)).
      replace (S (k-1)) with k in H1 by lia. lia. }
    assert (1 <= JJ k) by (unfold JJ; lia).
    split.
    + rewrite (Hlift (JJ k) ltac:(lia)), Hs1. cbn. eexists. reflexivity.
    + rewrite <- Nat.add_assoc, (Hlift (JJ k + 1) ltac:(lia)), Hs2. cbn. eexists. reflexivity.
Qed.

(* ---- FIB1Base ---- *)
(** Base case Epoch 4 by computation, and the tail theorem. *)

Definition ZPb (n:nat) (H:list bool) : bool :=
  forallb (fun i => negb (nth i H false)) (seq 0 (S n)) && nth (S n) H false && Nat.leb (n+3) (length H).

Lemma ZPb_spec n H : ZPb n H = true -> ZP n H.
Proof.
  unfold ZPb. intro E. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
  rewrite forallb_forall in E1. split; [|split].
  - intros i Hi. specialize (E1 i ltac:(apply in_seq; lia)). destruct (nth i H false); [discriminate|reflexivity].
  - exact E2.
  - apply Nat.leb_le, E3.
Qed.

Definition lleq (u v : list (list bool)) : bool := if list_eq_dec (list_eq_dec bool_dec) u v then true else false.

Definition goodb (n:nat) : bool :=
  match Tn n with
  | None => false
  | Some W =>
      ZPb n (hd [] W) &&
      match W with
      | [_] => true
      | H :: Wm =>
          existsb (fun m => match Tn m with
                            | Some Wm' => lleq Wm Wm' && (parity H || existsb (fun j => Nat.eqb m (JJ j)) (seq 1 8))
                            | None => false end) (seq 1 (n-1))
      | [] => false
      end
  end.

Lemma goodb_spec n : goodb n = true -> Good n.
Proof.
  unfold goodb. destruct (Tn n) as [W|] eqn:HT; [|discriminate].
  intro E. apply andb_true_iff in E as [EZ E]. exists W. split; [exact HT|]. split; [apply ZPb_spec, EZ|].
  destruct W as [|H [|s Wm]]; [discriminate E|left; eexists; reflexivity|].
  right. apply existsb_exists in E as [m [Hm E]]. apply in_seq in Hm.
  destruct (Tn m) as [Wm'|] eqn:HTm; [|discriminate].
  apply andb_true_iff in E as [EL EP]. unfold lleq in EL.
  destruct (list_eq_dec _ (s :: Wm) Wm') as [EW|]; [|discriminate]. subst Wm'.
  exists H, m, (s :: Wm). split; [reflexivity|]. split; [lia|]. split; [exact HTm|].
  intro HP. rewrite HP, orb_false_l in EP. apply existsb_exists in EP as [j [Hj Ej]].
  apply in_seq in Hj. apply Nat.eqb_eq in Ej. exists j. split; [lia|exact Ej].
Qed.

Lemma base_A : forall n, 1 <= n <= 2^4 -> Good n.
Proof.
  intros n Hn. apply goodb_spec.
  assert (Hall: forallb goodb (seq 1 16) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. apply Hall, in_seq. cbn in Hn. lia.
Qed.

Lemma den_below i LL : Forall (fun x => x < i) LL -> den LL i = false.
Proof.
  induction 1 as [|x LL Hx HL IH]; cbn; [reflexivity|]. unfold pxor. rewrite IH.
  destruct (Nat.eqb_spec i x); [lia|reflexivity].
Qed.

Lemma Q_check l LL N : length l <= N -> forallb (fun x => Nat.ltb x N) LL = true ->
  forallb (fun i => Bool.eqb (parity (Fn i l)) (den LL i)) (seq 0 N) = true -> Q l == den LL.
Proof.
  intros HN HL HC i. destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
  - rewrite forallb_forall in HC. specialize (HC i ltac:(apply in_seq; lia)).
    apply Bool.eqb_prop in HC. rewrite <- parity_Fn. exact HC.
  - rewrite Q_deg by lia. symmetry. apply den_below. rewrite Forall_forall. intros x Hx.
    rewrite forallb_forall in HL. specialize (HL x Hx). apply Nat.ltb_lt in HL. lia.
Qed.

Definition Y4 : list bool := match Tn 17 with Some [U] => firstn 50 U | _ => [] end.

Lemma base_B : exists Y, Tn (2^4+1) = Some [Y ++ [true;false]] /\ length Y = 3 * 2^4 + 2 /\
                         Q Y == den (QYl 4) /\ ZP (2^4+1) Y.
Proof.
  exists Y4. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split.
  - apply (Q_check Y4 (QYl 4) 50); vm_compute; reflexivity.
  - apply ZPb_spec. vm_compute. reflexivity.
Qed.

(** P check: (1+z)^e Q B for e in {1,2} *)
Definition mznQ (e:nat) (B:list bool) (i:nat) : bool :=
  xorb (parity (Fn i B)) (if Nat.leb e i then parity (Fn (i-e) B) else false).

Lemma mzn12 e q i : e = 1 \/ e = 2 -> mzn e q i = xorb (q i) (if Nat.leb e i then q (i-e) else false).
Proof.
  intros [->| ->].
  - reflexivity.
  - pose proof (frob 1 q i) as H. change (2^1) with 2 in H. rewrite H. reflexivity.
Qed.

Lemma P_check B e LL N : (e = 1 \/ e = 2) -> length B + e <= N -> forallb (fun x => Nat.ltb x N) LL = true ->
  forallb (fun i => Bool.eqb (mznQ e B i) (den LL i)) (seq 0 N) = true -> mzn e (Q B) == den LL.
Proof.
  intros He HN HL HC i. rewrite mzn12 by exact He. destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
  - rewrite forallb_forall in HC. specialize (HC i ltac:(apply in_seq; lia)).
    apply Bool.eqb_prop in HC. unfold mznQ in HC. rewrite !parity_Fn in HC. exact HC.
  - rewrite Q_deg by lia. destruct (Nat.leb e i); [rewrite Q_deg by lia|]; cbn;
    symmetry; apply den_below; rewrite Forall_forall; intros x Hx;
    rewrite forallb_forall in HL; specialize (HL x Hx); apply Nat.ltb_lt in HL; lia.
Qed.

Definition Bm (m:nat) : list bool := match Tn (bb m) with Some [B0; _] => B0 | _ => [] end.

Lemma base_C : forall m, 2 <= m <= 4 -> exists B, Tn (bb m) = Some [B; Tseg1] /\ length B = 3 * bb m - 4 /\
                                   mzn (eps m) (Q B) == den (Pl m).
Proof.
  intros m Hm. exists (Bm m).
  assert (Hm3: m = 2 \/ m = 3 \/ m = 4) by lia.
  destruct Hm3 as [->|[->| ->]]; (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (apply (P_check _ _ _ 40); [vm_compute; auto| vm_compute; lia | vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.

Lemma base_D : forall m, 1 <= m -> JJ m + 1 <= 2^4 + 1 -> (exists s, Tn (JJ m) = Some [s]) /\ (exists s, Tn (JJ m + 1) = Some [s]).
Proof.
  intros m Hm HJ.
  assert (m <= 5).
  { destruct (Nat.le_gt_cases m 5) as [H|H]; [exact H|]. pose proof (JJ_big m 3 ltac:(lia) ltac:(lia)). cbn in *. lia. }
  assert (Hm5: m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5) by lia.
  destruct Hm5 as [->|[->|[->|[->| ->]]]]; split; vm_compute; eexists; reflexivity.
Qed.

Theorem Epoch4 : Epoch 4.
Proof. split; [exact base_A|split; [exact base_B|split; [exact base_C|exact base_D]]]. Qed.

Theorem Epoch_all k : 4 <= k -> Epoch k.
Proof.
  intro Hk. induction k as [|k IH]; [lia|].
  destruct (Nat.eq_dec k 3) as [->|Hne]; [exact Epoch4|].
  apply Epoch_step; [lia|]. apply IH. lia.
Qed.

Theorem tail_good n : 1 <= n -> Good n.
Proof.
  intro Hn. destruct (Epoch_all (n + 4) ltac:(lia)) as [HA _]. apply HA. split; [exact Hn|].
  assert (n < 2^n) by (apply Nat.pow_gt_lin_r; lia). assert (2^n <= 2^(n+4)) by (apply pow_mono; lia). lia.
Qed.

Theorem tail_never_halts n : 1 <= n -> Tn n <> None.
Proof. intros Hn E. destruct (tail_good n Hn) as [W [HW _]]. congruence. Qed.


End Tail.
Import Tail.

(** ************************** Part 3: doubling, and the final theorem ************************** *)

(** The real token system is the doubled tail system (PROOF.md section 5), and the final theorem. *)
Open Scope list_scope.
Open Scope nat_scope.

Definition b2t (b:bool) : tok := if b then tx else ty.
Definition toks1 (s:list bool) : list tok := map b2t s.
Fixpoint toks (W:list (list bool)) : list tok :=
  match W with [] => [] | [s] => toks1 s | s :: W' => toks1 s ++ tD :: toks W' end.
Fixpoint dbl (s:list bool) : list bool := match s with [] => [] | a::s' => a :: a :: dbl s' end.
Fixpoint ilv (s:list bool) : list bool := match s with [] => [] | a::s' => a :: false :: ilv s' end.

Definition b2i (b:bool) : item := if b then PX else PY.
Definition its_of (outs:list bool) : list item := rev (map b2i outs).

Lemma render_app' a b : render (a ++ b) = render b ++ render a.
Proof. induction a as [|i a IH]; cbn; [rewrite app_nil_r; reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma render_its_of outs : render (its_of outs) = toks1 outs.
Proof.
  induction outs as [|b outs IH]; [reflexivity|]. unfold its_of in *. cbn [map rev].
  rewrite render_app', IH. cbn. destruct b; reflexivity.
Qed.

Lemma rsweep_bits bits : forall its c rest,
  rsweep its c (toks1 bits ++ rest) = rsweep (its_of (pxl c bits) ++ its) (xorb c (parity bits)) rest.
Proof.
  induction bits as [|b bits IH]; intros its c rest.
  - cbn. rewrite xorb_false_r. reflexivity.
  - destruct b; cbn [toks1 map app b2t rsweep]; fold (toks1 bits); rewrite IH;
      unfold its_of; cbn [pxl map rev parity]; rewrite <- app_assoc; cbn [app];
      destruct c, (parity bits); reflexivity.
Qed.

Lemma toks_cons s W : W <> [] -> toks (s :: W) = toks1 s ++ tD :: toks W.
Proof. destruct W; [congruence|reflexivity]. Qed.

Lemma noD_toks1 s : existsb isD (toks1 s) = false.
Proof. induction s as [|b s IH]; [reflexivity|]. destruct b; exact IH. Qed.

Lemma toks1_length s : length (toks1 s) = length s.
Proof. apply map_length. Qed.

Lemma pxl_last_parity c s : s <> [] -> last (pxl c s) false = xorb c (parity s).
Proof.
  revert c; induction s as [|a s IH]; intros c Hs; [congruence|].
  destruct s as [|b s'].
  - cbn. rewrite xorb_false_r. reflexivity.
  - change (last (pxl c (a :: b :: s')) false) with (last (pxl (xorb c a) (b :: s')) false).
    rewrite (IH (xorb c a)) by discriminate. cbn [parity]. rewrite xorb_assoc. reflexivity.
Qed.

Lemma toks1_app u v : toks1 (u ++ v) = toks1 u ++ toks1 v.
Proof. apply map_app. Qed.

Lemma toks1_repeat n : toks1 (repeat true n) = repeat tx n.
Proof. induction n; cbn; [reflexivity|]. f_equal. exact IHn. Qed.

Lemma its_of_app u v : its_of (u ++ v) = its_of v ++ its_of u.
Proof. unfold its_of. rewrite map_app, rev_app_distr. reflexivity. Qed.

Lemma pxl_snoc_last c s : s <> [] -> pxl c s = removelast (pxl c s) ++ [xorb c (parity s)].
Proof.
  intro Hs. rewrite <- pxl_last_parity by exact Hs. apply app_removelast_last.
  destruct s; [congruence|discriminate].
Qed.

Lemma removelast_length' {T} (l:list T) : length (removelast l) = length l - 1.
Proof.
  induction l as [|a l IH]; [reflexivity|]. destruct l as [|b l]; [reflexivity|].
  change (removelast (a :: b :: l)) with (a :: removelast (b :: l)). cbn [length] in *. rewrite IH. lia.
Qed.

Lemma bridge W : forall W' its, Gs W = Some W' ->
  rsweep (PDY :: its) false (toks W) = Some (tx :: render its ++ [tD] ++ toks W').
Proof.
  induction W as [|sg W1 IH]; intros W' its HG; [discriminate|].
  destruct W1 as [|sg1 W1'].
  - (* single segment *)
    cbn [toks]. rewrite <- (app_nil_r (toks1 sg)), rsweep_bits. cbn [xorb].
    cbn [Gs] in HG. destruct (parity sg) eqn:HP.
    + inversion HG; subst W'. cbn [rsweep toks]. rewrite render_app', render_its_of. cbn [render itoks].
      unfold G1. cbn [toks1 map app b2t]. fold (toks1 (pxl false sg ++ [true;false])). rewrite toks1_app.
      cbn. rewrite <- !app_assoc. reflexivity.
    + destruct (beql (skipn (length sg - 2) (G1 sg)) [true;false;false]) eqn:Eb; [|discriminate].
      inversion HG; subst W'. apply beql_spec in Eb.
      assert (HS3: 3 <= length sg).
      { destruct sg as [|a [|b [|c S0]]]; cbn in Eb; try discriminate; cbn; lia. }
      assert (Hpre: pxl false sg = firstn (length sg - 3) (pxl false sg) ++ [true;false;false]).
      { unfold G1 in Eb. replace (length sg - 2) with (S (length sg - 3)) in Eb by lia. cbn [skipn] in Eb.
        rewrite <- Eb. symmetry. apply firstn_skipn. }
      set (pre := firstn (length sg - 3) (pxl false sg)) in *.
      rewrite Hpre, its_of_app. cbn [its_of map rev app b2i rsweep].
      cbn [toks]. rewrite render_app', render_its_of. cbn [render itoks].
      replace (firstn (length sg - 2) (G1 sg)) with (false :: pre).
      2:{ unfold G1. replace (length sg - 2) with (S (length sg - 3)) by lia. cbn [firstn]. reflexivity. }
      cbn [toks1 map b2t app]. fold (toks1 pre). rewrite <- !app_assoc. reflexivity.
  - (* head followed by D *)
    rewrite toks_cons by discriminate. rewrite rsweep_bits. cbn [xorb].
    rewrite Gs_cons2 in HG. destruct (parity sg) eqn:HP.
    + destruct (Gs (sg1 :: W1')) as [W1''|] eqn:EG; cbn [option_map] in HG; [|discriminate]. inversion HG; subst W'.
      assert (HSne: sg <> []) by (intro E; subst; discriminate).
      rewrite (pxl_snoc_last false sg HSne), HP, its_of_app. cbn [its_of map rev app b2i rsweep].
      rewrite (IH W1'' (its_of (removelast (pxl false sg)) ++ PDY :: its) eq_refl).
      rewrite toks_cons by (apply (Gs_nonempty _ _ EG)).
      rewrite render_app', render_its_of. cbn [render itoks].
      replace (F sg) with (false :: removelast (pxl false sg)).
      2:{ unfold F. rewrite (pxl_snoc_last false sg HSne) at 2. rewrite HP.
          replace (length sg) with (S (length (removelast (pxl false sg)))).
          2:{ rewrite removelast_length', pxl_length. destruct sg; [congruence|cbn; lia]. }
          cbn [firstn]. f_equal. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. }
      cbn [toks1 map b2t app]. fold (toks1 (removelast (pxl false sg))). rewrite <- !app_assoc. reflexivity.
    + destruct W1' as [|sg2 W1'']; [|discriminate]. inversion HG; subst W'.
      cbn [toks rsweep]. rewrite noD_toks1.
      rewrite render_app', render_its_of. cbn [render itoks].
      unfold G1. cbn [toks1 map b2t app]. fold (toks1 (pxl false sg ++ repeat true (length sg1) ++ [true;true;false])).
      rewrite !toks1_app, toks1_repeat, toks1_length.
      replace (length sg1 + 2) with (S (S (length sg1))) by lia.
      rewrite !repeat_snoc. rewrite <- !app_assoc. reflexivity.
Qed.

(** ===== list lemmas for dbl / ilv ===== *)
Lemma pxl_dbl s : pxl false (dbl s) = ilv s.
Proof. induction s as [|a s IH]; [reflexivity|]. destruct a; cbn; rewrite IH; reflexivity. Qed.

Lemma parity_dbl s : parity (dbl s) = false.
Proof. induction s as [|a s IH]; [reflexivity|]. cbn. rewrite IH. destruct a; reflexivity. Qed.

Lemma pxl_ilv c s : pxl c (ilv s) = dbl (pxl c s).
Proof. revert c; induction s as [|a s IH]; intro c; [reflexivity|]. cbn [ilv pxl dbl]. rewrite xorb_false_r, IH. reflexivity. Qed.

Lemma parity_ilv s : parity (ilv s) = parity s.
Proof. induction s as [|a s IH]; [reflexivity|]. cbn [ilv parity]. rewrite IH. destruct a; reflexivity. Qed.

Lemma dbl_app u v : dbl (u ++ v) = dbl u ++ dbl v.
Proof. induction u; cbn; [reflexivity|]. rewrite IHu. reflexivity. Qed.

Lemma ilv_app u v : ilv (u ++ v) = ilv u ++ ilv v.
Proof. induction u; cbn; [reflexivity|]. rewrite IHu. reflexivity. Qed.

Lemma pxl_app' c u v : pxl c (u ++ v) = pxl c u ++ pxl (xorb c (parity u)) v.
Proof. apply pxl_app. Qed.

Lemma removelast_app_single {T} (l:list T) a : removelast (l ++ [a]) = l.
Proof. apply removelast_last. Qed.

Lemma removelast_dbl s : s <> [] -> removelast (dbl s) = dbl (removelast s) ++ [last s false].
Proof.
  intro Hs. rewrite (app_removelast_last false Hs) at 1. rewrite dbl_app. cbn [dbl].
  replace (dbl (removelast s) ++ [last s false; last s false]) with ((dbl (removelast s) ++ [last s false]) ++ [last s false])
    by (rewrite <- app_assoc; reflexivity).
  apply removelast_last.
Qed.

Lemma nth_skipn' {T} k : forall i (l:list T) d, nth i (skipn k l) d = nth (k + i) l d.
Proof. induction k; intros i l d; [reflexivity|]. destruct l; cbn; [destruct i; reflexivity|apply IHk]. Qed.

Lemma ZP_decomp n H : ZP n H -> H = repeat false (S n) ++ skipn (S n) H /\ exists r, skipn (S n) H = true :: r.
Proof.
  intros [HZ [H1 HL]]. split.
  - rewrite <- (firstn_skipn (S n) H) at 1. f_equal.
    apply nth_ext with (d := false) (d' := false); rewrite firstn_length, ?repeat_length; [lia|].
    intros i Hi. rewrite nth_firstn, nth_repeat. destruct (Nat.ltb_spec i (S n)); [apply HZ; lia|lia].
  - destruct (skipn (S n) H) as [|b r] eqn:E.
    + exfalso. assert (length (skipn (S n) H) = O) by (rewrite E; reflexivity). rewrite skipn_length in H0. lia.
    + exists r. f_equal. rewrite <- H1. rewrite <- (Nat.add_0_r (S n)). rewrite <- nth_skipn'. rewrite E. reflexivity.
Qed.

(** ===== the four token-level rounds ===== *)
Lemma round1_head r W2 W3 : Gs W2 = Some W3 ->
  tstep (toks1 (dbl (true :: r)) ++ [tx; tD] ++ toks W2) = Some (toks1 (ilv (true :: r)) ++ tD :: toks W3).
Proof.
  intro HG.
  change (tstep (toks1 (dbl (true :: r)) ++ [tx; tD] ++ toks W2)) with (rsweep [PY] false (toks1 (dbl r) ++ [tx; tD] ++ toks W2)).
  rewrite rsweep_bits, pxl_dbl, parity_dbl.
  change (rsweep (its_of (ilv r) ++ [PY]) (xorb false false) ([tx; tD] ++ toks W2))
    with (rsweep (PDY :: its_of (ilv r) ++ [PY]) false (toks W2)).
  rewrite (bridge W2 W3 _ HG). f_equal.
  rewrite render_app', render_its_of. cbn [render itoks ilv toks1 map b2t app]. fold (toks1 (ilv r)).
  reflexivity.
Qed.

Lemma last_app2 {T} (u:list T) a b d : last (u ++ [a;b]) d = b.
Proof. replace (u ++ [a;b]) with ((u ++ [a]) ++ [b]) by (rewrite <- app_assoc; reflexivity). apply last_last. Qed.

Lemma outs_last r : last (true :: dbl (pxl true r)) false = xorb true (parity r).
Proof.
  destruct r as [|a r]; [reflexivity|].
  change (last (true :: dbl (pxl true (a :: r))) false) with (last (dbl (pxl true (a :: r))) false).
  assert (Hne: pxl true (a :: r) <> []) by discriminate.
  rewrite (app_removelast_last false Hne), dbl_app. cbn [dbl]. rewrite last_app2.
  rewrite pxl_last_parity by discriminate. reflexivity.
Qed.

Lemma round2_alive r W3 W4 : parity (true :: r) = true -> Gs W3 = Some W4 ->
  tstep (toks1 (ilv (true :: r)) ++ tD :: toks W3) = Some (toks1 (removelast (dbl (pxl false (true :: r)))) ++ tD :: toks W4).
Proof.
  intros HP HG.
  change (tstep (toks1 (ilv (true :: r)) ++ tD :: toks W3)) with (rsweep [PX] true (toks1 (ilv r) ++ tD :: toks W3)).
  rewrite rsweep_bits, pxl_ilv, parity_ilv.
  cbn [parity] in HP. replace (xorb true (parity r)) with true by (destruct (parity r); cbn in *; congruence).
  set (outs := true :: dbl (pxl true r)).
  assert (Hits: its_of (dbl (pxl true r)) ++ [PX] = its_of outs) by (unfold outs, its_of; reflexivity).
  rewrite Hits.
  assert (Hl: last outs false = true) by (unfold outs; rewrite outs_last; destruct (parity r); cbn in *; congruence).
  assert (Hne: outs <> []) by discriminate.
  rewrite (app_removelast_last false Hne), Hl, its_of_app.
  change (its_of [true]) with [PX]. cbn [app].
  change (rsweep (PX :: its_of (removelast outs)) true (tD :: toks W3))
    with (rsweep (PDY :: its_of (removelast outs)) false (toks W3)).
  rewrite (bridge W3 W4 _ HG), render_its_of.
  replace (dbl (pxl false (true :: r))) with (true :: outs) by reflexivity.
  replace (removelast (true :: outs)) with (true :: removelast outs).
  2:{ destruct outs; [congruence|reflexivity]. }
  reflexivity.
Qed.

Lemma round2_dies r s3 : parity (true :: r) = false ->
  tstep (toks1 (ilv (true :: r)) ++ tD :: toks [s3]) = Some (toks1 (dbl (pxl false (true :: r))) ++ repeat tx (length s3 + 2) ++ [ty]).
Proof.
  intros HP.
  change (tstep (toks1 (ilv (true :: r)) ++ tD :: toks [s3])) with (rsweep [PX] true (toks1 (ilv r) ++ tD :: toks1 s3)).
  rewrite rsweep_bits, pxl_ilv, parity_ilv.
  cbn [parity] in HP. replace (xorb true (parity r)) with false by (destruct (parity r); cbn in *; congruence).
  cbn [rsweep]. rewrite noD_toks1, toks1_length.
  rewrite render_app', render_its_of. reflexivity.
Qed.

Lemma round1_single r0 : tstep (toks1 (removelast (dbl ((true :: r0) ++ [true; false])))) =
  Some (toks1 (ilv (true :: r0)) ++ tD :: toks [[false;false;true;false]]).
Proof.
  assert (E: removelast (dbl ((true :: r0) ++ [true; false])) = true :: true :: dbl r0 ++ [true;true;false]).
  { rewrite dbl_app. change (dbl (true :: r0)) with (true :: true :: dbl r0).
    change (dbl [true;false]) with [true;true;false;false].
    replace ((true :: true :: dbl r0) ++ [true; true; false; false]) with ((true :: true :: dbl r0 ++ [true;true;false]) ++ [false])
      by (cbn; rewrite <- !app_assoc; reflexivity).
    apply removelast_last. }
  rewrite E.
  change (tstep (toks1 (true :: true :: dbl r0 ++ [true;true;false]))) with (rsweep [PY] false (toks1 (dbl r0 ++ [true;true;false]))).
  rewrite toks1_app, rsweep_bits, pxl_dbl, parity_dbl.
  change (rsweep (its_of (ilv r0) ++ [PY]) (xorb false false) (toks1 [true;true;false]))
    with (Some (tx :: render (its_of (ilv r0) ++ [PY]) ++ [tD;ty;ty;tx;ty])).
  rewrite render_app', render_its_of. reflexivity.
Qed.

(** ===== tail-side facts ===== *)
Lemma Tn_inj m m' W : 1 <= m -> 1 <= m' -> Tn m = Some W -> Tn m' = Some W -> m = m'.
Proof. intros H1 H2 E1 E2. pose proof (Tn_total m W H1 E1). pose proof (Tn_total m' W H2 E2). lia. Qed.

Lemma JJ_singles j : 1 <= j -> (exists s, Tn (JJ j) = Some [s]) /\ (exists s, Tn (JJ j + 1) = Some [s]).
Proof.
  intro Hj. destruct (Epoch_all (j + 4) ltac:(lia)) as [_ [_ [_ HD]]]. apply HD; [exact Hj|].
  pose proof (JJ_small j (j+3) ltac:(lia) ltac:(lia)). replace (j + 4) with (S (j+3)) by lia. rewrite pow_S. lia.
Qed.

Lemma death_single j : 1 <= j -> exists s, Tn (2 * JJ j + 1) = Some [s].
Proof.
  intro Hj. destruct (Nat.eq_dec j 1) as [->|Hj1].
  - exists [false;false;false;false;true;false;true;true;true;false]. vm_compute. reflexivity.
  - pose proof (JJ_formula j ltac:(lia)) as F1. pose proof (JJ_formula (S j) ltac:(lia)) as F2.
    pose proof (eps_range j) as E1. pose proof (eps_range (S j)) as E2.
    assert (Heps: eps (S j) = 3 - eps j) by (unfold eps; rewrite Nat.odd_succ, <- Nat.negb_odd; destruct (Nat.odd j); reflexivity).
    rewrite pow_S in F2. assert (4 <= 2^j) by (pose proof (pow_mono 2 j ltac:(lia)); cbn in H; lia).
    destruct (JJ_singles (S j) ltac:(lia)) as [[s1 Hs1] [s2 Hs2]].
    destruct E1 as [E1|E1].
    + rewrite E1 in Heps. assert (Hq: 2 * JJ j + 1 = JJ (S j)) by lia. rewrite Hq. eauto.
    + rewrite E1 in Heps. assert (Hq: 2 * JJ j + 1 = JJ (S j) + 1) by lia. rewrite Hq. eauto.
Qed.

Lemma Tn_some n : 1 <= n -> exists W, Tn n = Some W.
Proof. intro Hn. destruct (Tn n) eqn:E; [eauto|]. exfalso. apply (tail_never_halts n Hn E). Qed.

Definition RelD (n:nat) (RR:list tok) : Prop :=
  exists W, Tn n = Some W /\
   ((exists sg, W = [sg] /\ RR = toks1 (removelast (dbl (skipn (S n) sg)))) \/
    (exists H Wm m W2, W = H :: Wm /\ 1 <= m /\ Tn m = Some Wm /\ Tn (2*m) = Some W2 /\
        RR = toks1 (dbl (skipn (S n) H)) ++ [tx; tD] ++ toks W2)).

Lemma skipn_zeros_app {T} n (z:T) l : skipn n (repeat z n ++ l) = l.
Proof. induction n; cbn; auto. Qed.

Lemma G1_split n Hs : G1 (repeat false (S n) ++ Hs) = repeat false (S (S n)) ++ pxl false Hs.
Proof. rewrite G1_zeros_l. unfold G1. rewrite (repeat_snoc false (S n)), <- app_assoc. reflexivity. Qed.

Lemma skipn_F n Hs : Hs <> [] -> skipn (S (S n)) (F (repeat false (S n) ++ Hs)) = removelast (pxl false Hs).
Proof.
  intro Hne. rewrite F_as_G1, G1_split, app_length, repeat_length.
  replace (S n + length Hs) with (S (S n) + (length Hs - 1)) by (destruct Hs; [congruence|cbn; lia]).
  rewrite firstn_app, repeat_length, firstn_all2 by (rewrite repeat_length; lia).
  replace (S (S n) + (length Hs - 1) - S (S n)) with (length Hs - 1) by lia.
  rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia). rewrite Nat.sub_diag. cbn [skipn app].
  rewrite (app_removelast_last false (l:=pxl false Hs)) at 1 by (destruct Hs; [congruence|discriminate]).
  rewrite firstn_app, removelast_length', pxl_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite removelast_length', pxl_length; lia). reflexivity.
Qed.

Lemma dbl_repeat k : dbl (repeat true k) = repeat true (2 * k).
Proof. induction k; [reflexivity|]. cbn [repeat dbl]. rewrite IHk. replace (2 * S k) with (S (S (2 * k))) by lia. reflexivity. Qed.

Lemma toks1_repeat_tx k : toks1 (repeat true k) = repeat tx k.
Proof. apply toks1_repeat. Qed.

Lemma doubling n RR : 9 <= n -> RelD n RR -> exists R1 R2, tstep RR = Some R1 /\ tstep R1 = Some R2 /\ RelD (S n) R2.
Proof.
  intros Hn [W [HW HR]].
  destruct (tail_good n ltac:(lia)) as [W0 [HW0 [HZ Hcase]]]. rewrite HW in HW0. inversion HW0; subst W0. clear HW0.
  destruct (Tn_some (S n) ltac:(lia)) as [Wn HWn].
  pose proof HWn as HGs. rewrite Tn_S, HW in HGs by lia.
  destruct HR as [[sg [-> HRs]]|[H [Wm [m [W2 [-> [Hm [HTm [HTW2 HRh]]]]]]]]].
  - (* single *)
    cbn [hd] in HZ. destruct (ZP_decomp n sg HZ) as [Hsg [r Hr]].
    destruct (Tn_ends n [sg] ltac:(lia) HW) as [p Hp]. cbn [last] in Hp.
    pose proof (single_len n sg ltac:(lia) HW) as Hlen.
    assert (HSs: skipn (S n) sg = skipn (S n) p ++ [true;false]).
    { rewrite Hp, skipn_app. replace (S n - length p) with 0 by (assert (length p = 3*n-1) by (rewrite Hp, app_length in Hlen; cbn in Hlen; lia); lia).
      reflexivity. }
    assert (Hp0: exists r0, skipn (S n) p = true :: r0).
    { destruct (skipn (S n) p) as [|b r0] eqn:Ep.
      - exfalso. assert (length (skipn (S n) p) = 0) by (rewrite Ep; reflexivity). rewrite skipn_length in H.
        rewrite Hp, app_length in Hlen. cbn in Hlen. lia.
      - exists r0. rewrite HSs in Hr. cbn in Hr. inversion Hr. reflexivity. }
    destruct Hp0 as [r0 Hr0]. rewrite HSs, Hr0 in HRs. rewrite Hr0 in HSs.
    clear Hr.
    set (Ss0 := true :: r0) in *.
    assert (HpS: parity sg = xorb (parity Ss0) true).
    { rewrite Hsg, parity_app, parity_zeros, HSs, parity_app. reflexivity. }
    cbn [Gs] in HGs.
    destruct (parity Ss0) eqn:EP.
    + (* split: parity sg = false *)
      rewrite HpS in HGs. cbn [xorb] in HGs.
      destruct (beql _ _) eqn:Eb; [|discriminate]. inversion HGs; subst Wn. clear HGs.
      destruct (Tn_some 2 ltac:(lia)) as [W4 HW4].
      assert (HG1: Gs [[false;false;true;false]] = Some W4) by (rewrite <- HW4; reflexivity).
      exists (toks1 (ilv Ss0) ++ tD :: toks [[false;false;true;false]]).
      eexists. split; [subst RR; apply round1_single|]. split.
      { apply (round2_alive r0 _ W4 EP HG1). }
      exists [firstn (length sg - 2) (G1 sg); [false;false;true;false]]. split; [exact HWn|].
      right. exists (firstn (length sg - 2) (G1 sg)), [[false;false;true;false]], 1, W4.
      split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [exact HW4|].
      fold Ss0.
      assert (Hsk: skipn (S (S n)) (firstn (length sg - 2) (G1 sg)) = removelast (pxl false Ss0)).
      { rewrite Hsg at 2. rewrite G1_split, HSs, pxl_app, firstn_app, repeat_length.
        assert (HL: length sg = S n + length Ss0 + 2) by (rewrite Hsg, app_length, repeat_length, HSs, app_length; cbn; lia).
        rewrite HL, firstn_all2 by (rewrite repeat_length; lia).
        replace (S n + length Ss0 + 2 - 2 - S (S n)) with (length Ss0 - 1) by lia.
        rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia). rewrite Nat.sub_diag. cbn [skipn app].
        rewrite firstn_app, pxl_length. replace (length Ss0 - 1 - length Ss0) with 0 by lia. rewrite firstn_O, app_nil_r.
        assert (Hne: pxl false Ss0 <> []) by discriminate.
        rewrite (app_removelast_last false Hne) at 1. rewrite firstn_app, removelast_length', pxl_length.
        replace (length Ss0 - 1 - (length Ss0 - 1)) with 0 by lia. rewrite firstn_O, app_nil_r.
        rewrite firstn_all2 by (rewrite removelast_length', pxl_length; lia). reflexivity. }
      rewrite Hsk.
      rewrite (removelast_dbl (pxl false Ss0)) by discriminate. rewrite pxl_last_parity by discriminate. rewrite EP.
      rewrite toks1_app. cbn [toks1 map b2t xorb]. rewrite <- app_assoc. reflexivity.
    + (* grow: parity sg = true *)
      rewrite HpS in HGs. cbn [xorb] in HGs. inversion HGs; subst Wn. clear HGs.
      exists (toks1 (ilv Ss0) ++ tD :: toks [[false;false;true;false]]).
      eexists. split; [subst RR; apply round1_single|]. split.
      { apply (round2_dies r0 [false;false;true;false] EP). }
      exists [G1 sg ++ [true;false]]. split; [exact HWn|]. left. exists (G1 sg ++ [true;false]). split; [reflexivity|].
      rewrite Hsg at 1. rewrite G1_split, <- app_assoc, skipn_zeros_app, HSs, pxl_app.
      cbn [length Nat.add]. fold Ss0. rewrite EP. cbn [pxl xorb].
      rewrite !dbl_app. cbn [dbl app].
      replace ((dbl (pxl false Ss0) ++ [true; true; true; true]) ++ [true; true; false; false])
        with ((dbl (pxl false Ss0) ++ [true; true; true; true; true; true; false]) ++ [false]) by (rewrite <- !app_assoc; reflexivity).
      rewrite removelast_last. rewrite toks1_app. reflexivity.
  - (* head *)
    cbn [hd] in HZ. destruct (ZP_decomp n H HZ) as [HH [r Hr]].
    assert (HWmne: Wm <> []) by (apply (Good_nonempty m); [apply tail_good; lia|exact HTm]).
    destruct Hcase as [[s Hs]|[H' [m' [Wm' [HE [Hm' [HTm' Hd]]]]]]]; [inversion Hs; subst; congruence|].
    inversion HE; subst H' Wm'. clear HE.
    assert (m' = m) by (apply (Tn_inj m' m Wm); [lia|lia|exact HTm'|exact HTm]). subst m'.
    rewrite Hr in HRh.
    destruct (Tn_some (S (2*m)) ltac:(lia)) as [W3 HW3].
    assert (HG2: Gs W2 = Some W3) by (rewrite <- HW3, Tn_S, HTW2 by lia; reflexivity).
    exists (toks1 (ilv (true :: r)) ++ tD :: toks W3).
    assert (HpH: parity H = parity (true :: r)) by (rewrite HH, parity_app, parity_zeros, Hr; reflexivity).
    destruct (parity (true :: r)) eqn:EP.
    + (* alive *)
      destruct (Tn_some (S (S (2*m))) ltac:(lia)) as [W4 HW4].
      assert (HG3: Gs W3 = Some W4) by (rewrite <- HW4, Tn_S, HW3 by lia; reflexivity).
      eexists. split; [subst RR; apply round1_head, HG2|]. split; [apply (round2_alive r W3 W4 EP HG3)|].
      rewrite Gs_alive in HGs by (auto; rewrite HpH; reflexivity).
      destruct (Tn_some (S m) ltac:(lia)) as [Wm2 HWm2].
      assert (HGm: Gs Wm = Some Wm2) by (rewrite <- HWm2, Tn_S, HTm by lia; reflexivity).
      rewrite HGm in HGs. cbn in HGs. inversion HGs; subst Wn. clear HGs.
      exists (F H :: Wm2). split; [exact HWn|]. right.
      exists (F H), Wm2, (S m), W4. split; [reflexivity|]. split; [lia|]. split; [exact HWm2|].
      split; [replace (2 * S m) with (S (S (2*m))) by lia; exact HW4|].
      rewrite HH at 1. rewrite Hr at 1. rewrite skipn_F by discriminate.
      rewrite (removelast_dbl (pxl false (true :: r))) by discriminate. rewrite pxl_last_parity by discriminate.
      cbn [xorb]. rewrite EP. rewrite toks1_app. cbn [toks1 map b2t xorb]. rewrite <- app_assoc. reflexivity.
    + (* dies *)
      destruct (Hd ltac:(rewrite HpH; reflexivity)) as [j [Hj Hmj]].
      destruct (death_single j Hj) as [s3 Hs3]. rewrite <- Hmj in Hs3.
      replace (2 * m + 1) with (S (2 * m)) in Hs3 by lia. rewrite HW3 in Hs3. inversion Hs3; subst W3. clear Hs3.
      eexists. split; [subst RR; apply round1_head, HG2|]. split; [apply (round2_dies r s3 EP)|].
      destruct Wm as [|s Wm]; [congruence|]. rewrite Gs_cons2 in HGs. rewrite HpH in HGs. cbn [xorb] in HGs.
      destruct Wm; [|discriminate]. inversion HGs; subst Wn. clear HGs.
      exists [G1 H ++ repeat true (length s) ++ [true;true;false]]. split; [exact HWn|]. left.
      eexists. split; [reflexivity|].
      pose proof (single_len m s ltac:(lia) HTm) as Hls.
      pose proof (single_len (S (2*m)) s3 ltac:(lia) HW3) as Hls3.
      rewrite HH at 1. rewrite G1_split, <- app_assoc, skipn_zeros_app, Hr, Hls.
      rewrite !dbl_app, dbl_repeat. cbn [dbl app].
      replace (dbl (pxl false (true :: r)) ++ repeat true (2 * (3 * m + 1)) ++ [true; true; true; true; false; false])
        with ((dbl (pxl false (true :: r)) ++ repeat true (2 * (3 * m + 1)) ++ [true; true; true; true; false]) ++ [false])
        by (rewrite <- !app_assoc; reflexivity).
      rewrite removelast_last, Hls3, !toks1_app, toks1_repeat.
      replace (3 * S (2 * m) + 1 + 2) with (2 * (3 * m + 1) + 4) by lia.
      rewrite repeat_app. cbn [toks1 map b2t repeat]. rewrite <- !app_assoc. reflexivity.
Qed.

(** ===== final assembly ===== *)
Lemma RelD9 : RelD 9 w1.
Proof.
  destruct (Tn_some 9 ltac:(lia)) as [W HW].
  exists W. split; [exact HW|]. left.
  vm_compute in HW. inversion HW; subst W. eexists. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Lemma iter_add a : forall b w, iter (a + b) w = match iter a w with Some w' => iter b w' | None => None end.
Proof.
  induction a; intros b w; cbn; [reflexivity|].
  destruct (tstep w); [apply IHa|reflexivity].
Qed.

Lemma iter_rel i : exists RR, iter (2*i) w1 = Some RR /\ RelD (9+i) RR.
Proof.
  induction i as [|i [RR [HR HRel]]].
  - exists w1. split; [reflexivity|exact RelD9].
  - destruct (doubling (9+i) RR ltac:(lia) HRel) as [R1 [R2 [H1 [H2 H3]]]].
    exists R2. split.
    + replace (2 * S i) with (2*i + 2) by lia. rewrite iter_add, HR. cbn. rewrite H1, H2. reflexivity.
    + replace (9 + S i) with (S (9 + i)) by lia. exact H3.
Qed.

Theorem tokens_never_halt : forall n, iter n w1 <> None.
Proof.
  intro n. destruct (PeanoNat.Nat.Even_or_Odd n) as [[i Hi]|[i Hi]];
    destruct (iter_rel i) as [RR [HR HRel]].
  - subst n. rewrite HR. discriminate.
  - destruct (doubling (9+i) RR ltac:(lia) HRel) as [R1 [R2 [H1 [H2 H3]]]].
    subst n. replace (2 * i + 1) with (2*i + 1) by lia. rewrite iter_add, HR. cbn. rewrite H1. discriminate.
Qed.

Theorem FIB1_nonhalt : ~ halts tm c0.
Proof. apply nonhalt_of_tokens, tokens_never_halt. Qed.



Theorem nonhalt : ~ halts tm c0.
Proof. exact FIB1_nonhalt. Qed.

Print Assumptions nonhalt.
