(** BB(6) holdout 1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_---1LC ("fractal in bouncer"): it never halts.

    Written by Claude (Anthropic), working autonomously with the permission of the account owner.

    Outline.
    1. Token model (Part 1). At every left record the tape is 0^inf [A]0 1 0 enc(w) 0^inf, where w is a word over
       the tokens x = 011, y = 111, D = 01. A round trip is a fixed right sweep (x -> 110, y -> 111, D y -> 11011)
       followed by a left sweep that runs a carry from the right end. [tstep_sim]: tstep w = Some w' -> Cfg w -->+ Cfg w'.
    2. Segment system (Part 2). Read the word right to left and cut it at the D's: a list of bit lists (x = 1, y = 0).
       One round [Gs]: each segment S becomes Phi(S) = NOT prefixXOR(S); at a D the segment before it is kept if its
       parity is 1 and "wiped" (merged with the single segment after it) if its parity is 0; at the end, parity 0
       appends 11 and parity 1 appends 0 and opens an empty segment. T(0) = [[]].
       Parity polynomial N_S(w) = (1+w) sigma_S(w) + 1 + (1+w)^|S| with sigma_S = sum_j s_j (1+w)^j satisfies
       parity(Phi^r S) = [w^r] N_S / (1+w)^(|S|+1), N_{X++Y} = N_X + (1+w)^|X| N_Y, w N_{Phi S} = N_S + parity(S)(1+w)^(|S|+1).
       Induction over epochs 2^k: T(2^k) = [U_k] with N_{U_k} = w^(2^(k-1)-1) * (sparse); the epoch copies T(j) for
       j < 2^(k-1) (lift), then one head lives exactly 2^(k-1) rounds (its N has a sparse closed form) and dies
       against a single segment, and the merge gives U_(k+1). Hence T(n) is defined for all n ([T_total]).
    3. Bridge (Part 3). tstep on the encoded word equals Gs on segments, so tstep never fails.
*)

From BusyCoq Require Import Individual62.
Require Import Lia Bool String List Arith Setoid Morphisms Permutation Btauto.
Import ListNotations.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_0LD0LD_0LE1LF_1LA0RA_---1LC"%string).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Open Scope list_scope.

(** ===== Right sweep ===== *)
Lemma RS_start l r: l {{A}}> [0;1;0] *> r -->+ l <* [1;1;1] {{A}}> r.
Proof. cbn; triv. Qed.
Lemma RS_x l r: l {{A}}> [0;1;1] *> r -->+ l <* [0;1;1] {{A}}> r.
Proof. cbn; triv. Qed.
Lemma RS_y l r: l {{A}}> [1;1;1] *> r -->+ l <* [1;1;1] {{A}}> r.
Proof. cbn; triv. Qed.
Lemma RS_Dy l r: l {{A}}> [0;1;1;1;1] *> r -->+ l <* [1;1;0;1;1] {{A}}> r.
Proof. cbn; triv. Qed.

(** ===== Right wall: start of the left sweep ===== *)
Lemma WALL_x l: l <* [0;1;1] {{A}}> [0;1] *> const 0 -->+ l <* [1;0;1] <{{C}} [1;1;1;0;1] *> const 0.
Proof. cbn; triv. Qed.
Lemma WALL_y l: l <* [1;1;1] {{A}}> [0;1] *> const 0 -->+ l <* [1;1;1] <{{D}} [0;1;1;0;1] *> const 0.
Proof. cbn; triv. Qed.
Lemma WALL_yD l: l <* [1;1;0] {{A}}> [0;1] *> const 0 -->+ l <* [1;1;0] <{{D}} [0;1;1;0;1] *> const 0.
Proof. cbn; triv. Qed.

(** ===== Left sweep: one token (markers: normal 111/101, after-D 110/100, head-outward) ===== *)
Lemma U_x0 l r: l <* [0;1;1] <* [1;1;1] <{{D}} [0;1;1] *> r -->+ l <* [1;0;1] <{{C}} [1;1;1] *> [0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma U_x1 l r: l <* [0;1;1] <* [1;0;1] <{{C}} [1;1;1] *> r -->+ l <* [1;1;1] <{{D}} [0;1;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma U_y0 l r: l <* [1;1;1] <* [1;1;1] <{{D}} [0;1;1] *> r -->+ l <* [1;1;1] <{{D}} [0;1;1] *> [0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma U_y1 l r: l <* [1;1;1] <* [1;0;1] <{{C}} [1;1;1] *> r -->+ l <* [1;0;1] <{{C}} [1;1;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma U_yD0 l r: l <* [1;1;0] <* [1;1;1] <{{D}} [0;1;1] *> r -->+ l <* [1;1;0] <{{D}} [0;1;1] *> [0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma U_yD1 l r: l <* [1;1;0] <* [1;0;1] <{{C}} [1;1;1] *> r -->+ l <* [1;0;0] <{{C}} [1;1;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.

(** ===== A kept D (carry 1 at the D) together with the next token ===== *)
Lemma KEEP_x l r: l <* [0;1;1] <* [1;1] <* [1;0;0] <{{C}} [1;1;1] *> r -->+
  l <* [1;0;1] <{{C}} [1;1;1] *> [0;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma KEEP_y l r: l <* [1;1;1] <* [1;1] <* [1;0;0] <{{C}} [1;1;1] *> r -->+
  l <* [1;1;1] <{{D}} [0;1;1] *> [0;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma KEEP_yD l r: l <* [1;1;0] <* [1;1] <* [1;0;0] <{{C}} [1;1;1] *> r -->+
  l <* [1;1;0] <{{D}} [0;1;1] *> [0;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.

(** ===== A wiped D (carry 0 at the D) ===== *)
Lemma WIPE_enter l r: l <* [1;1] <* [1;1;0] <{{D}} r -->+ l <{{C}} [1;1;0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma WIPE_x l r: l <* [0;1;1] <{{C}} r -->+ l <{{C}} [1;1;0] *> r.
Proof. cbn; triv. Qed.
Lemma WIPE_y l r: l <* [1;1;1] <{{C}} r -->+ l <{{C}} [1;1;0] *> r.
Proof. cbn; triv. Qed.
Lemma WIPE_wall r: const 0 <* [1;1;1] <{{C}} r -->+ const 0 {{A}}> [0;1;0;0;1;1;0] *> r.
Proof. cbn; triv. Qed.

(** ===== Left wall: the end rules ===== *)
Lemma END0 r: const 0 <* [1;1;1] <* [1;1;1] <{{D}} [0;1;1] *> r -->+
  const 0 {{A}}> [0;1;0;0;1;1;0;1;1] *> [0;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma END1 r: const 0 <* [1;1;1] <* [1;0;1] <{{C}} [1;1;1] *> r -->+
  const 0 {{A}}> [0;1;0;0;1;1;1;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.
Lemma KEEP_end r: const 0 <* [1;1;1] <* [1;1] <* [1;0;0] <{{C}} [1;1;1] *> r -->+
  const 0 {{A}}> [0;1;0;0;1;1;0;1;1;0;1] *> [1;1;1] *> r.
Proof. cbn; triv. Qed.

(** ===== Tokens ===== *)
Inductive tok := tx | ty | tD.
Definition enc_tok (t:tok) : list sym := match t with tx => [0;1;1] | ty => [1;1;1] | tD => [0;1] end.
Fixpoint enc (w:list tok) : list sym := match w with [] => [] | t::w' => enc_tok t ++ enc w' end.
Definition Cfg (w:list tok) := const 0 {{A}}> [0;1;0] *> enc w *> const 0.

Lemma enc_app u v: enc (u ++ v) = enc u ++ enc v.
Proof. induction u; cbn; [reflexivity|]. rewrite IHu, app_assoc. reflexivity. Qed.

Definition isD (t:tok) : bool := match t with tD => true | _ => false end.
Definition isx (t:tok) : bool := match t with tx => true | _ => false end.
Definition startsD (p:list tok) : bool := match p with tD :: _ => true | _ => false end.
Definition tokc (c:bool) : tok := if c then ty else tx.
Definition qc (c:bool) : Q := if c then C else D.
Definition mk (c b:bool) : list sym :=
  if b then (if c then [1;0;0] else [1;1;0]) else (if c then [1;0;1] else [1;1;1]).
Definition RSh (s:tok) (b:bool) : list sym :=
  match s with tx => [0;1;1] | ty => if b then [1;1;0] else [1;1;1] | tD => [1;1] end.

(** right-swept cells of a word given in processing order (= reversed tape order), head-outward *)
Fixpoint rsl (p:list tok) : list sym :=
  match p with
  | [] => []
  | tx :: p' => [0;1;1] ++ rsl p'
  | ty :: p' => match p' with tD :: p'' => [1;1;0] ++ [1;1] ++ rsl p'' | _ => [1;1;1] ++ rsl p' end
  | tD :: p' => [1;1] ++ rsl p'
  end.
Definition LS (p:list tok) : side := const 0 <* [1;1;1] <* rsl p.

Lemma rsl_cons s p: s <> tD -> rsl (s :: p) = RSh s (startsD p) ++ rsl p.
Proof. intro H. destruct s; [reflexivity| |congruence]. destruct p as [|[] p]; reflexivity. Qed.
Lemma LS_cons s p: s <> tD -> LS (s :: p) = LS p <* RSh s (startsD p).
Proof. intro H. unfold LS. rewrite rsl_cons by exact H. rewrite Str_app_assoc. reflexivity. Qed.
Lemma LS_D p: LS (tD :: p) = LS p <* [1;1].
Proof. unfold LS. cbn [rsl]. rewrite Str_app_assoc. reflexivity. Qed.

(** tape-order well-formedness: every D is followed by y *)
Fixpoint wfD (v:list tok) : bool :=
  match v with
  | [] => true
  | tD :: v' => match v' with ty :: v'' => wfD v'' | _ => false end
  | _ :: v' => wfD v'
  end.

Lemma RSWEEP_gen n: forall v p r, length v <= n -> wfD v = true -> startsD p = false ->
  LS p {{A}}> enc v *> r -->* LS (rev v ++ p) {{A}}> r.
Proof.
  induction n as [|n IH]; intros v p r Hl Hw Hp.
  - destruct v; [apply evstep_refl|cbn in Hl; lia].
  - destruct v as [|t v]; [apply evstep_refl|].
    destruct t.
    + cbn [enc enc_tok]. rewrite Str_app_assoc.
      eapply evstep_trans. { apply progress_evstep, RS_x. }
      replace (LS p <* [0;1;1]) with (LS (tx :: p)) by (rewrite LS_cons by discriminate; reflexivity).
      cbn [rev]. rewrite <- app_assoc. apply IH; [cbn in Hl; lia|exact Hw|reflexivity].
    + cbn [enc enc_tok]. rewrite Str_app_assoc.
      eapply evstep_trans. { apply progress_evstep, RS_y. }
      replace (LS p <* [1;1;1]) with (LS (ty :: p)) by (rewrite LS_cons by discriminate; rewrite Hp; reflexivity).
      cbn [rev]. rewrite <- app_assoc. apply IH; [cbn in Hl; lia|exact Hw|reflexivity].
    + destruct v as [|[] v]; cbn in Hw; try discriminate.
      cbn [enc enc_tok app].
      change (0 :: 1 :: 1 :: 1 :: 1 :: enc v) with ([0;1;1;1;1] ++ enc v). rewrite Str_app_assoc.
      eapply evstep_trans. { apply progress_evstep, RS_Dy. }
      replace (LS p <* [1;1;0;1;1]) with (LS (ty :: tD :: p))
        by (unfold LS; cbn [rsl]; rewrite !Str_app_assoc; reflexivity).
      replace (rev (tD :: ty :: v) ++ p) with (rev v ++ ty :: tD :: p)
        by (cbn [rev]; rewrite <- !app_assoc; reflexivity).
      apply IH; [cbn in Hl; lia|exact Hw|reflexivity].
Qed.

(** ===== The left sweep as a function ===== *)
Fixpoint lsw (c:bool) (pend:list tok) (out:list tok) : option (list tok) :=
  match pend with
  | [] => Some ((if c then [tD; ty] else [tx; tx]) ++ out)
  | tD :: pend' =>
      if c then
        match pend' with
        | [] => Some ([tx; tx; tD] ++ out)
        | tD :: _ => None
        | s :: pend'' => if andb (isx s) (startsD pend'') then None
                         else lsw (isx s) pend'' (tokc (isx s) :: tD :: out)
        end
      else if existsb isD pend' then None
      else Some (repeat tx (length pend' + 3) ++ out)
  | s :: pend' =>
      if andb (isx s) (startsD pend') then None
      else lsw (xorb c (isx s)) pend' (tokc (xorb c (isx s)) :: out)
  end.

Definition tstep (w:list tok) : option (list tok) :=
  match rev w with
  | tD :: s :: pend =>
      if isD s then None
      else if andb (isx s) (startsD pend) then None
      else if wfD (rev pend ++ [s]) then lsw (isx s) pend [tokc (isx s); tD]
      else None
  | _ => None
  end.

(** ===== Simulation ===== *)
Lemma concat_repeat_snoc {T} (a:list T) n: concat (repeat a n) ++ a = a ++ concat (repeat a n).
Proof. induction n as [|n IH]; cbn; [rewrite app_nil_r; reflexivity|]. rewrite <- app_assoc, IH. reflexivity. Qed.

Lemma wipe_run p r: existsb isD p = false ->
  LS p <{{C}} r -->* LS [] <{{C}} concat (repeat [1;1;0] (length p)) *> r.
Proof.
  revert r. induction p as [|s p IH]; intros r H.
  - apply evstep_refl.
  - cbn in H. apply orb_false_iff in H as [Hs Hp].
    assert (Hsp: startsD p = false) by (destruct p as [|[] p]; cbn in Hp |- *; try reflexivity; discriminate).
    rewrite LS_cons by (destruct s; cbn in Hs; congruence).
    eapply evstep_trans.
    { apply progress_evstep. rewrite Hsp. destruct s; cbn in Hs; try discriminate.
      - apply WIPE_x. - apply WIPE_y. }
    replace (concat (repeat [1;1;0] (length (s :: p))) *> r) with (concat (repeat [1;1;0] (length p)) *> [1;1;0] *> r).
    2:{ cbn [length repeat concat]. rewrite <- Str_app_assoc, concat_repeat_snoc. reflexivity. }
    apply IH, Hp.
Qed.

Lemma enc_repeat_tx k: enc (repeat tx k) = concat (repeat [0;1;1] k).
Proof. induction k; cbn; [reflexivity|]. rewrite IHk. reflexivity. Qed.

Lemma shift_list k: [0] ++ concat (repeat [1;1;0] k) ++ [1;1] = concat (repeat [0;1;1] (S k)).
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (concat (repeat [0;1;1] (S (S k)))) with ([0;1;1] ++ concat (repeat [0;1;1] (S k))).
  rewrite <- IH. simpl. reflexivity.
Qed.

Lemma wipe_cells k:
  [0;1;0;0;1;1;0] ++ concat (repeat [1;1;0] k) ++ [1;1;0;1;1] = [0;1;0] ++ enc (repeat tx (k+3)).
Proof.
  rewrite enc_repeat_tx. replace (k+3) with (S (S (S k))) by lia.
  rewrite <- (shift_list (S (S k))).
  change (repeat [1;1;0] (S (S k))) with ([1;1;0] :: [1;1;0] :: repeat [1;1;0] k).
  cbn [concat]. rewrite <- (concat_repeat_snoc [1;1;0] k). cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma end_case c out':
  LS [] <* mk c false <{{qc c}} enc (tokc c :: out') *> const 0 -->+
  Cfg ((if c then [tD; ty] else [tx; tx]) ++ tokc c :: out').
Proof.
  unfold LS, Cfg. destruct c; cbn [rsl mk qc tokc enc enc_tok app].
  - change (const 0 <* [1;1;1] <* [] <* [1;0;1]) with (const 0 <* [1;1;1] <* [1;0;1]).
    change (1 :: 1 :: 1 :: enc out') with ([1;1;1] ++ enc out'). rewrite Str_app_assoc.
    eapply progress_evstep_trans. { apply END1. } apply evstep_refl'. reflexivity.
  - change (const 0 <* [1;1;1] <* [] <* [1;1;1]) with (const 0 <* [1;1;1] <* [1;1;1]).
    change (0 :: 1 :: 1 :: enc out') with ([0;1;1] ++ enc out'). rewrite Str_app_assoc.
    eapply progress_evstep_trans. { apply END0. } apply evstep_refl'. reflexivity.
Qed.

Lemma lsw_sim n: forall pend c out' w', length pend <= n ->
  lsw c pend (tokc c :: out') = Some w' ->
  LS pend <* mk c (startsD pend) <{{qc c}} enc (tokc c :: out') *> const 0 -->+ Cfg w'.
Proof.
  induction n as [|n IH]; intros pend c out' w' Hl H.
  - destruct pend; [|cbn in Hl; lia].
    cbn in H. inversion H; subst. apply end_case.
  - destruct pend as [|t pend].
    { cbn in H. inversion H; subst. apply end_case. }
    destruct t.
    + (* x *)
      cbn [lsw] in H. destruct (startsD pend) eqn:Hs; cbn in H; [discriminate|].
      rewrite LS_cons by discriminate. rewrite Hs. cbn [startsD].
      destruct c; cbn [mk qc tokc enc enc_tok RSh xorb isx] in H |- *; rewrite ?Str_app_assoc.
      * eapply progress_trans. { apply U_x1. }
        change ([0;1;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc false :: ty :: out') *> const 0).
        replace [1;1;1] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend false (ty :: out') w'); [cbn in Hl; lia|exact H].
      * eapply progress_trans. { apply U_x0. }
        change ([1;1;1] *> [0;1;1] *> enc out' *> const 0) with (enc (tokc true :: tx :: out') *> const 0).
        replace [1;0;1] with (mk true (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend true (tx :: out') w'); [cbn in Hl; lia|exact H].
    + (* y *)
      cbn [lsw] in H. cbn [andb isx] in H. rewrite xorb_false_r in H.
      rewrite LS_cons by discriminate. cbn [startsD].
      destruct c, (startsD pend) eqn:Hs; cbn [mk qc tokc enc enc_tok RSh] in H |- *; rewrite ?Str_app_assoc.
      * eapply progress_trans. { apply U_yD1. }
        change ([1;1;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc true :: ty :: out') *> const 0).
        replace [1;0;0] with (mk true (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend true (ty :: out') w'); [cbn in Hl; lia|exact H].
      * eapply progress_trans. { apply U_y1. }
        change ([1;1;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc true :: ty :: out') *> const 0).
        replace [1;0;1] with (mk true (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend true (ty :: out') w'); [cbn in Hl; lia|exact H].
      * eapply progress_trans. { apply U_yD0. }
        change ([0;1;1] *> [0;1;1] *> enc out' *> const 0) with (enc (tokc false :: tx :: out') *> const 0).
        replace [1;1;0] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend false (tx :: out') w'); [cbn in Hl; lia|exact H].
      * eapply progress_trans. { apply U_y0. }
        change ([0;1;1] *> [0;1;1] *> enc out' *> const 0) with (enc (tokc false :: tx :: out') *> const 0).
        replace [1;1;1] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
        apply (IH pend false (tx :: out') w'); [cbn in Hl; lia|exact H].
    + (* D *)
      rewrite LS_D. cbn [startsD]. destruct c.
      * cbn [lsw] in H. destruct pend as [|s pend].
        -- inversion H; subst. unfold LS, Cfg. cbn [rsl mk qc tokc enc enc_tok app].
           change (const 0 <* [1;1;1] <* [] <* [1;1] <* [1;0;0]) with (const 0 <* [1;1;1] <* [1;1] <* [1;0;0]).
           change (1 :: 1 :: 1 :: enc out') with ([1;1;1] ++ enc out'). rewrite Str_app_assoc.
           eapply progress_evstep_trans. { apply KEEP_end. } apply evstep_refl'. reflexivity.
        -- destruct s; [| |discriminate].
           ++ destruct (startsD pend) eqn:Hs; cbn in H; [discriminate|].
              rewrite LS_cons by discriminate. rewrite Hs. cbn [mk qc tokc enc enc_tok RSh]. rewrite ?Str_app_assoc.
              eapply progress_trans. { apply KEEP_x. }
              change ([1;1;1] *> [0;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc true :: tD :: ty :: out') *> const 0).
              replace [1;0;1] with (mk true (startsD pend)) by (rewrite Hs; reflexivity).
              apply (IH pend true (tD :: ty :: out') w'); [cbn in Hl; lia|exact H].
           ++ cbn [andb isx] in H. rewrite LS_cons by discriminate.
              destruct (startsD pend) eqn:Hs; cbn [mk qc tokc enc enc_tok RSh]; rewrite ?Str_app_assoc.
              ** eapply progress_trans. { apply KEEP_yD. }
                 change ([0;1;1] *> [0;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc false :: tD :: ty :: out') *> const 0).
                 replace [1;1;0] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
                 apply (IH pend false (tD :: ty :: out') w'); [cbn in Hl; lia|exact H].
              ** eapply progress_trans. { apply KEEP_y. }
                 change ([0;1;1] *> [0;1] *> [1;1;1] *> enc out' *> const 0) with (enc (tokc false :: tD :: ty :: out') *> const 0).
                 replace [1;1;1] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
                 apply (IH pend false (tD :: ty :: out') w'); [cbn in Hl; lia|exact H].
      * cbn [lsw] in H. destruct (existsb isD pend) eqn:ED; [discriminate|].
        inversion H; subst. clear H. cbn [mk qc tokc enc enc_tok].
        eapply progress_evstep_trans. { apply WIPE_enter. }
        eapply evstep_trans. { apply wipe_run, ED. }
        unfold LS at 1. cbn [rsl]. change (const 0 <* [1;1;1] <* []) with (const 0 <* [1;1;1]).
        eapply evstep_trans. { apply progress_evstep, WIPE_wall. }
        unfold Cfg. apply evstep_refl'.
        rewrite enc_app. cbn [enc enc_tok].
        rewrite <- !Str_app_assoc. rewrite !app_assoc.
        rewrite <- (app_assoc [0;1;0;0;1;1;0]), wipe_cells. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma tstep_sim w w': tstep w = Some w' -> Cfg w -->+ Cfg w'.
Proof.
  unfold tstep. intro H.
  destruct (rev w) as [|[| |] [|s pend]] eqn:Ew; try discriminate.
  destruct (isD s) eqn:Es; [discriminate|].
  destruct (andb (isx s) (startsD pend)) eqn:Ex; [discriminate|].
  destruct (wfD (rev pend ++ [s])) eqn:Ewf; [|discriminate].
  assert (Hw: w = (rev pend ++ [s]) ++ [tD]).
  { rewrite <- (rev_involutive w), Ew. cbn. rewrite <- app_assoc. reflexivity. }
  subst w. unfold Cfg. rewrite enc_app. cbn [enc enc_tok]. rewrite app_nil_r, Str_app_assoc.
  eapply progress_evstep_trans. { apply RS_start. }
  change (const 0 <* [1;1;1]) with (LS []).
  eapply evstep_trans. { apply (RSWEEP_gen (length (rev pend ++ [s]))); [lia|exact Ewf|reflexivity]. }
  apply progress_evstep.
  rewrite rev_app_distr, rev_involutive. cbn [rev app]. rewrite app_nil_r.
  rewrite LS_cons by (destruct s; cbn in Es; congruence).
  destruct s; cbn in Es; try discriminate.
  - cbn in Ex. rewrite Ex. cbn [RSh].
    eapply progress_trans. { apply WALL_x. }
    change ([1;1;1;0;1] *> const 0) with (enc (tokc true :: [tD]) *> const 0).
    replace [1;0;1] with (mk true (startsD pend)) by (rewrite Ex; reflexivity).
    apply (lsw_sim (length pend) pend true [tD] w'); [lia|exact H].
  - destruct (startsD pend) eqn:Hs; cbn [RSh].
    + eapply progress_trans. { apply WALL_yD. }
      change ([0;1;1;0;1] *> const 0) with (enc (tokc false :: [tD]) *> const 0).
      replace [1;1;0] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
      apply (lsw_sim (length pend) pend false [tD] w'); [lia|exact H].
    + eapply progress_trans. { apply WALL_y. }
      change ([0;1;1;0;1] *> const 0) with (enc (tokc false :: [tD]) *> const 0).
      replace [1;1;1] with (mk false (startsD pend)) by (rewrite Hs; reflexivity).
      apply (lsw_sim (length pend) pend false [tD] w'); [lia|exact H].
Qed.


(** ************************** Part 2: the segment system never fails ************************** *)
Open Scope nat_scope.
Module Math.


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
Fixpoint den (L:list nat) : poly :=
  match L with [] => pzero | e::L' => pxor (fun i => Nat.eqb i e) (den L') end.

Lemma den_app L1 L2 : den (L1 ++ L2) == pxor (den L1) (den L2).
Proof. induction L1; cbn. { rewrite pxor_zero_l. reflexivity. } rewrite IHL1, pxor_assoc. reflexivity. Qed.

Lemma den_dup L : den (L ++ L) == pzero.
Proof. rewrite den_app, pxor_self. reflexivity. Qed.

Lemma den_perm L1 L2 : Permutation L1 L2 -> den L1 == den L2.
Proof.
  induction 1; cbn.
  - reflexivity.
  - rewrite IHPermutation. reflexivity.
  - rewrite <- !pxor_assoc. rewrite (pxor_comm (fun i => Nat.eqb i y)). reflexivity.
  - rewrite IHPermutation1. exact IHPermutation2.
Qed.

Lemma den_shl a L : den (map (fun e => e + a) L) == pshl a (den L).
Proof.
  induction L as [|e L IH]; cbn. { rewrite pshl_zero. reflexivity. }
  rewrite IH, pshl_xor. apply pxor_proper; [|reflexivity].
  intro i. unfold pshl. destruct (Nat.leb_spec a i), (Nat.eqb_spec i (e+a)), (Nat.eqb_spec (i-a) e); try lia; reflexivity.
Qed.

Lemma den_shr a L : Forall (fun e => a <= e) L -> den (map (fun e => e - a) L) == pshr a (den L).
Proof.
  induction 1 as [|e L He HL IH]; cbn. { intro; reflexivity. }
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

(** FIB2: segments, the segment map Phi, the parity polynomial N, and the segment step Gs.
    Words are in processing order (tape order reversed). A segment is a list of bits (x = true, y = false). *)

Ltac ptauto :=
  let i := fresh "i" in intro i; cbv [pxor mz pshl pbit pone pzero];
  repeat match goal with
         | |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b)
         | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
         end; try lia; try btauto.

Lemma mzn_0 n p : mzn n p 0 = p 0.
Proof. induction n; cbn; [reflexivity|]. unfold mz, pxor, pshl. cbn. rewrite IHn, xorb_false_r. reflexivity. Qed.

Lemma pshr_pshl a p : pshr a (pshl a p) == p.
Proof. intro i. unfold pshr, pshl. destruct (Nat.leb_spec a (i+a)); [|lia]. f_equal. lia. Qed.

Lemma pshl_inj a p q : pshl a p == pshl a q -> p == q.
Proof. intro H. rewrite <- (pshr_pshl a p), <- (pshr_pshl a q), H. reflexivity. Qed.

Lemma mzn_S n p : mzn (S n) p == mz (mzn n p).
Proof. reflexivity. Qed.

(** ===== Phi and parity ===== *)
Definition Phi (S:list bool) : list bool := map negb (pxl false S).
Fixpoint Phin (r:nat) (S:list bool) : list bool := match r with O => S | S r' => Phi (Phin r' S) end.

Lemma Phi_length S : length (Phi S) = length S.
Proof. unfold Phi. rewrite map_length, pxl_length. reflexivity. Qed.
Lemma Phin_length r S : length (Phin r S) = length S.
Proof. induction r; cbn; [reflexivity|]. rewrite Phi_length. exact IHr. Qed.

Lemma pxl_app c X Y : pxl c (X ++ Y) = pxl c X ++ pxl (xorb c (parity X)) Y.
Proof.
  revert c; induction X as [|a X IH]; intro c; cbn; [rewrite xorb_false_r; reflexivity|].
  rewrite IH. do 2 f_equal. rewrite xorb_assoc. reflexivity.
Qed.

Lemma Phi_app X Y : parity X = false -> Phi (X ++ Y) = Phi X ++ Phi Y.
Proof. intro H. unfold Phi. rewrite pxl_app, H, map_app. reflexivity. Qed.

Lemma pxl_last2 c S a : pxl c (S ++ [a]) = pxl c S ++ [xorb c (parity (S ++ [a]))].
Proof. rewrite pxl_app. cbn. rewrite parity_app. cbn. rewrite xorb_false_r, xorb_assoc. reflexivity. Qed.

Lemma Phi_last S a : exists P, Phi (S ++ [a]) = P ++ [negb (parity (S ++ [a]))].
Proof. exists (Phi S). unfold Phi. rewrite pxl_last2, map_app. reflexivity. Qed.

(** ===== sigma and N ===== *)
Fixpoint sig (S:list bool) : poly := match S with [] => pzero | a :: S' => pxor (pbit a) (mz (sig S')) end.
Definition NN (S:list bool) : poly := pxor (mz (sig S)) (pxor pone (mzn (length S) pone)).

#[global] Instance mzn_morph' n : Proper (peq ==> peq) (mzn n).
Proof. intros ? ? H; apply mzn_proper, H. Qed.

Lemma sig_0 S : sig S 0 = parity S.
Proof.
  induction S as [|a S IH]; [reflexivity|]. cbn [sig parity].
  change (pxor (pbit a) (mz (sig S)) 0) with (xorb (pbit a 0) (mz (sig S) 0)).
  assert (E: mz (sig S) 0 = sig S 0) by (unfold mz, pxor, pshl; cbn; apply xorb_false_r).
  rewrite E, IH. destruct a; reflexivity.
Qed.

Lemma NN_0 S : NN S 0 = parity S.
Proof.
  unfold NN, pxor at 1 2. rewrite mzn_0.
  assert (E: mz (sig S) 0 = sig S 0) by (unfold mz, pxor, pshl; cbn; apply xorb_false_r).
  rewrite E, sig_0. unfold pone. cbn. destruct (parity S); reflexivity.
Qed.

Lemma sig_pxl S : forall c, pshl 1 (sig (pxl c S)) ==
  pxor (sig S) (pxor (if xorb c (parity S) then mzn (length S) pone else pzero) (pbit c)).
Proof.
  induction S as [|a S IH]; intro c.
  - cbn. destruct c; cbn; ptauto.
  - cbn [pxl sig length parity]. rewrite pshl_xor, <- mz_shl, IH. rewrite <- xorb_assoc.
    destruct (xorb (xorb c a) (parity S)); cbn [mzn]; destruct c, a; cbn; ptauto.
Qed.

Lemma sig_negb P : sig (map negb P) == pxor (sig P) (sig (repeat true (length P))).
Proof.
  induction P as [|a P IH]; cbn; [ptauto|]. rewrite IH. destruct a; cbn; ptauto.
Qed.

Lemma sig_ones c : pshl 1 (sig (repeat true c)) == pxor (mzn c pone) pone.
Proof.
  induction c as [|c IH]; cbn [repeat sig mzn]; [ptauto|].
  rewrite pshl_xor, <- mz_shl, IH. ptauto.
Qed.

Lemma NN_Phi Z : pshl 1 (NN (Phi Z)) == pxor (NN Z) (if parity Z then mzn (S (length Z)) pone else pzero).
Proof.
  unfold NN. rewrite Phi_length. unfold Phi. rewrite sig_negb, pxl_length.
  rewrite !pshl_xor, <- mz_shl, pshl_xor, sig_pxl, sig_ones. cbn [xorb].
  cbn [mzn]. destruct (parity Z); ptauto.
Qed.

Lemma sig_app X Y : sig (X ++ Y) == pxor (sig X) (mzn (length X) (sig Y)).
Proof.
  induction X as [|a X IH]; cbn [app sig length mzn]; [ptauto|].
  rewrite IH, mz_xor. ptauto.
Qed.

Lemma NN_app X Y : NN (X ++ Y) == pxor (NN X) (mzn (length X) (NN Y)).
Proof.
  unfold NN. rewrite sig_app, app_length, !mzn_xor, mzn_mz, mzn_add, mz_xor. ptauto.
Qed.

Lemma NN_ones c : pshl 1 (NN (repeat true c)) == pxor (mzn c pone) pone.
Proof.
  unfold NN. rewrite repeat_length, !pshl_xor, <- mz_shl, sig_ones. ptauto.
Qed.

(** ===== Dormant and life lemmas ===== *)
Lemma dormant L Y Z : NN Z == pshl L Y -> forall t, t <= L ->
  NN (Phin t Z) == pshl (L - t) Y /\ (t < L -> parity (Phin t Z) = false).
Proof.
  intros HN t. induction t as [|t IH]; intro Ht.
  - cbn. rewrite Nat.sub_0_r. split; [exact HN|]. intro. rewrite <- NN_0, HN. unfold pshl.
    destruct (Nat.leb_spec L 0); [lia|reflexivity].
  - destruct IH as [IH1 IH2]; [lia|].
    assert (Hp: parity (Phin t Z) = false) by (apply IH2; lia).
    split.
    + cbn [Phin]. apply (pshl_inj 1). rewrite NN_Phi, Hp, pxor_zero_r, IH1.
      rewrite pshl_add. replace (1 + (L - S t)) with (L - t) by lia. reflexivity.
    + intro Hlt. rewrite <- NN_0. cbn [Phin].
      assert (H1: pshl 1 (NN (Phi (Phin t Z))) == pshl (L - t) Y).
      { rewrite NN_Phi, Hp, pxor_zero_r, IH1. reflexivity. }
      replace (L - t) with (1 + (L - S t)) in H1 by lia. rewrite <- pshl_add in H1.
      apply pshl_inj in H1. rewrite H1. unfold pshl. destruct (Nat.leb_spec (L - S t) 0); [lia|reflexivity].
Qed.

Lemma dormant_end L Y Z : NN Z == pshl L Y -> Y 0 = true ->
  NN (Phin L Z) == Y /\ parity (Phin L Z) = true.
Proof.
  intros HN HY. destruct (dormant L Y Z HN L (le_n L)) as [H1 _]. rewrite Nat.sub_diag, pshl_0 in H1.
  split; [exact H1|]. rewrite <- NN_0, H1. exact HY.
Qed.

Lemma life L R Z : NN Z == pxor (mzn (length Z) (pxor pone (pshl L pone))) (pshl L R) -> forall t, t <= L ->
  NN (Phin t Z) == pxor (mzn (length Z) (pxor pone (pshl (L - t) pone))) (pshl (L - t) R) /\
  (t < L -> parity (Phin t Z) = true).
Proof.
  intros HN t. induction t as [|t IH]; intro Ht.
  - cbn. rewrite Nat.sub_0_r. split; [exact HN|]. intro. rewrite <- NN_0, HN.
    unfold pxor at 1. rewrite mzn_0. unfold pxor, pone, pshl. cbn.
    destruct (Nat.leb_spec L 0); [lia|reflexivity].
  - destruct IH as [IH1 IH2]; [lia|].
    assert (Hp: parity (Phin t Z) = true) by (apply IH2; lia).
    assert (Hstep: NN (Phin (S t) Z) == pxor (mzn (length Z) (pxor pone (pshl (L - S t) pone))) (pshl (L - S t) R)).
    { cbn [Phin]. apply (pshl_inj 1). rewrite NN_Phi, Hp, IH1, Phin_length.
      set (m := length Z).
      assert (EB: pxor (pxor pone (pshl (L-t) pone)) (mz pone) == pxor (pshl 1 pone) (pshl (L-t) pone)) by ptauto.
      transitivity (pxor (mzn m (pxor (pxor pone (pshl (L-t) pone)) (mz pone))) (pshl (L-t) R)).
      - rewrite (mzn_xor m (pxor pone (pshl (L-t) pone)) (mz pone)).
        change (mzn (S m) pone) with (mz (mzn m pone)). rewrite <- mzn_mz. ptauto.
      - rewrite EB, pshl_xor, <- mzn_shl, pshl_xor, !pshl_add. replace (1 + (L - S t)) with (L - t) by lia.
        reflexivity. }
    split; [exact Hstep|].
    intro Hlt. rewrite <- NN_0, Hstep. unfold pxor at 1. rewrite mzn_0. unfold pxor, pone, pshl. cbn.
    destruct (Nat.leb_spec (L - S t) 0); [lia|reflexivity].
Qed.

Lemma life_end L R Z : NN Z == pxor (mzn (length Z) (pxor pone (pshl L pone))) (pshl L R) ->
  NN (Phin L Z) == R.
Proof.
  intro HN. destruct (life L R Z HN L (le_n L)) as [H _]. rewrite H, Nat.sub_diag, !pshl_0, pxor_self, mzn_zero, pxor_zero_l.
  reflexivity.
Qed.

(** ===== The segment step ===== *)
Fixpoint Gs (W : list (list bool)) : option (list (list bool)) :=
  match W with
  | [] => None
  | A0 :: W' =>
      match W' with
      | [] => Some (if parity A0 then [Phi A0 ++ [false]; []] else [Phi A0 ++ [true; true]])
      | S2 :: rest =>
          if parity A0 then option_map (cons (Phi A0)) (Gs W')
          else match rest with [] => Some [Phi A0 ++ repeat true (length S2 + 3)] | _ => None end
      end
  end.

Fixpoint Gsn (n:nat) (W:list (list bool)) : option (list (list bool)) :=
  match n with O => Some W | S n' => match Gsn n' W with Some W' => Gs W' | None => None end end.

Definition T (n:nat) := Gsn n [[]].

Lemma T_S n : T (S n) = match T n with Some W => Gs W | None => None end.
Proof. reflexivity. Qed.

Definition prepend (P:list bool) (W:list (list bool)) : list (list bool) :=
  match W with [] => [] | A0 :: W' => (P ++ A0) :: W' end.

Lemma Gs_nonempty W W' : Gs W = Some W' -> W' <> [].
Proof.
  revert W'. induction W as [|A0 W IH]; intros W' H; cbn in H; [discriminate|].
  destruct W as [|S2 rest].
  - inversion H; subst. destruct (parity A0); discriminate.
  - destruct (parity A0).
    + destruct (Gs (S2 :: rest)); cbn in H; inversion H; subst; discriminate.
    + destruct rest; inversion H; subst; discriminate.
Qed.

Lemma Gs_cons2 A B r : Gs (A :: B :: r) =
  if parity A then option_map (cons (Phi A)) (Gs (B :: r))
  else match r with [] => Some [Phi A ++ repeat true (length B + 3)] | _ => None end.
Proof. reflexivity. Qed.

Lemma Gs_prepend P W : parity P = false -> W <> [] -> Gs (prepend P W) = option_map (prepend (Phi P)) (Gs W).
Proof.
  intros HP HW. destruct W as [|A0 [|S2 rest]]; [congruence| |].
  - cbn. rewrite parity_app, HP, Phi_app by exact HP. cbn. destruct (parity A0); cbn; rewrite <- app_assoc; reflexivity.
  - cbn [prepend]. rewrite !Gs_cons2, parity_app, HP, Phi_app by exact HP. cbn [xorb].
    destruct (parity A0).
    + destruct (Gs (S2 :: rest)); reflexivity.
    + destruct rest; cbn; [rewrite <- app_assoc|]; reflexivity.
Qed.

Lemma Gs_head H W : parity H = true -> W <> [] -> Gs (H :: W) = option_map (cons (Phi H)) (Gs W).
Proof. intros HP HW. destruct W as [|S2 rest]; [congruence|]. cbn [Gs]. rewrite HP. reflexivity. Qed.

Lemma Gs_wipe H A0 : parity H = false -> Gs [H; A0] = Some [Phi H ++ repeat true (length A0 + 3)].
Proof. intro HP. cbn. rewrite HP. reflexivity. Qed.

(** size: total length + number of D's *)
Fixpoint size (W:list (list bool)) : nat :=
  match W with [] => 0 | [A0] => length A0 | A0 :: W' => length A0 + 1 + size W' end.

Lemma Gs_size W W' : Gs W = Some W' -> size W' = size W + 2.
Proof.
  revert W'. induction W as [|A0 W IH]; intros W' H; cbn in H; [discriminate|].
  destruct W as [|S2 rest].
  - inversion H; subst. destruct (parity A0); cbn; rewrite app_length, Phi_length; cbn; lia.
  - destruct (parity A0).
    + destruct (Gs (S2 :: rest)) as [W2|] eqn:E; cbn in H; inversion H; subst.
      specialize (IH W2 eq_refl). pose proof (Gs_nonempty _ _ E) as Hne.
      destruct W2 as [|A W2]; [congruence|]. cbn [size] in *. rewrite Phi_length.
      change (size (S2 :: rest)) with (size (S2 :: rest)) in IH. lia.
    + destruct rest; inversion H; subst. cbn. rewrite app_length, Phi_length, repeat_length. lia.
Qed.

Lemma T_size n W : T n = Some W -> size W = 2 * n.
Proof.
  revert W. induction n as [|n IH]; intros W H.
  - cbn in H. inversion H; subst. reflexivity.
  - rewrite T_S in H. destruct (T n) as [W0|]; [|discriminate]. apply Gs_size in H. rewrite H, (IH W0 eq_refl). lia.
Qed.

(** FIB2: constants of the epoch recursion and the two sparse-polynomial identities. *)

(** h_k = |head of epoch k|, d_k = suffix age when it dies. *)
Fixpoint hh (k:nat) : nat := match k with 0 => 3 | 1 => 5 | S (S k') => 2^(S (S (S k'))) + hh k' end.
Fixpoint dd (k:nat) : nat := match k with 0 => 0 | 1 => 0 | 2 => 1 | S (S k') => 2^(S k') + dd k' end.

Lemma pow_S m : 2^(S m) = 2 * 2^m.
Proof. reflexivity. Qed.
Lemma pow_ge1 m : 1 <= 2^m.
Proof. induction m; cbn; lia. Qed.
Lemma pow_mono a b : a <= b -> 2^a <= 2^b.
Proof. intro H. apply Nat.pow_le_mono_r; lia. Qed.
Lemma in_seq0 x n : In x (seq 0 n) -> x < n.
Proof. rewrite in_seq. lia. Qed.
Lemma seq_S_end n : seq 0 (S n) = seq 0 n ++ [n].
Proof. rewrite seq_S. reflexivity. Qed.
Lemma den_map_ext (f g : nat -> nat) (l : list nat) : (forall x, In x l -> f x = g x) -> den (map f l) == den (map g l).
Proof. intro H. rewrite (map_ext_in f g l H). reflexivity. Qed.

Lemma hh_SS k : hh (S (S k)) = 2^(S (S (S k))) + hh k.
Proof. reflexivity. Qed.
Lemma dd_SS k : 1 <= k -> dd (S (S k)) = 2^(S k) + dd k.
Proof. intro H. destruct k as [|k]; [lia|reflexivity]. Qed.

Lemma dd_closed k : 1 <= k -> 3 * dd k + (if Nat.even k then 5 else 4) = 2^(S k).
Proof.
  induction k as [k IH] using lt_wf_ind. intro Hk.
  destruct k as [|[|[|k]]]; [lia|reflexivity|reflexivity|].
  rewrite dd_SS by lia. specialize (IH (S k) ltac:(lia) ltac:(lia)).
  change (Nat.even (S (S (S k)))) with (Nat.even (S k)).
  rewrite !pow_S in *. destruct (Nat.even (S k)); lia.
Qed.

Lemma hh_dd k : 1 <= k -> hh k + 2 * dd k + 3 = 2^(S (S k)).
Proof.
  induction k as [k IH] using lt_wf_ind. intro Hk.
  destruct k as [|[|[|k]]]; [lia|reflexivity|reflexivity|].
  rewrite hh_SS, dd_SS by lia. specialize (IH (S k) ltac:(lia) ltac:(lia)).
  rewrite !pow_S in *. lia.
Qed.

Lemma dd_lt k : 1 <= k -> dd k < 2^k.
Proof.
  intro Hk. pose proof (dd_closed k Hk). rewrite pow_S in H. destruct (Nat.even k); lia.
Qed.

(** ===== exponent lists ===== *)
(** AL j = exponents of N_U / w^(L) for epoch k = j+1 (that is, Alist (j+1)). *)
Definition AL (j:nat) : list nat :=
  [0] ++ map (fun i => 2^j - 2^i) (seq 0 j) ++ (if Nat.even j then [2^j] else []) ++ [3 * 2^j].
Definition Dlist (k:nat) : list nat :=
  [0; 2^k] ++ map (fun i => 2^(S k) - 2^i) (seq 0 k) ++ (if Nat.even k then [2^(S k)] else []).

Definition NUf (k:nat) : poly := pshl (2^(pred k) - 1) (den (AL (pred k))).
Definition Df (k:nat) : poly := pxor (mzn (hh k) pone) (den (Dlist k)).

Lemma den_above0 L : Forall (fun x => 0 < x) L -> den L 0 = false.
Proof.
  induction 1 as [|x L Hx HL IH]; cbn; [reflexivity|]. unfold pxor. rewrite IH.
  destruct (Nat.eqb_spec 0 x); [lia|reflexivity].
Qed.

Lemma AL_0 j : den (AL j) 0 = true.
Proof.
  unfold AL. cbn [app den]. unfold pxor. cbn [Nat.eqb]. rewrite den_above0; [reflexivity|].
  rewrite !Forall_app. split; [|split].
  - rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx as [i [<- Hi]]. apply in_seq0 in Hi.
    pose proof (pow_mono (S i) j ltac:(lia)) as Hp. rewrite pow_S in Hp. pose proof (pow_ge1 i). lia.
  - destruct (Nat.even j); constructor; [pose proof (pow_ge1 j); lia|constructor].
  - constructor; [pose proof (pow_ge1 j); lia|constructor].
Qed.

Lemma den_cons0 L : den (0 :: L) 0 = negb (den L 0).
Proof. cbn [den]. unfold pxor. cbn. destruct (den L 0); reflexivity. Qed.

Lemma Df_0 k : Df k 0 = false.
Proof.
  unfold Df. unfold pxor at 1. rewrite mzn_0. unfold Dlist. cbn [app]. rewrite den_cons0, den_above0; [reflexivity|].
  constructor; [pose proof (pow_ge1 k); lia|]. rewrite Forall_app. split.
  - rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx as [i [<- Hi]]. apply in_seq0 in Hi.
    pose proof (pow_mono i k ltac:(lia)). rewrite pow_S. pose proof (pow_ge1 k). lia.
  - destruct (Nat.even k); constructor; [pose proof (pow_ge1 (S k)); lia|constructor].
Qed.

Lemma pone_den2 : pone == den [0].
Proof. intro i. cbn. unfold pxor, pzero, pone. rewrite xorb_false_r. reflexivity. Qed.
Lemma pshl_pone a : pshl a pone == den [a].
Proof. intro i. cbn. unfold pxor, pzero, pone, pshl. rewrite xorb_false_r.
  destruct (Nat.leb_spec a i), (Nat.eqb_spec i a), (Nat.eqb_spec (i - a) 0); try lia; reflexivity. Qed.

(** ===== merge identity ===== *)
Lemma merge_core k :
  pxor (den (Dlist k)) (pxor pone (pshl (2^(S (S k))) pone)) == pshl (2^k) (den (AL k)).
Proof.
  rewrite pshl_pone, pone_den2, <- den_shl. unfold AL, Dlist. rewrite !map_app. cbn [map].
  set (K := 2^k).
  assert (HM: den (map (fun e => e + K) (map (fun i => K - 2^i) (seq 0 k))) == den (map (fun i => 2^(S k) - 2^i) (seq 0 k))).
  { rewrite map_map. apply den_map_ext. intros i Hi. apply in_seq0 in Hi. pose proof (pow_mono i k ltac:(lia)).
    rewrite pow_S. fold K. lia. }
  rewrite !den_app. rewrite HM.
  set (M := map (fun i => 2^(S k) - 2^i) (seq 0 k)).
  replace (0 + K) with K by lia. replace (3 * K + K) with (2^(S (S k))) by (rewrite !pow_S; fold K; lia).
  replace (2^(S k)) with (K + K) by (rewrite pow_S; fold K; lia). fold M.
  destruct (Nat.even k); cbn [map den]; intro i; unfold pxor, pzero;
    destruct (den M i), (Nat.eqb i 0), (Nat.eqb i K), (Nat.eqb i (K+K)), (Nat.eqb i (2^(S (S k)))); reflexivity.
Qed.

(** ===== birth identity ===== *)
Lemma birth_core j :
  pxor (den (AL (S j))) (pxor (den (Dlist j)) (pshl (2^(S (S (S j)))) (den (Dlist j)))) ==
  pshl (2^(S j)) (den (Dlist (S (S j)))).
Proof.
  rewrite <- !den_shl. unfold AL, Dlist.
  rewrite (seq_S_end j), (seq_S_end (S j)), (seq_S_end j), !map_app, !map_map. cbn [map app].
  change (Nat.even (S (S j))) with (Nat.even j).
  replace (Nat.even (S j)) with (negb (Nat.even j)) by (rewrite Nat.even_succ, <- Nat.negb_even; reflexivity).
  pose proof (pow_ge1 j) as Hj.
  assert (HA: den (map (fun x => 2^(S (S (S j))) - 2^x + 2^(S j)) (seq 0 j)) ==
              den (map (fun x => 2^(S j) - 2^x + 2^(S (S (S j)))) (seq 0 j))).
  { apply den_map_ext. intros x Hx. apply in_seq0 in Hx. pose proof (pow_mono x j ltac:(lia)). rewrite !pow_S. lia. }
  replace (2^(S j) - 2^j) with (2^j) by (rewrite pow_S; lia).
  replace (0 + 2^(S (S (S j)))) with (2^(S (S (S j)))) by lia.
  replace (0 + 2^(S j)) with (2^(S j)) by lia.
  replace (2^(S (S j)) + 2^(S j)) with (3 * 2^(S j)) by (rewrite !pow_S; lia).
  replace (2^(S (S (S j))) - 2^j + 2^(S j)) with (2^j + 2^(S (S (S j)))) by (rewrite !pow_S; lia).
  replace (2^(S (S (S j))) - 2^(S j) + 2^(S j)) with (2^(S (S (S j)))) by (rewrite !pow_S; lia).
  replace (2^(S (S (S j))) + 2^(S j)) with (2^(S j) + 2^(S (S (S j)))) by lia.
  set (Q1 := map (fun x => 2^(S (S (S j))) - 2^x + 2^(S j)) (seq 0 j)) in *.
  set (P1 := map (fun i => 2^(S j) - 2^i) (seq 0 j)) in *.
  set (P2 := map (fun x => 2^(S j) - 2^x + 2^(S (S (S j)))) (seq 0 j)) in *.
  clearbody P1 P2 Q1.
  set (a := 2^j) in *. set (b := 2^(S j)) in *. set (c := 2^(S (S (S j)))) in *.
  clearbody a b c.
  destruct (Nat.even j); cbn [negb map app]; try replace (c + b) with (b + c) by lia;
    rewrite ?den_app; cbn [den]; rewrite ?den_app, ?HA; cbn [den];
    intro i; unfold pxor, pzero;
    destruct (den P1 i), (den P2 i), (Nat.eqb i 0), (Nat.eqb i a), (Nat.eqb i b), (Nat.eqb i (3*b)),
             (Nat.eqb i c), (Nat.eqb i (a + c)), (Nat.eqb i (b + c)); reflexivity.
Qed.

Lemma birth_identity j :
  pxor (den (AL (S j))) (mzn (2^(S (S (S j)))) (Df j)) ==
  pxor (mzn (hh (S (S j))) (pxor pone (pshl (2^(S j)) pone))) (pshl (2^(S j)) (Df (S (S j)))).
Proof.
  unfold Df. rewrite (mzn_xor (2^(S (S (S j))))), <- mzn_add, <- hh_SS, frob.
  rewrite (mzn_xor (hh (S (S j)))), mzn_shl, !pshl_xor, <- birth_core.
  set (Z := pshl (2^(S (S (S j)))) (den (Dlist j))). set (V := pshl (2^(S j)) (mzn (hh (S (S j))) pone)).
  set (H := mzn (hh (S (S j))) pone). set (X := den (AL (S j))). set (Y := den (Dlist j)).
  intro i. unfold pxor. destruct (X i), (Y i), (Z i), (V i), (H i); reflexivity.
Qed.

(** FIB2: the epoch induction. T n is never None. *)

Lemma T_nonempty n W : T n = Some W -> W <> [].
Proof.
  destruct n as [|n]; intro H.
  - cbn in H. inversion H; subst. discriminate.
  - rewrite T_S in H. destruct (T n); [|discriminate]. eapply Gs_nonempty, H.
Qed.

Definition Pk (k:nat) : Prop :=
  (forall n, n <= 2^k -> T n <> None) /\
  (exists U, T (2^k) = Some [U] /\ length U = 2^(S k) /\ NN U == NUf k) /\
  (exists Dy Sd, T (2^k - 1) = Some [Dy; Sd] /\ T (dd (pred k)) = Some [Sd] /\
                 length Dy = hh (pred k) /\ NN Dy == Df (pred k)).

Lemma lift k U : 1 <= k -> (forall n, n <= 2^k -> T n <> None) -> T (2^k) = Some [U] -> NN U == NUf k ->
  forall j, j <= 2^(pred k) - 1 -> T (2^k + j) = option_map (prepend (Phin j U)) (T j).
Proof.
  intros Hk Ha HU HN. unfold NUf in HN.
  pose proof (dormant _ _ _ HN) as Hd.
  induction j as [|j IH]; intro Hj.
  - rewrite Nat.add_0_r, HU. cbn. rewrite app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r, T_S, IH by lia.
    assert (Hjk: j <= 2^k).
    { destruct k as [|k']; [lia|]. cbn [pred] in Hj. rewrite pow_S. pose proof (pow_ge1 k'). lia. }
    destruct (T j) as [Wj|] eqn:ETj; [|exfalso; apply (Ha j Hjk), ETj].
    cbn [option_map]. rewrite T_S, ETj.
    rewrite Gs_prepend.
    + reflexivity.
    + apply (proj2 (Hd j ltac:(lia))). lia.
    + eapply T_nonempty, ETj.
Qed.

Lemma pow_pos k : 0 < 2^k.
Proof. pose proof (pow_ge1 k). lia. Qed.

Lemma step j : 1 <= j -> Pk (S j) -> Pk (S (S j)) -> Pk (S (S (S j))).
Proof.
  intros Hj1 [Ha1 [[U1 [HU1 [HlU1 HNU1]]] [Dy2 [Sd' [HT2 [HTd2 [HlDy2 HNDy2]]]]]]]
         [Ha [[U [HU [HlU HNU]]] _]].
  cbn [pred] in *.
  set (K := 2^(S (S j))).
  set (L := 2^(S j) - 1).
  assert (HK: K = 2 * 2^(S j)) by reflexivity.
  assert (HSj: 2^(S j) = 2 * 2^j) by reflexivity.
  pose proof (pow_ge1 j) as Hpj.
  (* lift phase *)
  pose proof (lift (S (S j)) U ltac:(lia) Ha HU HNU) as Hlift. cbn [pred] in Hlift.
  assert (HTL: T (K + L) = Some [Phin L U ++ Dy2; Sd']).
  { unfold K. rewrite (Hlift L ltac:(unfold L; lia)). unfold L. rewrite HT2. reflexivity. }
  (* the head at birth *)
  unfold NUf in HNU. cbn [pred] in HNU.
  destruct (dormant_end _ _ _ HNU (AL_0 (S j))) as [HNX _].
  fold L in HNX.
  set (Hc := Phin L U ++ Dy2).
  assert (HlHc: length Hc = hh (S (S j))).
  { unfold Hc. rewrite app_length, Phin_length, HlU, HlDy2. rewrite hh_SS. reflexivity. }
  assert (HNHc: NN Hc == pxor (mzn (length Hc) (pxor pone (pshl (2^(S j)) pone))) (pshl (2^(S j)) (Df (S (S j))))).
  { rewrite HlHc. unfold Hc. rewrite NN_app, Phin_length, HlU, HNX, HNDy2. apply birth_identity. }
  pose proof (life _ _ _ HNHc) as Hlife.
  pose proof (life_end _ _ _ HNHc) as HNDy.
  (* head run *)
  assert (Hdk: dd (S (S j)) = 2^(S j) + dd j) by (apply dd_SS; lia).
  assert (Hddk: dd (S (S j)) < K) by (unfold K; apply dd_lt; lia).
  assert (Hrun: forall t, t <= 2^(S j) -> T (K + L + t) = option_map (cons (Phin t Hc)) (T (dd j + t))).
  { induction t as [|t IHt]; intro Ht.
    - rewrite !Nat.add_0_r, HTL, HTd2. reflexivity.
    - rewrite Nat.add_succ_r, T_S, IHt by lia.
      destruct (T (dd j + t)) as [W|] eqn:EW.
      2:{ exfalso. apply (Ha (dd j + t)); [unfold K in Hddk; lia|exact EW]. }
      cbn [option_map]. rewrite Nat.add_succ_r, T_S, EW.
      rewrite Gs_head; [reflexivity| |eapply T_nonempty, EW].
      apply (proj2 (Hlife t ltac:(lia))). lia. }
  (* the suffix at death is a single segment *)
  assert (HTdk: T (dd (S (S j))) = Some [Phin (dd j) U1 ++ Sd']).
  { rewrite Hdk. rewrite (lift (S j) U1 ltac:(lia) Ha1 HU1 HNU1 (dd j)).
    - rewrite HTd2. reflexivity.
    - cbn [pred]. pose proof (dd_lt j Hj1). lia. }
  set (Sd := Phin (dd j) U1 ++ Sd') in *.
  set (Dyk := Phin (2^(S j)) Hc) in *.
  assert (HTdeath: T (2^(S (S (S j))) - 1) = Some [Dyk; Sd]).
  { replace (2^(S (S (S j))) - 1) with (K + L + 2^(S j)) by (rewrite (pow_S (S (S j))); fold K; unfold L; lia).
    rewrite (Hrun (2^(S j)) (le_n _)). replace (dd j + 2^(S j)) with (dd (S (S j))) by lia. rewrite HTdk. reflexivity. }
  assert (HlDyk: length Dyk = hh (S (S j))) by (unfold Dyk; rewrite Phin_length; exact HlHc).
  assert (HpDyk: parity Dyk = false) by (rewrite <- NN_0, HNDy; apply Df_0).
  (* merge *)
  set (U' := Phi Dyk ++ repeat true (length Sd + 3)).
  assert (HTU': T (2^(S (S (S j)))) = Some [U']).
  { replace (2^(S (S (S j)))) with (S (2^(S (S (S j))) - 1)) by (pose proof (pow_ge1 (S (S (S j)))); lia).
    rewrite T_S, HTdeath. apply Gs_wipe, HpDyk. }
  assert (HlSd: length Sd = 2 * dd (S (S j))) by (pose proof (T_size _ _ HTdk) as HS; cbn in HS; exact HS).
  assert (HlU': length U' = 2^(S (S (S (S j))))).
  { unfold U'. rewrite app_length, Phi_length, repeat_length, HlDyk, HlSd. pose proof (hh_dd (S (S j)) ltac:(lia)). lia. }
  assert (HNU': NN U' == NUf (S (S (S j)))).
  { apply (pshl_inj 1). unfold U', NUf. cbn [pred].
    rewrite NN_app, Phi_length, HlDyk, pshl_xor, NN_Phi, HpDyk, pxor_zero_r, HNDy.
    rewrite <- mzn_shl, NN_ones, mzn_xor, <- (mzn_add (hh (S (S j)))), pshl_add.
    replace (1 + (2^(S (S j)) - 1)) with (2^(S (S j))) by (pose proof (pow_ge1 (S (S j))); lia).
    replace (hh (S (S j)) + (length Sd + 3)) with (2^(S (S (S (S j))))) by (rewrite HlSd; pose proof (hh_dd (S (S j)) ltac:(lia)); lia).
    rewrite frob, <- merge_core. unfold Df.
    set (H := mzn (hh (S (S j))) pone). set (D := den (Dlist (S (S j)))). set (P := pshl (2^(S (S (S (S j))))) pone).
    intro i. unfold pxor. destruct (H i), (D i), (P i), (pone i); reflexivity. }
  (* assemble *)
  clearbody Hc Dyk Sd U'.
  unfold K, L in *. clear HK.
  split; [|split].
  - intros n Hn.
    destruct (Nat.le_gt_cases n (2^(S (S j)))) as [H1|H1]; [apply Ha, H1|].
    destruct (Nat.le_gt_cases n (2^(S (S j)) + (2^(S j) - 1))) as [H2|H2].
    + replace n with (2^(S (S j)) + (n - 2^(S (S j)))) by lia. rewrite (Hlift (n - 2^(S (S j)))) by lia.
      destruct (T (n - 2^(S (S j)))) eqn:E; [discriminate|]. exfalso.
      apply (Ha (n - 2^(S (S j)))); [lia|exact E].
    + destruct (Nat.le_gt_cases n (2^(S (S (S j))) - 1)) as [H3|H3].
      * rewrite (pow_S (S (S j))) in H3.
        replace n with (2^(S (S j)) + (2^(S j) - 1) + (n - (2^(S (S j)) + (2^(S j) - 1)))) by lia.
        rewrite (Hrun (n - (2^(S (S j)) + (2^(S j) - 1)))) by (rewrite (pow_S (S j)) in *; lia).
        destruct (T (dd j + (n - (2^(S (S j)) + (2^(S j) - 1))))) eqn:E; [discriminate|]. exfalso.
        apply (Ha (dd j + (n - (2^(S (S j)) + (2^(S j) - 1))))); [|exact E].
        rewrite (pow_S (S j)) in *. lia.
      * replace n with (2^(S (S (S j)))) by lia. rewrite HTU'. discriminate.
  - exists U'. split; [exact HTU'|]. split; [exact HlU'|exact HNU'].
  - exists Dyk, Sd. cbn [pred]. split; [exact HTdeath|]. split; [exact HTdk|]. split; [exact HlDyk|exact HNDy].
Qed.

(** ===== Base cases by computation ===== *)
Lemma mzn_pone_deg m : forall i, m < i -> mzn m pone i = false.
Proof.
  induction m as [|m IH]; intros i Hi.
  - cbn [mzn]. unfold pone. destruct (Nat.eqb_spec i 0); [lia|reflexivity].
  - cbn [mzn]. unfold mz, pxor, pshl. rewrite IH by lia.
    destruct (Nat.leb_spec 1 i); [rewrite IH by lia|]; reflexivity.
Qed.

Lemma sig_deg Sg : forall i, length Sg <= i -> sig Sg i = false.
Proof.
  induction Sg as [|a Sg IH]; intros i Hi; [reflexivity|].
  cbn [length] in Hi. change (sig (a :: Sg) i) with (xorb (pbit a i) (mz (sig Sg) i)).
  unfold mz, pxor, pshl. rewrite (IH i) by lia. destruct (Nat.leb_spec 1 i); [|lia]. rewrite (IH (i-1)) by lia.
  unfold pbit, pone, pzero. destruct a; [destruct (Nat.eqb_spec i 0); [lia|]|]; reflexivity.
Qed.

Lemma NN_deg Sg i : length Sg < i -> NN Sg i = false.
Proof.
  intro Hi. cbv [NN pxor mz pshl]. rewrite (sig_deg Sg i) by lia. rewrite (mzn_pone_deg _ i) by lia.
  destruct (Nat.leb_spec 1 i); [|lia]. rewrite (sig_deg Sg (i-1)) by lia.
  unfold pone. destruct (Nat.eqb_spec i 0); [lia|reflexivity].
Qed.

Lemma den_below i L : Forall (fun x => x < i) L -> den L i = false.
Proof.
  induction 1 as [|x L Hx HL IH]; cbn; [reflexivity|]. unfold pxor. rewrite IH.
  destruct (Nat.eqb_spec i x); [lia|reflexivity].
Qed.

Lemma peq_check p q N : (forall i, N <= i -> p i = false) -> (forall i, N <= i -> q i = false) ->
  forallb (fun i => Bool.eqb (p i) (q i)) (seq 0 N) = true -> p == q.
Proof.
  intros Hp Hq HC i. destruct (Nat.lt_ge_cases i N) as [Hi|Hi].
  - rewrite forallb_forall in HC. specialize (HC i ltac:(apply in_seq; lia)). apply Bool.eqb_prop in HC. exact HC.
  - rewrite Hp, Hq by exact Hi. reflexivity.
Qed.

Lemma bound_list L N : forallb (fun x => Nat.ltb x N) L = true -> forall i, N <= i -> Forall (fun x => x < i) L.
Proof.
  intros H i Hi. rewrite Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx).
  apply Nat.ltb_lt in H. lia.
Qed.

Lemma NUf_deg k N : forallb (fun x => Nat.ltb (x + (2^(pred k) - 1)) N) (AL (pred k)) = true ->
  forall i, N <= i -> NUf k i = false.
Proof.
  intros H i Hi. unfold NUf. rewrite <- den_shl. apply den_below. rewrite Forall_forall. intros x Hx.
  apply in_map_iff in Hx as [y [<- Hy]]. rewrite forallb_forall in H. specialize (H y Hy). apply Nat.ltb_lt in H. lia.
Qed.

Lemma Df_deg k N : hh k < N -> forallb (fun x => Nat.ltb x N) (Dlist k) = true -> forall i, N <= i -> Df k i = false.
Proof.
  intros H1 H2 i Hi. unfold Df, pxor. rewrite mzn_pone_deg by lia. rewrite den_below; [reflexivity|].
  apply (bound_list _ N H2 i Hi).
Qed.

Definition okb (o:option (list (list bool))) : bool := match o with Some _ => true | None => false end.

Lemma defined_upto N : forallb (fun n => okb (T n)) (seq 0 (S N)) = true -> forall n, n <= N -> T n <> None.
Proof.
  intros H n Hn. rewrite forallb_forall in H. specialize (H n ltac:(apply in_seq; lia)).
  destruct (T n); [discriminate|discriminate H].
Qed.

Definition seg1 (o:option (list (list bool))) : list bool := match o with Some [U] => U | _ => [] end.
Definition segA (o:option (list (list bool))) : list bool := match o with Some [X1; _] => X1 | _ => [] end.
Definition segB (o:option (list (list bool))) : list bool := match o with Some [_; X2] => X2 | _ => [] end.

Lemma base2 : Pk 2.
Proof.
  split; [|split].
  - apply defined_upto. vm_compute. reflexivity.
  - exists (seg1 (T 4)). split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    apply (peq_check _ _ 9).
    + intros i Hi. apply NN_deg. vm_compute. lia.
    + apply NUf_deg. vm_compute. reflexivity.
    + vm_compute. reflexivity.
  - exists (segA (T 3)), (segB (T 3)). cbn [pred].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    apply (peq_check _ _ 6).
    + intros i Hi. apply NN_deg. vm_compute. lia.
    + apply Df_deg; [vm_compute; lia|vm_compute; reflexivity].
    + vm_compute. reflexivity.
Qed.

Lemma base3 : Pk 3.
Proof.
  split; [|split].
  - apply defined_upto. vm_compute. reflexivity.
  - exists (seg1 (T 8)). split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    apply (peq_check _ _ 17).
    + intros i Hi. apply NN_deg. vm_compute. lia.
    + apply NUf_deg. vm_compute. reflexivity.
    + vm_compute. reflexivity.
  - exists (segA (T 7)), (segB (T 7)). cbn [pred].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    apply (peq_check _ _ 12).
    + intros i Hi. apply NN_deg. vm_compute. lia.
    + apply Df_deg; [vm_compute; lia|vm_compute; reflexivity].
    + vm_compute. reflexivity.
Qed.

Lemma Pk_all k : 2 <= k -> Pk k.
Proof.
  induction k as [k IH] using lt_wf_ind. intro Hk.
  destruct k as [|[|[|[|j]]]]; try lia.
  - exact base2.
  - exact base3.
  - apply (step (S j)); [lia|apply IH; lia|apply IH; lia].
Qed.

Theorem T_total n : T n <> None.
Proof.
  destruct (Pk_all (S (S n)) ltac:(lia)) as [Ha _]. apply Ha.
  pose proof (Nat.pow_gt_lin_r 2 (S (S n)) ltac:(lia)). lia.
Qed.

End Math.
Import Math.

(** ************************** Part 3: bridge and the theorem ************************** *)
Open Scope list_scope.
Open Scope nat_scope.


(** FIB2: bridge between the tape-level token step and the segment step, and the final theorem. *)

Definition b2t (b:bool) : tok := if b then tx else ty.

Fixpoint flat (W:list (list bool)) : list tok :=
  match W with
  | [] => []
  | Sa :: W' => match W' with [] => map b2t Sa | _ => map b2t Sa ++ tD :: flat W' end
  end.

Definition encw (W:list (list bool)) : list tok := rev (tD :: flat W).

Fixpoint lastb (d:bool) (Sb:list bool) : bool := match Sb with [] => d | b :: B' => lastb b B' end.

(** every non-last segment is nonempty and ends in false (y) *)
Definition endy (Sa:list bool) : bool := match Sa with [] => false | _ => negb (lastb false Sa) end.
Fixpoint invb (W:list (list bool)) : bool :=
  match W with
  | [] => true
  | Sa :: W' => match W' with [] => true | _ => endy Sa && invb W' end
  end.

Definition firstne (W:list (list bool)) : bool :=
  match W with (_ :: _) :: _ => true | _ => false end.

Lemma lastb_indep Sb d d' : Sb <> [] -> lastb d Sb = lastb d' Sb.
Proof. destruct Sb; [congruence|reflexivity]. Qed.

(** ===== the left sweep on one segment ===== *)
Lemma lsw_seg Sb : forall c R out,
  (startsD R = true -> lastb false Sb = false) ->
  lsw c (map b2t Sb ++ R) out = lsw (xorb c (parity Sb)) R (rev (map b2t (map negb (pxl c Sb))) ++ out).
Proof.
  induction Sb as [|b Sb IH]; intros c R out HR.
  - cbn. rewrite xorb_false_r. reflexivity.
  - assert (HR': startsD R = true -> lastb false Sb = false).
    { intro H. specialize (HR H). destruct Sb as [|b' B']; [reflexivity|]. cbn in HR |- *. exact HR. }
    assert (Hchk: andb (isx (b2t b)) (startsD (map b2t Sb ++ R)) = false).
    { destruct Sb as [|b' B'].
      - cbn in HR |- *. destruct (startsD R) eqn:E; [|destruct b; reflexivity].
        specialize (HR eq_refl). subst b. reflexivity.
      - cbn. destruct b'; destruct b; reflexivity. }
    cbn [map app pxl parity].
    destruct b; cbn [b2t] in *.
    + cbn [lsw]. rewrite Hchk. cbn [isx]. rewrite IH by exact HR'.
      cbn [map rev]. rewrite <- app_assoc. cbn [app]. rewrite xorb_assoc.
      destruct c; reflexivity.
    + cbn [lsw]. cbn [isx andb]. rewrite xorb_false_r. rewrite IH by exact HR'.
      cbn [map rev]. rewrite <- app_assoc. cbn [app]. rewrite xorb_false_l.
      destruct c; reflexivity.
Qed.

Lemma rev_map_repeat n : rev (map b2t (repeat true n)) = repeat tx n.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat map rev]. rewrite IH. cbn [b2t].
  clear IH. induction n as [|n IHn]; [reflexivity|]. cbn [repeat app]. rewrite IHn. reflexivity.
Qed.

Lemma flat_cons Sa W : W <> [] -> flat (Sa :: W) = map b2t Sa ++ tD :: flat W.
Proof. destruct W; [congruence|reflexivity]. Qed.

Lemma isD_b2t_free Sb : existsb isD (map b2t Sb) = false.
Proof. induction Sb as [|b Sb IH]; [reflexivity|]. cbn. rewrite IH. destruct b; reflexivity. Qed.

Lemma lsw_Gs W : W <> [] -> invb W = true -> forall out,
  lsw false (flat W) out = option_map (fun W' => rev (flat W') ++ out) (Gs W).
Proof.
  induction W as [|Sa W IH]; intros HW Hinv out; [congruence|].
  destruct W as [|Sb rest].
  - (* single segment *)
    cbn [flat Gs]. rewrite <- (app_nil_r (map b2t Sa)). rewrite lsw_seg by (intro H; discriminate H).
    rewrite xorb_false_l. cbn [lsw option_map]. f_equal.
    unfold Phi. destruct (parity Sa); cbn [flat]; rewrite !map_app, !rev_app_distr; cbn [rev map app b2t]; reflexivity.
  - cbn [invb] in Hinv. apply andb_true_iff in Hinv as [HA Hinv'].
    assert (HAne: Sa <> []) by (destruct Sa; [discriminate|congruence]).
    assert (HAl: lastb false Sa = false) by (destruct Sa; [congruence|]; cbn in HA |- *; destruct (lastb b Sa); [discriminate|reflexivity]).
    rewrite flat_cons by discriminate.
    rewrite lsw_seg by (intro; exact HAl). rewrite xorb_false_l.
    fold (Phi Sa).
    rewrite Gs_cons2. destruct (parity Sa) eqn:EpA.
    + (* keep *)
      assert (Hk: lsw true (tD :: flat (Sb :: rest)) (rev (map b2t (Phi Sa)) ++ out) =
                  lsw false (flat (Sb :: rest)) (tD :: rev (map b2t (Phi Sa)) ++ out)).
      { destruct rest as [|Sc rest'].
        - cbn [flat]. destruct Sb as [|b B']; [reflexivity|]. destruct b; reflexivity.
        - cbn [invb] in Hinv'. apply andb_true_iff in Hinv' as [HB _].
          destruct Sb as [|b B']; [discriminate|]. destruct b; reflexivity. }
      rewrite Hk, IH by (discriminate || exact Hinv').
      destruct (Gs (Sb :: rest)) as [W'|] eqn:EG; [|reflexivity]. cbn [option_map]. f_equal.
      rewrite flat_cons by (eapply Gs_nonempty, EG). cbn [rev]. rewrite rev_app_distr. cbn [rev].
      rewrite <- !app_assoc. reflexivity.
    + (* wipe *)
      cbn [lsw]. destruct rest as [|Sc rest'].
      * cbn [flat]. rewrite isD_b2t_free. cbn [option_map]. f_equal. rewrite map_length.
        cbn [flat]. rewrite map_app, rev_app_distr, rev_map_repeat, <- app_assoc. reflexivity.
      * rewrite flat_cons by discriminate. rewrite existsb_app. cbn [existsb isD]. rewrite orb_true_r. reflexivity.
Qed.

(** ===== well-formedness for the right sweep ===== *)
Fixpoint wfP (v:list tok) : bool :=
  match v with
  | [] => true
  | ty :: v' => match v' with tD :: v'' => wfP v'' | _ => wfP v' end
  | tD :: _ => false
  | tx :: v' => wfP v'
  end.

Lemma wfD_app n : forall x y, length x <= n -> wfD x = true -> wfD (x ++ y) = wfD y.
Proof.
  induction n as [|n IH]; intros x y Hl Hx.
  - destruct x; [reflexivity|cbn in Hl; lia].
  - destruct x as [|[| |] x]; [reflexivity| | |].
    + cbn [app wfD] in *. apply IH; [cbn in Hl; lia|exact Hx].
    + cbn [app wfD] in *. apply IH; [cbn in Hl; lia|exact Hx].
    + destruct x as [|[| |] x]; cbn in Hx; try discriminate.
      cbn [app wfD]. apply IH; [cbn in Hl; lia|exact Hx].
Qed.

Lemma wfP_wfD n : forall v, length v <= n -> wfP v = true -> wfD (rev v) = true.
Proof.
  induction n as [|n IH]; intros v Hl Hv.
  - destruct v; [reflexivity|cbn in Hl; lia].
  - destruct v as [|t v]; [reflexivity|]. destruct t.
    + cbn [rev]. rewrite (wfD_app _ (rev v) [tx] (le_n _)); [reflexivity|].
      apply IH; [cbn in Hl; lia|exact Hv].
    + destruct v as [|t' v']; [reflexivity|]. destruct t'.
      * change (rev (ty :: tx :: v')) with (rev (tx :: v') ++ [ty]).
        rewrite (wfD_app _ (rev (tx :: v')) [ty] (le_n _)); [reflexivity|].
        apply IH; [cbn in Hl |- *; lia|exact Hv].
      * change (rev (ty :: ty :: v')) with (rev (ty :: v') ++ [ty]).
        rewrite (wfD_app _ (rev (ty :: v')) [ty] (le_n _)); [reflexivity|].
        apply IH; [cbn in Hl |- *; lia|exact Hv].
      * change (rev (ty :: tD :: v')) with ((rev v' ++ [tD]) ++ [ty]). rewrite <- app_assoc.
        change ([tD] ++ [ty]) with [tD; ty].
        rewrite (wfD_app _ (rev v') [tD; ty] (le_n _)); [reflexivity|].
        apply IH; [cbn in Hl |- *; lia|exact Hv].
    + discriminate.
Qed.

Lemma wfP_seg Sa v : Sa <> [] -> lastb false Sa = false -> wfP (map b2t Sa ++ tD :: v) = wfP v.
Proof.
  induction Sa as [|a Sa IH]; intros Hne Hl; [congruence|].
  destruct Sa as [|a' A'].
  - cbn in Hl. subst a. reflexivity.
  - cbn [map app]. rewrite <- IH by (discriminate || exact Hl).
    destruct a, a'; reflexivity.
Qed.

Lemma wfP_nod Sa : wfP (map b2t Sa) = true.
Proof.
  induction Sa as [|a Sa IH]; [reflexivity|]. destruct a; cbn [map b2t wfP]; [exact IH|].
  destruct Sa as [|[] A']; exact IH.
Qed.

Lemma wfP_flat W : invb W = true -> wfP (flat W) = true.
Proof.
  induction W as [|Sa W IH]; intro H; [reflexivity|].
  destruct W as [|Sb rest]; [apply wfP_nod|].
  cbn [invb] in H. apply andb_true_iff in H as [HA H'].
  assert (HAne: Sa <> []) by (destruct Sa; [discriminate|congruence]).
  assert (HAl: lastb false Sa = false) by (destruct Sa; [congruence|]; cbn in HA |- *; destruct (lastb b Sa); [discriminate|reflexivity]).
  rewrite flat_cons by discriminate. rewrite wfP_seg by assumption. apply IH, H'.
Qed.

(** ===== tstep on encoded words ===== *)
Lemma tstep_encw W : invb W = true -> firstne W = true -> tstep (encw W) = option_map encw (Gs W).
Proof.
  intros Hinv Hf. unfold tstep, encw. rewrite rev_involutive.
  destruct W as [|[|a Sa] W]; try discriminate.
  pose proof (lsw_Gs ((a :: Sa) :: W) ltac:(discriminate) Hinv [tD]) as HL.
  assert (Hwf: wfP (flat ((a :: Sa) :: W)) = true) by (apply wfP_flat, Hinv).
  assert (Ev: exists pend, flat ((a :: Sa) :: W) = b2t a :: pend) by (destruct W; eexists; reflexivity).
  destruct Ev as [pend Ev]. rewrite Ev in HL, Hwf |- *.
  assert (Hwf': wfD (rev pend ++ [b2t a]) = true).
  { change (rev pend ++ [b2t a]) with (rev (b2t a :: pend)).
    apply (wfP_wfD (length (b2t a :: pend)) (b2t a :: pend) (le_n _)), Hwf. }
  remember (Gs ((a :: Sa) :: W)) as G eqn:EG. clear EG.
  destruct a; cbn [b2t] in HL, Hwf' |- *; cbn [lsw isD isx andb xorb tokc] in HL |- *.
  - destruct (startsD pend).
    + destruct G; cbn in HL |- *; congruence.
    + rewrite Hwf'. rewrite HL. destruct G; reflexivity.
  - rewrite Hwf'. rewrite HL. destruct G; reflexivity.
Qed.

(** ===== invariants are preserved ===== *)
Lemma Gs_firstne W W' : Gs W = Some W' -> firstne W' = true.
Proof.
  intro H. destruct W as [|Sa [|Sb rest]]; [discriminate| |].
  - cbn in H. inversion H; subst. destruct (parity Sa); unfold Phi; destruct (map negb (pxl false Sa)); reflexivity.
  - rewrite Gs_cons2 in H. destruct (parity Sa) eqn:Ep.
    + destruct (Gs (Sb :: rest)); cbn in H; inversion H; subst.
      destruct Sa as [|a Sa]; [discriminate|]. reflexivity.
    + destruct rest; inversion H; subst. unfold Phi. destruct (map negb (pxl false Sa)); [|reflexivity].
      cbn [app]. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma lastb_app_single d Sa b : lastb d (Sa ++ [b]) = b.
Proof. revert d; induction Sa as [|a Sa IH]; intro d; [reflexivity|]. cbn. apply IH. Qed.

Lemma Phi_endy Sa : Sa <> [] -> parity Sa = true -> endy (Phi Sa) = true.
Proof.
  intros Hne Hp. destruct (exists_last Hne) as [A0 [a ->]].
  destruct (Phi_last A0 a) as [P HP]. rewrite HP, Hp.
  unfold endy. rewrite lastb_app_single. destruct P; reflexivity.
Qed.

Lemma Gs_invb W : invb W = true -> forall W', Gs W = Some W' -> invb W' = true.
Proof.
  induction W as [|Sa W IH]; intros Hinv W' H; [discriminate|].
  destruct W as [|Sb rest].
  - cbn in H. inversion H; subst. destruct (parity Sa) eqn:Ep; [|reflexivity].
    cbn [invb]. rewrite andb_true_r. unfold endy. rewrite lastb_app_single.
    destruct (Phi Sa ++ [false]) eqn:E; [destruct (Phi Sa); discriminate|reflexivity].
  - cbn [invb] in Hinv. apply andb_true_iff in Hinv as [HA Hinv'].
    rewrite Gs_cons2 in H. destruct (parity Sa) eqn:Ep.
    + destruct (Gs (Sb :: rest)) as [W2|] eqn:EG; cbn in H; inversion H; subst.
      pose proof (Gs_nonempty _ _ EG) as Hne.
      destruct W2 as [|Sc W2]; [congruence|]. cbn [invb].
      rewrite Phi_endy by (destruct Sa; [discriminate|congruence] || exact Ep).
      cbn [andb]. apply (IH Hinv' _ eq_refl).
    + destruct rest; inversion H; subst; reflexivity.
Qed.

Lemma Gsn_shift W W' m : Gs W = Some W' -> Gsn m W' = Gsn (S m) W.
Proof.
  intro H. induction m as [|m IH].
  - cbn. rewrite H. reflexivity.
  - cbn [Gsn]. rewrite IH. reflexivity.
Qed.

(** ===== start and the final theorem ===== *)
Definition w1 : list tok := [tx; tx; tD].

Lemma init : c0 -[ tm ]->* Cfg w1.
Proof. unfold Cfg, w1. cbn [enc enc_tok app]. solve_init. Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt. { apply init. }
  apply progress_nonhalt_cond with (C := Cfg)
    (P := fun w => exists W, w = encw W /\ invb W = true /\ firstne W = true /\ forall m, Gsn m W <> None).
  - intros w [W [-> [Hi [Hf Hall]]]].
    destruct (Gs W) as [W'|] eqn:EG; [|exfalso; apply (Hall (S O)); cbn; exact EG].
    exists (encw W'). split.
    + apply tstep_sim. rewrite tstep_encw, EG by assumption. reflexivity.
    + exists W'. split; [reflexivity|]. split; [eapply Gs_invb; eassumption|]. split; [eapply Gs_firstne, EG|].
      intro m. rewrite (Gsn_shift W W' m EG). apply Hall.
  - exists [[true; true]]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intro m. rewrite (Gsn_shift [[]] [[true; true]] m eq_refl). exact (T_total (S m)).
Qed.

Print Assumptions nonhalt.
