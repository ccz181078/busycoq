(* Classification: translated counter. Source: BusyCoq PR #37,
   commit bea67188b999166fca661da2f659f267eb7630ed.
   Original proof bodies preserved; local packaging only. *)

(* #428 1RB0LA_1RC---_0LD1RD_1RA0RE_0RF1RC_1LF0LA and #513 1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_0RC0LF:
   translated base-4 counters with lazy carries. Each level m (17, 35, 71, 143, then 288 4^j - 1 and 576 4^j - 1)
   counts to its overflow; the erase leaves the blank tape one cell left of the old trail, so the machine replays its
   own history (a crossing counter X) up to the old counter's remains; X freezes there (S1), a lone counter shrinks to
   nothing (S2), X restarts as a lone counter, absorbs the swept marks and merges into the level-(2m+1) counter (S3).
   Machine-free theory first (digits, the right pass RP, the invariant, values, the climb), then Section Gen: the
   whole argument for any machine with the bounded rules stated as hypotheses (both machines make the same tape
   rewrites); TM1 / TM2 prove the rules by es', the merge rounds, and the base case by a bounded run of
   20,274,513 / 24,009,260 steps. *)
From BusyCoq Require Import Individual62 ES_v3.
From Coq Require Import String List Arith ZifyNat Lia ZArith Bool NArith.
Import ListNotations.
Set Warnings "-abstract-large-number".

Inductive dg := Dm | D0 | D1 | D2 | D3.
Definition sc d := match d with Dm => D0 | D0 => D1 | D1 => D2 | D2 => D3 | D3 => D3 end.

Definition bt d : list Sym :=
  match d with
  | Dm => [1;1;1;1;1;0] | D0 => [1;1;1;1;1] | D1 => [1;1;0;1;1;1;0] | D2 => [1;1;0;1;1;1] | D3 => [1;1;0;0;1;1;1;0]
  end.
Definition dec d : list Sym :=
  match d with
  | Dm => [1;1;0;1;1;0;1] | D0 => [1;0;1;1;0;1] | D1 => [1;1;0;1;1;1;0;1] | D2 => [1;0;1;1;1;0;1]
  | D3 => [1;1;0;1;1;1;1;0;1]
  end.
Fixpoint Bs ds : list Sym := match ds with [] => [] | d :: ds => [1] ++ bt d ++ Bs ds end.
Fixpoint decstack ds l := match ds with [] => l | d :: ds => decstack ds (l <* dec d) end.

Definition Rl d : list Sym :=
  match d with
  | Dm => [1;1;1;0;1;1;0] | D0 => [1;1;0;1;1;0] | D1 => [1;1;1;0;1;1;1;0] | D2 => [1;1;0;1;1;1;0]
  | D3 => [1;1;1;0;1;1;1;1;0]
  end.
Definition Er d : list Sym :=
  match d with
  | Dm => [0;0;0;1;1;1;0;1;1;1] | D0 => [0;0;0;1;1;1;1;1;1]
  | D1 => [0;0;0;0;1;1;1;0;1;1;1] | D2 => [0;0;0;0;1;1;1;1;1;1] | D3 => [0;0;0;0;0;1;1;1;0;1;1;1]
  end.
Definition Er' d : list Sym :=
  match d with
  | Dm => [1;1;1;0;1;1;1] | D0 => [1;1;1;1;1;1] | D1 => [0;1;1;1;0;1;1;1] | D2 => [0;1;1;1;1;1;1]
  | D3 => [0;0;1;1;1;0;1;1;1]
  end.
Lemma Er_split d r: [0] *> Er d *> r = [0;0;0;0] *> Er' d *> r.
Proof. destruct d; reflexivity. Qed.

Fixpoint lstack ds l := match ds with [] => l | d :: ds => lstack ds l <* Rl d end.
Fixpoint Ers ds : list Sym := match ds with [] => [0;0;0] | d :: ds => Ers ds ++ Er' d end.
Fixpoint Ercat ds : list Sym := match ds with [] => [] | d :: ds => Ercat ds ++ Er' d end.
Lemma Ers_cat ds: Ers ds = [0;0;0] ++ Ercat ds.
Proof. induction ds as [|d ds IH]; cbn [Ers Ercat]; [reflexivity | rewrite IH, app_assoc; reflexivity]. Qed.
Lemma Ercat_app ds ds': Ercat (ds ++ ds') = Ercat ds' ++ Ercat ds.
Proof.
  induction ds as [|d ds IH]; cbn [app Ercat].
  - rewrite app_nil_r; reflexivity.
  - rewrite IH, app_assoc; reflexivity.
Qed.
Lemma bt_Er' t r: [1;1] *> Er' t *> r = bt t *> [1] *> [1;1] *> r.
Proof. destruct t; reflexivity. Qed.
Lemma dec_input t ts r: [1;1] *> Ercat (rev (t :: ts)) *> r = bt t *> Bs ts *> [1] *> [1;1] *> r.
Proof.
  revert t r; induction ts as [|t' ts IH]; intros.
  - cbn [rev app Ercat Bs]. apply bt_Er'.
  - replace (rev (t :: t' :: ts)) with (rev (t' :: ts) ++ [t]) by reflexivity.
    rewrite Ercat_app. cbn [Ercat app].
    rewrite Str_app_assoc, bt_Er', IH. cbn [Bs]. repeat rewrite Str_app_assoc. reflexivity.
Qed.
Lemma decstack_app ds d l: decstack (ds ++ [d]) l = decstack ds l <* dec d.
Proof. revert l; induction ds as [|d' ds IH]; intros; cbn [app decstack]; [reflexivity | apply IH]. Qed.
Lemma lstack_app xs ys l: lstack (xs ++ ys) l = lstack xs (lstack ys l).
Proof. induction xs as [|x xs IH]; cbn [app lstack]; congruence. Qed.
Lemma dec_Rl d y: y <* dec d <* [1] = y <* [1] <* Rl d.
Proof. destruct d; reflexivity. Qed.
Lemma dec_l ds y: decstack ds y <* [1] = lstack (rev ds) (y <* [1]).
Proof.
  revert y; induction ds as [|d ds IH]; intros; cbn [decstack rev].
  - reflexivity.
  - rewrite IH, dec_Rl, lstack_app. reflexivity.
Qed.

Definition EX3 d : list Sym :=
  match d with
  | D0 => [1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;0;1] | D2 => [1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;1;0;1] | _ => []
  end.

Fixpoint Bt ds : list Sym := match ds with [] => [] | d :: ds => bt d ++ [1] ++ Bt ds end.
Lemma Bt_Bs t ts r: bt t *> Bs ts *> [1] *> r = Bt (t :: ts) *> r.
Proof.
  revert t r; induction ts as [|t' ts IH]; intros; cbn [Bs Bt]; repeat rewrite Str_app_assoc.
  - reflexivity.
  - rewrite IH. cbn [Bt]. repeat rewrite Str_app_assoc. reflexivity.
Qed.
Lemma dec_inputB ds r: ds <> [] -> [1;1] *> Ercat (rev ds) *> r = Bt ds *> [1;1] *> r.
Proof. destruct ds as [|t ts]; [congruence|]. intros _. rewrite dec_input, Bt_Bs. reflexivity. Qed.
Lemma rev_cons_nn (e : dg) rout: rev (e :: rout) <> [].
Proof. cbn [rev]. intro H. destruct (app_eq_nil _ _ H) as [_ H']. discriminate. Qed.

Inductive top := TDig (d : dg) | TLone.
Definition topok tp := tp = TDig D1 \/ tp = TDig D2 \/ tp = TLone.
Definition tbok tp := tp = TDig D1 \/ tp = TDig D2 \/ tp = TDig D3 \/ tp = TLone.
Lemma topok_tb tp: topok tp -> tbok tp.
Proof. unfold topok, tbok; tauto. Qed.
Definition TB tp : list Sym :=
  match tp with
  | TDig D1 => [1;1;0;1;1;1;0;0] | TDig D2 => [1;0;1;1;1;0;0] | TDig D3 => [1;1;0;1;1;1;1;0;0] | TDig _ => []
  | TLone => [1;1;0;0]
  end.
Definition base tp (l : side) := match tp with TDig d => l <* [0] <* Rl d | TLone => l <* [0] <* [1;1;1;0] end.
Lemma TB_base tp W: tbok tp -> W <* TB tp <* [1] = base tp W.
Proof. intros [-> | [-> | [-> | ->]]]; reflexivity. Qed.
Definition EXT : list Sym := [1;1;0;1;1;0;1;1;1].
Lemma side_app (l : side) xs ys: l <* xs <* ys = l <* (ys ++ xs).
Proof. symmetry. apply Str_app_assoc. Qed.

Inductive RP : top -> list dg -> list dg -> list Sym -> top -> list dg -> Prop :=
  | RP_nil tp rout : RP tp rout [] [] tp rout
  | RP_can tp rout d ds tx tp' rout' : d <> D3 -> RP tp (d :: rout) ds tx tp' rout' -> RP tp rout (d :: ds) tx tp' rout'
  | RP_fire tp rout dh ds tx tp' rout' : dh = D0 \/ dh = D2 -> RP tp (Dm :: sc dh :: rout) ds tx tp' rout' ->
      RP tp (dh :: rout) (D3 :: ds) tx tp' rout'
  | RP_top ds tx tp' rout' : RP (TDig D3) [Dm] ds tx tp' rout' -> RP (TDig D2) [] (D3 :: ds) tx tp' rout'
  | RP_detach ds tx tp' rout' : RP TLone [] ds tx tp' rout' -> RP TLone [] (D3 :: ds) (tx ++ EXT) tp' rout'
  | RP_trig tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' : topok tp -> (dh = Dm /\ e = D0) \/ (dh = D1 /\ e = D2) ->
      RP tp [] (rev (e :: rout)) tx1 tp1 rout2 -> RP tp1 rout2 (Dm :: ds) tx2 tp' rout' ->
      RP tp (dh :: rout) (D3 :: ds) (tx2 ++ tx1 ++ [1;1;1]) tp' rout'.

Definition RecT (l0 : side) tp ws d0 (r : side) := lstack (d0 :: rev ws) (base tp l0) <* [1;0] {{C}}> r.

Definition OVT : list Sym := [0;0;0;0;1;1;1;1;1;1;1;0;1;1;1].
Definition Zl d : list Sym :=
  match d with D1 => [0;1;1;1;1;1;1;1] | D3 => [0;0;1;1;1;1;1;1;1] | _ => [] end.
Fixpoint S2T (ks : list nat) (l : side) : side :=
  match ks with [] => l | k :: ks => S2T ks l <* [1]^^(S (S k)) <* [0;1;1;0] end.
Fixpoint S3B (ks : list nat) : list Sym :=
  match ks with [] => [] | k :: ks => S3B ks ++ [0]^^k ++ [1;1;1;1;1;1] end.

Definition topokb tp := match tp with TDig D1 | TDig D2 | TLone => true | _ => false end.
Definition tbokb tp := match tp with TDig D1 | TDig D2 | TDig D3 | TLone => true | _ => false end.
Lemma topokb_ok tp: topokb tp = true -> topok tp.
Proof. destruct tp as [[]|]; cbn; try discriminate; unfold topok; auto. Qed.
Lemma tbokb_ok tp: tbokb tp = true -> tbok tp.
Proof. destruct tp as [[]|]; cbn; try discriminate; unfold tbok; auto. Qed.

Fixpoint rpf (n : nat) tp rout ds : option (list Sym * top * list dg) :=
  match n with O => None | S n =>
  match ds with
  | [] => Some ([], tp, rout)
  | D3 :: ds' =>
      match rout with
      | [] => match tp with
              | TDig D2 => rpf n (TDig D3) [Dm] ds'
              | TLone => match rpf n TLone [] ds' with Some (tx, tp', r') => Some (tx ++ EXT, tp', r') | None => None end
              | _ => None
              end
      | dh :: rout0 =>
          match dh with
          | D0 | D2 => rpf n tp (Dm :: sc dh :: rout0) ds'
          | Dm | D1 =>
              if topokb tp then
                match rpf n tp [] (rev (sc dh :: rout0)) with
                | Some (tx1, tp1, rout2) =>
                    match rpf n tp1 rout2 (Dm :: ds') with
                    | Some (tx2, tp', r') => Some (tx2 ++ tx1 ++ [1;1;1], tp', r')
                    | None => None
                    end
                | None => None
                end
              else None
          | D3 => None
          end
      end
  | d :: ds' => rpf n tp (d :: rout) ds'
  end end.

Lemma rpf_sound n: forall tp rout ds tx tp' rout', rpf n tp rout ds = Some (tx, tp', rout') -> RP tp rout ds tx tp' rout'.
Proof.
  induction n as [|n IH]; intros tp rout ds tx tp' rout' H; [discriminate|].
  destruct ds as [|d ds]; cbn [rpf] in H.
  - inversion H; subst. constructor.
  - destruct d; try (apply RP_can; [discriminate | apply IH; exact H]).
    destruct rout as [|dh rout0].
    + destruct tp as [[]|]; try discriminate.
      * apply RP_top. apply IH. exact H.
      * destruct (rpf n TLone [] ds) as [[[tx0 tp0] r0]|] eqn:E; [|discriminate].
        inversion H; subst. apply RP_detach. apply IH. exact E.
    + destruct dh; try discriminate.
      * destruct (topokb tp) eqn:Et; [|discriminate].
        destruct (rpf n tp [] (rev (sc Dm :: rout0))) as [[[tx1 tp1] rout2]|] eqn:E1; [|discriminate].
        destruct (rpf n tp1 rout2 (Dm :: ds)) as [[[tx2 tp2] r2]|] eqn:E2; [|discriminate].
        inversion H; subst. eapply RP_trig; eauto using topokb_ok.
      * apply RP_fire; [auto | apply IH; exact H].
      * destruct (topokb tp) eqn:Et; [|discriminate].
        destruct (rpf n tp [] (rev (sc D1 :: rout0))) as [[[tx1 tp1] rout2]|] eqn:E1; [|discriminate].
        destruct (rpf n tp1 rout2 (Dm :: ds)) as [[[tx2 tp2] r2]|] eqn:E2; [|discriminate].
        inversion H; subst. eapply RP_trig; eauto using topokb_ok.
      * apply RP_fire; [auto | apply IH; exact H].
Qed.

Definition incf (n : nat) tp ws d0 : option (list Sym * top * list dg * dg) :=
  match d0 with
  | D0 | D2 => Some ([], tp, ws, sc d0)
  | D1 =>
      if topokb tp then
        match ws with
        | [] => Some ([1;1;1], tp, [], D2)
        | _ => match rpf n tp [] ws with
               | Some (tx, tp', rout) => if tbokb tp' then Some (tx ++ [1;1;1], tp', rev rout, D2) else None
               | None => None
               end
        end
      else None
  | D3 =>
      if topokb tp then
        match ws with
        | [] => None
        | _ => match rpf n tp [] ws with
               | Some (tx, tp1, d1 :: rout) =>
                   match d1 with
                   | D0 | D2 => if tbokb tp1 then Some (tx ++ [1;1;1], tp1, rev rout ++ [sc d1], D0) else None
                   | Dm | D1 =>
                       if topokb tp1 then
                         match rpf n tp1 [] (rev (sc d1 :: rout)) with
                         | Some (tx2, tp', rout2) =>
                             if tbokb tp' then Some (tx2 ++ [1;1;1] ++ tx ++ [1;1;1], tp', rev rout2, D0) else None
                         | None => None
                         end
                       else None
                   | D3 => None
                   end
               | _ => None
               end
        end
      else None
  | Dm => None
  end.
Fixpoint incs n k tp ws d0 : option (list Sym * top * list dg * dg) :=
  match k with
  | O => Some ([], tp, ws, d0)
  | S k => match incf n tp ws d0 with
           | Some (g, tp1, ws1, d1) =>
               match incs n k tp1 ws1 d1 with Some (g2, tp', ws', d') => Some (g2 ++ g, tp', ws', d') | None => None end
           | None => None
           end
  end.

Fixpoint scan (s : bool) (l : list dg) : option bool :=
  match l with
  | [] => Some s
  | D2 :: l => scan s l
  | D3 :: l => if s then scan false l else None
  | _ :: l => scan true l
  end.
Definition ok s l := scan s l <> None.

Lemma scan_app s X Y: scan s (X ++ Y) = match scan s X with Some s' => scan s' Y | None => None end.
Proof.
  revert s; induction X as [|d X IH]; intros s; [reflexivity|].
  destruct d; cbn [app scan]; try apply IH. destruct s; [apply IH | reflexivity].
Qed.
Lemma ok_mono l: ok false l -> ok true l.
Proof.
  unfold ok; induction l as [|d l IH]; cbn [scan]; [discriminate|].
  destruct d; auto; intros H; exfalso; apply H; reflexivity.
Qed.
Lemma ok_app_l s X Y: ok s (X ++ Y) -> exists s', scan s X = Some s' /\ ok s' Y.
Proof.
  unfold ok; rewrite scan_app. destruct (scan s X) as [s'|]; [intros H; exists s'; auto | intros H; exfalso; apply H; reflexivity].
Qed.
Lemma ok_app_r s X s' Y: scan s X = Some s' -> ok s' Y -> ok s (X ++ Y).
Proof. unfold ok; rewrite scan_app; intros ->; auto. Qed.
Lemma ok_fire s X dh Z: dh = D0 \/ dh = D2 -> ok s (X ++ [dh; D3] ++ Z) -> ok s (X ++ [sc dh; Dm] ++ Z).
Proof.
  intros Hdh H. destruct (ok_app_l _ _ _ H) as [s0 [E H0]]. apply (ok_app_r _ _ _ _ E).
  destruct Hdh as [-> | ->]; unfold ok in *; cbn [scan sc app] in *.
  - apply ok_mono; exact H0.
  - destruct s0; [apply ok_mono; exact H0 | exfalso; apply H0; reflexivity].
Qed.
Lemma ok_trig s X dh Z: dh = Dm \/ dh = D1 -> ok s (X ++ [dh; D3] ++ Z) -> ok s (X ++ [sc dh; Dm] ++ Z).
Proof.
  intros Hdh H. destruct (ok_app_l _ _ _ H) as [s0 [E H0]]. apply (ok_app_r _ _ _ _ E).
  destruct Hdh as [-> | ->]; unfold ok in *; cbn [scan sc app] in *; apply ok_mono; exact H0.
Qed.
Lemma ok_prefix s X Y: ok s (X ++ Y) -> ok s X.
Proof. intros H. destruct (ok_app_l _ _ _ H) as [s' [E _]]. unfold ok; rewrite E; discriminate. Qed.

Definition dtop tp := tp = TDig D2 \/ tp = TLone.

Lemma rev_two (a b : dg) l: rev (b :: a :: l) = rev l ++ [a; b].
Proof. cbn [rev]. rewrite <- app_assoc. reflexivity. Qed.

Lemma rp_mono tp rout ds tx tp' rout': RP tp rout ds tx tp' rout' -> dtop tp ->
  forall Y, ok false (rev rout ++ ds ++ Y) -> tp' = tp /\ ok false (rev rout' ++ Y).
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd _ IH | tp rout dh ds tx tp' rout' Hdh _ IH
                 | ds tx tp' rout' _ IH | ds tx tp' rout' _ IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde _ IH1 _ IH2]; intros Hdt Y H.
  - split; [reflexivity | exact H].
  - apply IH; [exact Hdt|]. cbn [rev]. rewrite <- app_assoc. exact H.
  - apply IH; [exact Hdt|]. rewrite rev_two, <- app_assoc.
    cbn [rev] in H. rewrite <- app_assoc in H. apply ok_fire; [exact Hdh | exact H].
  - exfalso. cbn in H. apply H. reflexivity.
  - exfalso. cbn in H. apply H. reflexivity.
  - assert (Ee: e = sc dh) by (destruct Hde as [[-> ->] | [-> ->]]; reflexivity).
    assert (H1: ok false (rev [] ++ rev (e :: rout) ++ Dm :: ds ++ Y)).
    { cbn [rev app]. rewrite <- app_assoc. cbn [app]. rewrite Ee.
      cbn [rev] in H. rewrite <- app_assoc in H.
      apply ok_trig; [destruct Hde as [[-> _] | [-> _]]; auto | exact H]. }
    destruct (IH1 Hdt _ H1) as [E1 H2]. subst tp1.
    destruct (IH2 Hdt Y H2) as [E2 H3]. split; [exact E2 | exact H3].
Qed.

Definition cl d : nat := match d with Dm => 7 | D0 => 6 | D1 => 8 | D2 => 7 | D3 => 9 end.
Fixpoint cls l : nat := match l with [] => O | d :: l => cl d + cls l end.
Definition dv d : Z := match d with Dm => (-1)%Z | D0 => 0%Z | D1 => 1%Z | D2 => 2%Z | D3 => 3%Z end.
Fixpoint wv (l : list dg) : Z := match l with [] => 0%Z | d :: l => (dv d * 4 ^ Z.of_nat (length l) + wv l)%Z end.
Ltac zring := rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_0; repeat (rewrite Z.pow_succ_r by lia); rewrite ?Z.pow_0_r; ring.
Fixpoint count3 (l : list dg) : nat := match l with [] => O | D3 :: l => S (count3 l) | _ :: l => count3 l end.

Lemma cls_app X Y: cls (X ++ Y) = cls X + cls Y.
Proof. induction X as [|d X IH]; cbn; lia. Qed.
Lemma cls_rev l: cls (rev l) = cls l.
Proof. induction l as [|d l IH]; cbn [rev cls]; [reflexivity|]. rewrite cls_app; cbn; lia. Qed.
Lemma wv_app X Y: wv (X ++ Y) = (wv X * 4 ^ Z.of_nat (length Y) + wv Y)%Z.
Proof.
  induction X as [|d X IH]; cbn [app wv length]; [lia|].
  rewrite IH, length_app, Nat2Z.inj_add, Z.pow_add_r by lia. ring.
Qed.
Lemma ok_33 s X Z: ok s (X ++ [D3; D3] ++ Z) -> False.
Proof.
  intros H. destruct (ok_app_l _ _ _ H) as [s0 [_ H0]]. unfold ok in H0; cbn in H0.
  destruct s0; apply H0; reflexivity.
Qed.

Lemma rp_meas tp rout ds tx tp' rout': RP tp rout ds tx tp' rout' -> dtop tp -> ok false (rev rout ++ ds) ->
  length rout' = length rout + length ds /\ cls rout' + length tx = cls rout + cls ds /\ wv (rev rout') = wv (rev rout ++ ds) /\
  exists k, tx = [1]^^k.
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd _ IH | tp rout dh ds tx tp' rout' Hdh _ IH
                 | ds tx tp' rout' _ IH | ds tx tp' rout' _ IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde H1 IH1 H2 IH2]; intros Hdt H.
  - rewrite app_nil_r. cbn. repeat split; try lia. exists O. reflexivity.
  - destruct IH as [E1 [E2 [E3 E4]]]; [exact Hdt | cbn [rev]; rewrite <- app_assoc; exact H|].
    cbn [length cls] in *. repeat split; [lia | lia| |exact E4]. rewrite E3. cbn [rev]. rewrite <- app_assoc. reflexivity.
  - destruct IH as [E1 [E2 [E3 E4]]]; [exact Hdt | rewrite rev_two, <- app_assoc; cbn [rev] in H; rewrite <- app_assoc in H;
      apply ok_fire; [exact Hdh | exact H]|].
    cbn [length cls] in *. rewrite E3, rev_two, <- app_assoc. cbn [rev]. rewrite <- app_assoc.
    destruct Hdh as [-> | ->]; cbn [sc cl] in *; (split; [lia | split; [lia| split; [|exact E4]]]);
      rewrite !wv_app; cbn [wv length app dv]; zring.
  - exfalso. cbn in H. apply H. reflexivity.
  - exfalso. cbn in H. apply H. reflexivity.
  - assert (Ee: e = sc dh) by (destruct Hde as [[-> ->] | [-> ->]]; reflexivity).
    assert (Hdh: dh = Dm \/ dh = D1) by (destruct Hde as [[-> _] | [-> _]]; auto).
    assert (Hs: ok false (rev rout ++ [e; Dm] ++ ds)).
    { rewrite Ee. apply ok_trig; [exact Hdh|]. cbn [rev] in H. rewrite <- app_assoc in H. exact H. }
    assert (Hs1: ok false (rev [] ++ rev (e :: rout))).
    { cbn [rev app]. apply (ok_prefix _ _ (Dm :: ds)). rewrite <- app_assoc. exact Hs. }
    destruct (rp_mono _ _ _ _ _ _ H1 Hdt (Dm :: ds)) as [Et1 Hs2].
    { cbn [rev app]. rewrite <- app_assoc. exact Hs. }
    subst tp1.
    destruct (IH1 Hdt Hs1) as [F1 [F2 [F3 [k1 F4]]]]. destruct (IH2 Hdt Hs2) as [G1 [G2 [G3 [k2 G4]]]].
    rewrite length_rev in F1. cbn [length] in F1.
    rewrite cls_rev in F2. cbn [cls] in F2.
    cbn [rev app] in F3.
    split; [rewrite G1, F1; cbn [length]; lia|]. split.
    + rewrite !length_app. cbn [length cls] in *. rewrite Ee in F2. destruct Hdh as [-> | ->]; cbn [sc cl] in *; lia.
    + split.
      * rewrite G3, (wv_app (rev rout2)), F3. cbn [rev]. rewrite !wv_app. cbn [wv length]. rewrite Ee.
        destruct Hdh as [-> | ->]; cbn [sc dv]; zring.
      * exists (k2 + (k1 + 3))%nat. rewrite F4, G4, !lpow_add. reflexivity.
Qed.

Lemma count3_can x l: x <> D3 -> count3 (x :: l) = count3 l.
Proof. destruct x; cbn; congruence. Qed.
Lemma dg3_dec x: x <> D3 \/ x = D3.
Proof. destruct x; auto; left; discriminate. Qed.

Lemma rp_exists tp: dtop tp -> forall T n3 d rout ds, length rout + length ds <= T -> count3 ds <= n3 -> length ds <= d ->
  ok false (rev rout ++ ds) -> exists tx rout', RP tp rout ds tx tp rout'.
Proof.
  intros Hdt. assert (Htp: topok tp) by (destruct Hdt as [-> | ->]; unfold topok; auto).
  induction T as [|T IHT].
  { intros n3 d rout ds HT Hn Hd H. destruct ds as [|x ds]; [exists (@nil Sym), rout; constructor | cbn [length] in HT; lia]. }
  intros n3; induction n3 as [|n3 IHn].
  { intros d; induction d as [|d IHd]; intros rout ds HT Hn Hd H; (destruct ds as [|x ds]; [exists (@nil Sym), rout; constructor|]).
    - cbn [length] in Hd; lia.
    - destruct (dg3_dec x) as [Hx | ->]; [|cbn [count3] in Hn; lia].
      rewrite count3_can in Hn by exact Hx.
      destruct (IHd (x :: rout) ds) as [tx [rout' Hr]];
        [cbn [length] in *; lia | exact Hn | cbn [length] in Hd; lia | cbn [rev]; rewrite <- app_assoc; exact H|].
      exists tx, rout'. apply RP_can; [exact Hx | exact Hr]. }
  intros d; induction d as [|d IHd]; intros rout ds HT Hn Hd H; (destruct ds as [|x ds]; [exists (@nil Sym), rout; constructor|]).
  { cbn [length] in Hd; lia. }
  destruct (dg3_dec x) as [Hx | ->].
  { rewrite count3_can in Hn by exact Hx.
    destruct (IHd (x :: rout) ds) as [tx [rout' Hr]];
      [cbn [length] in *; lia | exact Hn | cbn [length] in Hd; lia | cbn [rev]; rewrite <- app_assoc; exact H|].
    exists tx, rout'. apply RP_can; [exact Hx | exact Hr]. }
  cbn [count3 length] in *.
  destruct rout as [|dh rout0].
  { exfalso. cbn in H. apply H. reflexivity. }
  cbn [rev] in H. rewrite <- app_assoc in H. cbn [app] in H. cbn [length] in HT.
  assert (Hdh: (dh = Dm \/ dh = D1) \/ (dh = D0 \/ dh = D2) \/ dh = D3) by (destruct dh; auto).
  destruct Hdh as [Hde | [Hf | ->]].
  - assert (Hs: ok false (rev rout0 ++ [sc dh; Dm] ++ ds)) by (apply ok_trig; auto).
    assert (Hs1: ok false (rev [] ++ rev (sc dh :: rout0))).
    { cbn [rev app]. apply (ok_prefix _ _ (Dm :: ds)). rewrite <- app_assoc. exact Hs. }
    destruct (IHT (count3 (rev (sc dh :: rout0))) (length (rev (sc dh :: rout0))) [] (rev (sc dh :: rout0)))
      as [tx1 [rout2 Hr1]]; [rewrite length_rev; cbn [length]; lia | lia | lia | exact Hs1|].
    destruct (rp_mono _ _ _ _ _ _ Hr1 Hdt (Dm :: ds)) as [_ Hs2]; [cbn [rev app]; rewrite <- app_assoc; exact Hs|].
    destruct (rp_meas _ _ _ _ _ _ Hr1 Hdt Hs1) as [L1 _].
    destruct (IHn (S (length ds)) rout2 (Dm :: ds)) as [tx2 [rout' Hr2]];
      [cbn [length]; rewrite L1, length_rev; cbn [length]; lia | cbn [count3]; lia | cbn [length]; lia | exact Hs2|].
    exists (tx2 ++ tx1 ++ [1;1;1]), rout'. apply (RP_trig tp rout0 dh (sc dh) ds tx1 tp rout2 tx2 tp rout' Htp);
      [destruct Hde as [-> | ->]; [left | right]; split; reflexivity | exact Hr1 | exact Hr2].
  - destruct (IHn d (Dm :: sc dh :: rout0) ds) as [tx [rout' Hr]];
      [cbn [length]; lia | lia | lia | rewrite rev_two, <- app_assoc; apply ok_fire; auto|].
    exists tx, rout'. apply RP_fire; [exact Hf | exact Hr].
  - exfalso. apply (ok_33 false (rev rout0) ds). exact H.
Qed.

Lemma count3_app X Y: count3 (X ++ Y) = count3 X + count3 Y.
Proof. induction X as [|d X IH]; [reflexivity|]. destruct d; cbn [app count3]; rewrite ?IH; reflexivity. Qed.
Lemma rp_3free tp rout ds tx tp' rout': RP tp rout ds tx tp' rout' -> count3 ds = O ->
  tx = [] /\ tp' = tp /\ rout' = rev ds ++ rout.
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd _ IH | | | | ]; intros H3; try (cbn [count3] in H3; discriminate).
  - repeat split; reflexivity.
  - rewrite count3_can in H3 by exact Hd. destruct (IH H3) as [-> [-> ->]].
    repeat split. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma scan_true_3free B: count3 B = O -> scan true B = Some true.
Proof.
  induction B as [|d B IH]; intros H; [reflexivity|].
  destruct d; cbn [count3 scan] in *; try discriminate; apply IH; exact H.
Qed.
Lemma rp_lowest tp rout ds tx tp' rout': RP tp rout ds tx tp' rout' -> dtop tp -> ok false (rev rout ++ ds) ->
  count3 ds <> O -> exists X B, rev rout' = X ++ Dm :: B /\ count3 B = O.
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd H1 IH | tp rout dh ds tx tp' rout' Hdh H1 IH
                 | ds tx tp' rout' H1 IH | ds tx tp' rout' H1 IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde H1 IH1 H2 IH2]; intros Hdt Hok H3.
  - exfalso; apply H3; reflexivity.
  - apply IH; [exact Hdt | cbn [rev]; rewrite <- app_assoc; exact Hok |]. rewrite count3_can in H3 by exact Hd. exact H3.
  - destruct (Nat.eq_dec (count3 ds) O) as [E|E].
    + destruct (rp_3free _ _ _ _ _ _ H1 E) as [_ [_ ->]].
      exists (rev rout ++ [sc dh]), ds. split; [|exact E].
      rewrite rev_app_distr, rev_involutive. cbn [rev]. rewrite <- !app_assoc. reflexivity.
    + apply IH; [exact Hdt | | exact E]. rewrite rev_two, <- app_assoc. cbn [rev] in Hok. rewrite <- app_assoc in Hok.
      apply ok_fire; [exact Hdh | exact Hok].
  - exfalso. cbn in Hok. apply Hok. reflexivity.
  - exfalso. cbn in Hok. apply Hok. reflexivity.
  - assert (Hs: ok false (rev rout ++ [e; Dm] ++ ds)).
    { assert (Ee: e = sc dh) by (destruct Hde as [[-> ->] | [-> ->]]; reflexivity). rewrite Ee.
      apply ok_trig; [destruct Hde as [[-> _] | [-> _]]; auto|]. cbn [rev] in Hok. rewrite <- app_assoc in Hok. exact Hok. }
    destruct (rp_mono _ _ _ _ _ _ H1 Hdt (Dm :: ds)) as [Et Hs2]; [cbn [rev app]; rewrite <- app_assoc; exact Hs|].
    subst tp1.
    destruct (Nat.eq_dec (count3 ds) O) as [E|E].
    + destruct (rp_3free _ _ _ _ _ _ H2 E) as [_ [_ ->]].
      exists (rev rout2), ds. split; [|exact E].
      rewrite rev_app_distr, rev_involutive. reflexivity.
    + apply IH2; [exact Hdt | exact Hs2 | cbn [count3]; exact E].
Qed.

Definition lowc d := match d with D2 | D3 => D3 | d => d end.
Definition Inv ws d0 := ok false (ws ++ [lowc d0]).
Lemma Inv_word ws d0: Inv ws d0 -> ok false (ws ++ [d0]).
Proof.
  unfold Inv; intros H. destruct (ok_app_l _ _ _ H) as [s [E H0]]. apply (ok_app_r _ _ _ _ E).
  unfold ok in *; destruct d0; cbn in *; try discriminate; destruct s; cbn in *; congruence.
Qed.
Lemma ok_stop s X d: d = Dm \/ d = D0 \/ d = D1 -> ok s X -> ok s (X ++ [d]).
Proof.
  intros Hd H. unfold ok in *. rewrite scan_app. destruct (scan s X); [|exfalso; apply H; reflexivity].
  destruct Hd as [-> | [-> | ->]]; discriminate.
Qed.
Lemma ok_after_pass tp ws tx rout: RP tp [] ws tx tp rout -> dtop tp -> ok false ws ->
  (exists d, In d ws /\ d <> D2) -> ok false (rev rout ++ [D3]).
Proof.
  intros Hr Hdt H [d [Hin Hd]].
  destruct (rp_mono _ _ _ _ _ _ Hr Hdt []) as [_ Hm]; [rewrite app_nil_r; exact H|]. rewrite app_nil_r in Hm.
  destruct (Nat.eq_dec (count3 ws) O) as [E|E].
  - destruct (rp_3free _ _ _ _ _ _ Hr E) as [_ [_ ->]]. rewrite app_nil_r, rev_involutive.
    destruct (in_split _ _ Hin) as [A [B ->]].
    assert (EB: count3 B = O) by (rewrite count3_app in E; cbn [count3] in E; destruct d; lia).
    assert (Ed: d = Dm \/ d = D0 \/ d = D1).
    { rewrite count3_app in E. destruct d; cbn [count3] in E; auto; [congruence | lia]. }
    destruct (ok_app_l _ _ _ H) as [s [Es Hs]].
    unfold ok. rewrite <- app_assoc, scan_app, Es. cbn [app].
    destruct Ed as [-> | [-> | ->]]; cbn [scan]; rewrite scan_app, scan_true_3free by exact EB; cbn; discriminate.
  - destruct (rp_lowest _ _ _ _ _ _ Hr Hdt H E) as [X [B [EX EB]]]. rewrite EX in *.
    destruct (ok_app_l _ _ _ Hm) as [s [Es _]].
    unfold ok. rewrite <- app_assoc, scan_app, Es. cbn [app scan].
    rewrite scan_app, scan_true_3free by exact EB. cbn. discriminate.
Qed.

Lemma pow4_ge1 n: (1 <= 4 ^ Z.of_nat n)%Z.
Proof. change 1%Z with (4 ^ 0)%Z at 1. apply Z.pow_le_mono_r; lia. Qed.
Lemma wv_upper w: forall s, ok s w ->
  (12 * wv w <= 8 * (4 ^ Z.of_nat (length w) - 1) + (if s then 3 * 4 ^ Z.of_nat (length w) else 0))%Z.
Proof.
  induction w as [|d w IH]; intros s H; cbn [wv length].
  - destruct s; cbn; lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (pow4_ge1 (length w)) as HP.
    unfold ok in H; destruct d; cbn [scan dv] in H |- *.
    + specialize (IH true H). destruct s; lia.
    + specialize (IH true H). destruct s; lia.
    + specialize (IH true H). destruct s; lia.
    + specialize (IH s H). destruct s; lia.
    + destruct s; [|exfalso; apply H; reflexivity]. specialize (IH false H). cbv beta iota in IH. lia.
Qed.
Lemma wv_lower w: (- (4 ^ Z.of_nat (length w) - 1) <= 3 * wv w)%Z.
Proof.
  induction w as [|d w IH]; cbn [wv length]; [lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. destruct d; cbn [dv]; lia.
Qed.
Definition pos012 d := d = D0 \/ d = D1 \/ d = D2.
Lemma wv_pos012 c: Forall pos012 c -> (0 <= wv c /\ 3 * wv c <= 2 * (4 ^ Z.of_nat (length c) - 1))%Z.
Proof.
  induction c as [|d c IH]; intros H; cbn [wv length]; [lia|].
  inversion H as [|? ? Hd Hc]; subst. destruct (IH Hc) as [L U].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  pose proof (pow4_ge1 (length c)) as HP.
  destruct Hd as [-> | [-> | ->]]; cbn [dv]; lia.
Qed.
Lemma inv_unique w: forall c s, length w = length c -> ok s w -> Forall pos012 c -> wv w = wv c -> w = c.
Proof.
  induction w as [|d w IH]; intros [|e c] s Hl Hok Hc Hv; cbn [length] in Hl; try discriminate; [reflexivity|].
  inversion Hc as [|? ? He Hc']; subst.
  assert (Hok': exists s', ok s' w) by (unfold ok in *; destruct d; cbn [scan] in Hok;
    [exists true | exists true | exists true | exists s | destruct s; [exists false | exfalso; apply Hok; reflexivity]]; exact Hok).
  destruct Hok' as [s' Hok'].
  pose proof (wv_upper w s' Hok') as U. pose proof (wv_lower w) as L. destruct (wv_pos012 c Hc') as [L2 U2].
  cbn [wv] in Hv. injection Hl as Hl. rewrite Hl in *.
  pose proof (pow4_ge1 (length c)) as HP.
  assert (Ede: d = e).
  { destruct He as [-> | [-> | ->]]; destruct d; cbn [dv] in Hv; try reflexivity; exfalso; destruct s'; lia. }
  subst e. f_equal. apply (IH c s'); [reflexivity | exact Hok' | exact Hc' | lia].
Qed.

Lemma all2_wv m: (3 * wv (repeat D2 m) = 2 * (4 ^ Z.of_nat m - 1))%Z.
Proof.
  induction m as [|m IH]; cbn [repeat wv length]; [reflexivity|].
  rewrite repeat_length, Nat2Z.inj_succ, Z.pow_succ_r by lia. cbn [dv]. lia.
Qed.
Lemma all2_dec ws: (forall d, In d ws -> d = D2) \/ (exists d, In d ws /\ d <> D2).
Proof.
  induction ws as [|d ws [IH|IH]].
  - left; intros d [].
  - destruct d; try (right; eexists; split; [left; reflexivity | discriminate]).
    left; intros x [<- | Hx]; auto.
  - right; destruct IH as [x [Hx Hne]]; exists x; split; [right; exact Hx | exact Hne].
Qed.
Lemma all2_of ws: (forall d, In d ws -> d = D2) -> ws = repeat D2 (length ws).
Proof. induction ws as [|d ws IH]; intros H; [reflexivity|]. cbn [length repeat]. rewrite (H d (or_introl eq_refl)). f_equal. apply IH. intros x Hx; apply H; right; exact Hx. Qed.

Lemma rp_app tp rout X tx1 tp1 rout1: RP tp rout X tx1 tp1 rout1 -> forall Y tx2 tp2 rout2, RP tp1 rout1 Y tx2 tp2 rout2 ->
  RP tp rout (X ++ Y) (tx2 ++ tx1) tp2 rout2.
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd H1 IH | tp rout dh ds tx tp' rout' Hdh H1 IH
                 | ds tx tp' rout' H1 IH | ds tx tp' rout' H1 IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde H1 IH1 H2 IH2]; intros Y txa tpa routa Ha; cbn [app].
  - rewrite app_nil_r. exact Ha.
  - apply RP_can; [exact Hd | apply IH; exact Ha].
  - apply RP_fire; [exact Hdh | apply IH; exact Ha].
  - apply RP_top. apply IH. exact Ha.
  - rewrite app_assoc. apply RP_detach. apply IH. exact Ha.
  - rewrite (app_assoc txa tx2). eapply RP_trig; [exact Htp | exact Hde | exact H1 | apply IH2; exact Ha].
Qed.
Lemma rp_copy tp l: count3 l = O -> forall rout, RP tp rout l [] tp (rev l ++ rout).
Proof.
  induction l as [|d l IH]; intros H rout; [constructor|].
  destruct (dg3_dec d) as [Hd | ->]; [|cbn in H; discriminate].
  rewrite count3_can in H by exact Hd. apply RP_can; [exact Hd|].
  cbn [rev]. rewrite <- app_assoc. apply IH. exact H.
Qed.
Lemma count3_repeat2 n: count3 (repeat D2 n) = O.
Proof. induction n; cbn; auto. Qed.
Lemma count3_repeatm n: count3 (repeat Dm n) = O.
Proof. induction n; cbn; auto. Qed.
Lemma rev_repeat {A} (x : A) n: rev (repeat x n) = repeat x n.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat rev]. rewrite IH.
  replace [x] with (repeat x 1) by reflexivity. rewrite <- repeat_app, Nat.add_comm. reflexivity.
Qed.
Definition U a c := repeat D2 a ++ [D3] ++ repeat Dm c.
Lemma rev_U a c: rev (U a c) = repeat Dm c ++ [D3] ++ repeat D2 a.
Proof. unfold U. rewrite !rev_app_distr, !rev_repeat. cbn. rewrite <- app_assoc. reflexivity. Qed.
Lemma rp_pre tp l: count3 l = O -> forall rout rest tx tp' rout', RP tp (rev l ++ rout) rest tx tp' rout' ->
  RP tp rout (l ++ rest) tx tp' rout'.
Proof.
  induction l as [|d l IH]; intros H rout rest tx tp' rout' Hr; [exact Hr|].
  destruct (dg3_dec d) as [Hd | ->]; [|cbn in H; discriminate].
  rewrite count3_can in H by exact Hd. cbn [app]. apply RP_can; [exact Hd|]. apply IH; [exact H|].
  cbn [rev] in Hr. rewrite <- app_assoc in Hr. exact Hr.
Qed.
Lemma repeat_snoc {A} (x : A) n l: repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof. induction n as [|n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma rp_wave tp a c: RP tp [] (U (S a) c) [] tp (rev (U a (S c))).
Proof.
  unfold U at 1. apply rp_pre; [apply count3_repeat2|]. rewrite app_nil_r, rev_repeat. cbn [repeat app].
  apply RP_fire; [right; reflexivity|]. cbn [sc].
  rewrite rev_U. cbn [repeat app]. rewrite <- repeat_snoc.
  pose proof (rp_copy tp (repeat Dm c) (count3_repeatm c) (Dm :: D3 :: repeat D2 a)) as Hc.
  rewrite rev_repeat in Hc. exact Hc.
Qed.

Lemma rev_lift (e : dg) rout X: rev (e :: rout ++ rev X) = X ++ rev (e :: rout).
Proof. cbn [rev]. rewrite rev_app_distr, rev_involutive, app_assoc. reflexivity. Qed.
Fixpoint TR (ct : nat -> list Sym) i s : list Sym := match s with O => [] | S s => TR ct (S i) s ++ ct i ++ [1;1;1] end.
Lemma TR_add ct s1: forall i s2, TR ct i (s1 + s2) = TR ct (i + s1) s2 ++ TR ct i s1.
Proof.
  induction s1 as [|s1 IH]; intros i s2; cbn [TR Nat.add].
  - rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - rewrite IH, <- app_assoc. replace (S i + s1) with (i + S s1) by lia. reflexivity.
Qed.
Lemma rp_ctxg ctx ct n tp r1 ds tx tp' r2: RP tp r1 ds tx tp' r2 ->
  (forall i, i < n -> RP tp [] (ctx i) (ct i) tp (rev (ctx (S i)))) -> dtop tp -> ok false (rev r1 ++ ds) ->
  exists s, length tx = 3 * s /\ forall i, i + s <= n -> RP tp (r1 ++ rev (ctx i)) ds (TR ct i s) tp' (r2 ++ rev (ctx (i + s))).
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd H1 IH | tp rout dh ds tx tp' rout' Hdh H1 IH
                 | ds tx tp' rout' H1 IH | ds tx tp' rout' H1 IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde H1 IH1 H2 IH2]; intros Hc Hdt Hok.
  - exists O. split; [reflexivity|]. intros i _. rewrite Nat.add_0_r. constructor.
  - destruct (IH Hc Hdt) as [s [Hs IH']]; [cbn [rev]; rewrite <- app_assoc; exact Hok|].
    exists s. split; [exact Hs|]. intros i Hi. apply RP_can; [exact Hd|]. apply IH'; exact Hi.
  - destruct (IH Hc Hdt) as [s [Hs IH']].
    { rewrite rev_two, <- app_assoc. cbn [rev] in Hok. rewrite <- app_assoc in Hok. apply ok_fire; [exact Hdh | exact Hok]. }
    exists s. split; [exact Hs|]. intros i Hi. apply RP_fire; [exact Hdh|]. apply IH'; exact Hi.
  - exfalso. cbn in Hok. apply Hok. reflexivity.
  - exfalso. cbn in Hok. apply Hok. reflexivity.
  - assert (Ee: e = sc dh) by (destruct Hde as [[-> ->] | [-> ->]]; reflexivity).
    assert (Hs: ok false (rev rout ++ [e; Dm] ++ ds)).
    { rewrite Ee. apply ok_trig; [destruct Hde as [[-> _] | [-> _]]; auto|]. cbn [rev] in Hok. rewrite <- app_assoc in Hok. exact Hok. }
    assert (Hs1: ok false (rev [] ++ rev (e :: rout))).
    { cbn [rev app]. apply (ok_prefix _ _ (Dm :: ds)). rewrite <- app_assoc. exact Hs. }
    destruct (rp_mono _ _ _ _ _ _ H1 Hdt (Dm :: ds)) as [Et Hs2]; [cbn [rev app]; rewrite <- app_assoc; exact Hs|].
    subst tp1.
    destruct (IH1 Hc Hdt Hs1) as [s1 [Hl1 IH1']]. destruct (IH2 Hc Hdt Hs2) as [s2 [Hl2 IH2']].
    exists (S (s1 + s2)). split; [rewrite !length_app, Hl1, Hl2; cbn [length]; lia|].
    intros i Hi.
    replace (TR ct i (S (s1 + s2))) with (TR ct (S i + s1) s2 ++ (TR ct (S i) s1 ++ ct i) ++ [1;1;1])
      by (cbn [TR]; rewrite TR_add, <- !app_assoc; reflexivity).
    replace (i + S (s1 + s2)) with (S i + s1 + s2) by lia.
    eapply RP_trig; [exact Htp | exact Hde | |].
    + cbn [app]. rewrite rev_lift. eapply rp_app; [apply Hc; lia|]. exact (IH1' (S i) ltac:(lia)).
    + exact (IH2' (S i + s1) ltac:(lia)).
Qed.

Inductive IInc (tp : top) : list dg -> dg -> list dg -> dg -> list Sym -> Prop :=
  | II_fast ws d0 : d0 = D0 \/ d0 = D2 -> IInc tp ws d0 ws (sc d0) []
  | II_low1 t ts tx rout : RP tp [] (t :: ts) tx tp rout -> IInc tp (t :: ts) D1 (rev rout) D2 (tx ++ [1;1;1])
  | II_low3 t ts tx d1 rest : (d1 = D0 \/ d1 = D2) -> RP tp [] (t :: ts) tx tp (d1 :: rest) ->
      IInc tp (t :: ts) D3 (rev rest ++ [sc d1]) D0 (tx ++ [1;1;1])
  | II_trans t ts tx d1 e rest tx2 rout2 : ((d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2)) ->
      RP tp [] (t :: ts) tx tp (d1 :: rest) -> RP tp [] (rev (e :: rest)) tx2 tp rout2 ->
      IInc tp (t :: ts) D3 (rev rout2) D0 (tx2 ++ [1;1;1] ++ tx ++ [1;1;1]).

Lemma rev_lift2 (rout X : list dg): rev (rout ++ rev X) = X ++ rev rout.
Proof. rewrite rev_app_distr, rev_involutive. reflexivity. Qed.
Lemma II_low1' tp ws tx rout: ws <> [] -> RP tp [] ws tx tp rout -> IInc tp ws D1 (rev rout) D2 (tx ++ [1;1;1]).
Proof. destruct ws as [|t ts]; [congruence|]. intros _. apply II_low1. Qed.
Lemma II_low3' tp ws tx d1 rest: ws <> [] -> (d1 = D0 \/ d1 = D2) -> RP tp [] ws tx tp (d1 :: rest) ->
  IInc tp ws D3 (rev rest ++ [sc d1]) D0 (tx ++ [1;1;1]).
Proof. destruct ws as [|t ts]; [congruence|]. intros _. apply II_low3. Qed.
Lemma II_trans' tp ws tx d1 e rest tx2 rout2: ws <> [] -> ((d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2)) ->
  RP tp [] ws tx tp (d1 :: rest) -> RP tp [] (rev (e :: rest)) tx2 tp rout2 ->
  IInc tp ws D3 (rev rout2) D0 (tx2 ++ [1;1;1] ++ tx ++ [1;1;1]).
Proof. destruct ws as [|t ts]; [congruence|]. intros _. apply II_trans. Qed.
Lemma app_cons_nn {A} (X : list A) t ts: X ++ t :: ts <> [].
Proof. destruct X; discriminate. Qed.
Lemma iinc_liftg ctx ct n tp Xw d0 Xw' d0' g: IInc tp Xw d0 Xw' d0' g ->
  (forall i, i < n -> RP tp [] (ctx i) (ct i) tp (rev (ctx (S i)))) -> dtop tp -> Inv Xw d0 ->
  exists k, length g = 3 * k /\ ((d0 = D0 \/ d0 = D2) -> k = O) /\ ((d0 = D1 \/ d0 = D3) -> 1 <= k) /\
    forall i, i + k <= n -> IInc tp (ctx i ++ Xw) d0 (ctx (i + k) ++ Xw') d0' (TR ct i k).
Proof.
  intros HI Hc Hdt Hinv. destruct HI as [ws d0 Hd0 | t ts tx rout Hr | t ts tx d1 rest Hd1 Hr | t ts tx d1 e rest tx2 rout2 Hde Hr Hr2].
  - exists O. split; [reflexivity|]. split; [auto|]. split; [destruct Hd0 as [-> | ->]; intros [E|E]; discriminate|].
    intros i _. rewrite Nat.add_0_r. apply II_fast; exact Hd0.
  - assert (H0: ok false (rev [] ++ t :: ts)) by (cbn [rev app]; apply (ok_prefix _ _ [lowc D1]); exact Hinv).
    destruct (rp_ctxg ctx ct n _ _ _ _ _ _ Hr Hc Hdt H0) as [s [Hs Hl]].
    exists (S s). split; [rewrite length_app, Hs; cbn; lia|]. split; [intros [E|E]; discriminate|]. split; [lia|]. intros i Hi.
    replace (ctx (i + S s) ++ rev rout) with (rev (rout ++ rev (ctx (S i + s)))) by (rewrite rev_lift2; f_equal; f_equal; lia).
    cbn [TR]. rewrite app_assoc. apply II_low1'; [apply app_cons_nn|].
    eapply rp_app; [apply Hc; lia|]. exact (Hl (S i) ltac:(lia)).
  - assert (H0: ok false (rev [] ++ t :: ts)) by (cbn [rev app]; apply (ok_prefix _ _ [lowc D3]); exact Hinv).
    destruct (rp_ctxg ctx ct n _ _ _ _ _ _ Hr Hc Hdt H0) as [s [Hs Hl]].
    exists (S s). split; [rewrite length_app, Hs; cbn; lia|]. split; [intros [E|E]; discriminate|]. split; [lia|]. intros i Hi.
    replace (ctx (i + S s) ++ rev rest ++ [sc d1]) with (rev (rest ++ rev (ctx (S i + s))) ++ [sc d1])
      by (rewrite rev_lift2, app_assoc; f_equal; f_equal; f_equal; lia).
    cbn [TR]. rewrite app_assoc. apply II_low3'; [apply app_cons_nn | exact Hd1|].
    eapply rp_app; [apply Hc; lia|]. exact (Hl (S i) ltac:(lia)).
  - assert (H0: ok false (rev [] ++ t :: ts)) by (cbn [rev app]; apply (ok_prefix _ _ [lowc D3]); exact Hinv).
    destruct (rp_ctxg ctx ct n _ _ _ _ _ _ Hr Hc Hdt H0) as [s [Hs Hl]].
    destruct (rp_mono _ _ _ _ _ _ Hr Hdt [D3]) as [_ Hm]; [cbn [rev app]; exact Hinv|].
    cbn [rev] in Hm. rewrite <- app_assoc in Hm. cbn [app] in Hm.
    assert (Ee: e = sc d1) by (destruct Hde as [[-> ->] | [-> ->]]; reflexivity).
    assert (H2: ok false (rev [] ++ rev (e :: rest))).
    { cbn [rev app]. apply (ok_prefix _ _ [Dm]). rewrite <- app_assoc. rewrite Ee.
      apply (ok_trig false (rev rest) d1 []); [destruct Hde as [[-> _] | [-> _]]; auto | exact Hm]. }
    destruct (rp_ctxg ctx ct n _ _ _ _ _ _ Hr2 Hc Hdt H2) as [s2 [Hs2 Hl2]].
    exists (S s + S s2). split; [rewrite !length_app, Hs, Hs2; cbn; lia|]. split; [intros [E|E]; discriminate|]. split; [lia|].
    intros i Hi.
    rewrite TR_add. cbn [TR]. replace (i + S s) with (S i + s) by lia.
    replace (ctx (i + (S s + S s2)) ++ rev rout2) with (rev (rout2 ++ rev (ctx (S (S i + s) + s2))))
      by (rewrite rev_lift2; f_equal; f_equal; lia).
    replace ((TR ct (S (S i + s)) s2 ++ ct (S i + s) ++ [1;1;1]) ++ TR ct (S i) s ++ ct i ++ [1;1;1])
      with ((TR ct (S (S i + s)) s2 ++ ct (S i + s)) ++ [1;1;1] ++ (TR ct (S i) s ++ ct i) ++ [1;1;1])
      by (rewrite <- !app_assoc; reflexivity).
    apply II_trans' with (d1 := d1) (e := e) (rest := rest ++ rev (ctx (S i + s)));
      [apply app_cons_nn | exact Hde | |].
    + eapply rp_app; [apply Hc; lia|]. exact (Hl (S i) ltac:(lia)).
    + rewrite rev_lift. eapply rp_app; [apply Hc; lia|]. exact (Hl2 (S (S i + s)) ltac:(lia)).
Qed.
Definition ctxW a i := U (a - i) i.
Lemma ctxW_ok tp a i: i < a -> RP tp [] (ctxW a i) [] tp (rev (ctxW a (S i))).
Proof. intros H. unfold ctxW. replace (a - i) with (S (a - S i)) by lia. apply rp_wave. Qed.

Lemma ones_sides (l : side) a b: l <* [1]^^a <* [1]^^b = l <* [1]^^(b + a).
Proof. rewrite side_app, <- lpow_add. reflexivity. Qed.
Lemma ok_swap_stop s X d e: (d = Dm \/ d = D0 \/ d = D1) -> (e = Dm \/ e = D0 \/ e = D1) -> ok s (X ++ [d]) -> ok s (X ++ [e]).
Proof.
  intros Hd He H. apply ok_stop; [exact He|]. destruct (ok_app_l _ _ _ H) as [s' [E _]]. unfold ok; rewrite E; discriminate.
Qed.
Lemma ok_low3_0 s X: ok s (X ++ [D0; D3]) -> ok s (X ++ [D1; D0]).
Proof. intros H. destruct (ok_app_l _ _ _ H) as [s0 [E _]]. apply (ok_app_r _ _ _ _ E). unfold ok; cbn; discriminate. Qed.
Lemma ok_low3_2 s X: ok s (X ++ [D2; D3]) -> ok s (X ++ [D3; D0]).
Proof.
  intros H. destruct (ok_app_l _ _ _ H) as [s0 [E H0]]. apply (ok_app_r _ _ _ _ E).
  unfold ok in *; cbn in *. destruct s0; [discriminate | exfalso; apply H0; reflexivity].
Qed.
Lemma wv_snoc ws d: wv (ws ++ [d]) = (4 * wv ws + dv d)%Z.
Proof. rewrite wv_app. cbn [wv length]. zring. Qed.
Lemma lpow1_length k: length ([1]^^k) = k.
Proof. induction k as [|k IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma iinc_exists tp ws d0: dtop tp -> Inv ws d0 -> d0 <> Dm -> (d0 = D1 -> exists d, In d ws /\ d <> D2) ->
  exists ws' d0' N, IInc tp ws d0 ws' d0' ([1]^^N) /\ Inv ws' d0' /\ d0' <> Dm /\
    length ws' = length ws /\ wv (ws' ++ [d0']) = (wv (ws ++ [d0]) + 1)%Z /\ N + cls (ws' ++ [d0']) = cls (ws ++ [d0]) + 2.
Proof.
  intros Hdt HI Hd0 Hc. destruct d0; [congruence | | | | ].
  - exists ws, D1, O. split; [apply (II_fast tp ws D0); auto|].
    unfold Inv in *; cbn [lowc] in *.
    split; [apply (ok_swap_stop _ _ D0); auto|]. split; [discriminate|]. split; [reflexivity|].
    rewrite !wv_snoc, !cls_app. cbn [dv cls cl app]. lia.
  - destruct (Hc eq_refl) as [d [Hin Hne]].
    destruct ws as [|t ts]; [contradiction|].
    assert (H0: ok false (rev [] ++ t :: ts)) by (cbn [rev app]; apply (ok_prefix _ _ [lowc D1]); exact HI).
    destruct (rp_exists tp Hdt (length (t :: ts)) (count3 (t :: ts)) (length (t :: ts)) [] (t :: ts)) as [tx [rout Hr]];
      [cbn; lia | lia | lia | exact H0 |].
    destruct (rp_meas _ _ _ _ _ _ Hr Hdt H0) as [L1 [C1 [V1 [k Ek]]]]. subst tx.
    exists (rev rout), D2, (k + 3)%nat. split.
    + replace ([1]^^(k + 3)) with ([1]^^k ++ [1;1;1]) by (rewrite lpow_add; reflexivity). apply II_low1. exact Hr.
    + split; [apply (ok_after_pass tp (t :: ts) ([1]^^k) rout Hr Hdt); [cbn [rev app] in H0; exact H0 | exists d; auto]|].
      split; [discriminate|]. split; [rewrite length_rev, L1; reflexivity|].
      rewrite lpow1_length in C1. cbn [rev app] in V1.
      split; [rewrite !wv_snoc, V1; cbn [dv]; lia | rewrite !cls_app, cls_rev; cbn [cls cl] in *; lia].
  - exists ws, D3, O. split; [apply (II_fast tp ws D2); auto|].
    split; [exact HI|]. split; [discriminate|]. split; [reflexivity|].
    rewrite !wv_snoc, !cls_app. cbn [dv cls cl app]. lia.
  - destruct ws as [|t ts]; [exfalso; unfold Inv, ok in HI; cbn in HI; apply HI; reflexivity|].
    assert (H0: ok false (rev [] ++ t :: ts)) by (cbn [rev app]; apply (ok_prefix _ _ [lowc D3]); exact HI).
    destruct (rp_exists tp Hdt (length (t :: ts)) (count3 (t :: ts)) (length (t :: ts)) [] (t :: ts)) as [tx [rout Hr]];
      [cbn; lia | lia | lia | exact H0 |].
    destruct (rp_mono _ _ _ _ _ _ Hr Hdt [D3]) as [_ Hm]; [cbn [rev app]; exact HI|].
    destruct (rp_meas _ _ _ _ _ _ Hr Hdt H0) as [L1 [C1 [V1 [k Ek]]]]. subst tx.
    destruct rout as [|d1 rest]; [cbn in L1; discriminate|].
    cbn [rev] in Hm, V1. rewrite <- app_assoc in Hm. cbn [app] in Hm. cbn [rev app] in V1.
    rewrite lpow1_length in C1. cbn [cls] in C1.
    assert (Hd1: (d1 = Dm \/ d1 = D1) \/ (d1 = D0 \/ d1 = D2) \/ d1 = D3) by (destruct d1; auto).
    destruct Hd1 as [Hde | [Hd1 | ->]].
    + (* a trigger: a second pass *)
      assert (Hs: ok false (rev rest ++ [sc d1; Dm] ++ [])) by (apply ok_trig; auto).
      assert (H2: ok false (rev [] ++ rev (sc d1 :: rest))) by (cbn [rev app]; apply (ok_prefix _ _ [Dm]); rewrite <- app_assoc; exact Hs).
      destruct (rp_exists tp Hdt (length (rev (sc d1 :: rest))) (count3 (rev (sc d1 :: rest))) (length (rev (sc d1 :: rest))) []
        (rev (sc d1 :: rest))) as [tx2 [rout2 Hr2]]; [cbn [length]; lia | lia | lia | exact H2 |].
      destruct (rp_mono _ _ _ _ _ _ Hr2 Hdt []) as [_ Hm2]; [rewrite app_nil_r; exact H2|]. rewrite app_nil_r in Hm2.
      destruct (rp_meas _ _ _ _ _ _ Hr2 Hdt H2) as [L2 [C2 [V2 [k2 Ek2]]]]. subst tx2.
      exists (rev rout2), D0, (k2 + 3 + k + 3)%nat. split.
      * replace ([1]^^(k2 + 3 + k + 3)) with ([1]^^k2 ++ [1;1;1] ++ [1]^^k ++ [1;1;1]) by (rewrite !lpow_add, <- !app_assoc; reflexivity).
        apply (II_trans tp t ts ([1]^^k) d1 (sc d1) rest ([1]^^k2) rout2); [destruct Hde as [-> | ->]; [left | right]; split; reflexivity | exact Hr | exact Hr2].
      * split; [apply (ok_stop false (rev rout2) D0); auto|]. split; [discriminate|].
        split; [rewrite length_rev, L2, length_rev; cbn [length] in *; lia|].
        rewrite lpow1_length in C2. cbn [rev app] in V2. rewrite cls_rev in C2.
        destruct Hde as [-> | ->]; cbn [cls cl sc] in C2, V2 |- *;
          (split; [rewrite !wv_snoc, V2, <- V1, !wv_snoc; cbn [dv]; lia | rewrite !cls_app, cls_rev; cbn [cls cl] in *; lia]).
    + (* a carry into 0 or 2 *)
      exists (rev rest ++ [sc d1]), D0, (k + 3)%nat. split.
      * replace ([1]^^(k + 3)) with ([1]^^k ++ [1;1;1]) by (rewrite lpow_add; reflexivity). apply II_low3; [exact Hd1 | exact Hr].
      * split; [unfold Inv; cbn [lowc]; rewrite <- app_assoc; destruct Hd1 as [-> | ->]; [apply ok_low3_0 | apply ok_low3_2]; exact Hm|].
        split; [discriminate|]. split; [rewrite length_app, length_rev; cbn [length] in *; lia|].
        destruct Hd1 as [-> | ->]; cbn [sc] in *;
          (split; [rewrite !wv_snoc, <- V1, !wv_snoc; cbn [dv]; lia | rewrite !cls_app, cls_rev; cbn [cls cl] in *; lia]).
    + exfalso. apply (ok_33 false (rev rest) []). exact Hm.
Qed.

Lemma wv_dm k: (3 * wv (repeat Dm k) = - (4 ^ Z.of_nat k - 1))%Z.
Proof.
  induction k as [|k IH]; cbn [repeat wv length]; [reflexivity|].
  rewrite repeat_length, Nat2Z.inj_succ, Z.pow_succ_r by lia. cbn [dv]. lia.
Qed.
Lemma cls_dm k: cls (repeat Dm k) = 7 * k.
Proof. induction k as [|k IH]; cbn [repeat cls cl]; lia. Qed.
Definition lv (w : list dg) : Z := (3 * wv w + 4 ^ Z.of_nat (length w))%Z.
Lemma lv_dm k w: lv (repeat Dm k ++ w) = lv w.
Proof.
  unfold lv. rewrite wv_app, length_app, repeat_length, Nat2Z.inj_add, Z.pow_add_r by lia.
  rewrite Z.mul_add_distr_l, Z.mul_assoc, wv_dm. ring.
Qed.
Lemma lv_snoc w d: lv (w ++ [d]) = (4 * lv w + 3 * dv d)%Z.
Proof.
  unfold lv. rewrite wv_snoc, length_app, Nat.add_comm. cbn [length Nat.add].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.
Lemma inv_unique2 e: forall w c s, length w = e + length c -> ok s w -> Forall pos012 c ->
  wv w = wv (repeat Dm e ++ c) -> w = repeat Dm e ++ c.
Proof.
  induction e as [|e IH]; intros w c s Hl Hok Hc Hv.
  - exact (inv_unique w c s Hl Hok Hc Hv).
  - destruct w as [|d w]; [discriminate|]. cbn [length] in Hl. injection Hl as Hl.
    assert (E: (3 * wv (repeat Dm e ++ c) = 4 ^ Z.of_nat (length c) - 4 ^ Z.of_nat (length w) + 3 * wv c)%Z).
    { rewrite Hl, Nat2Z.inj_add, Z.pow_add_r by lia. rewrite wv_app, Z.mul_add_distr_l, Z.mul_assoc, wv_dm. ring. }
    assert (Ln: length (repeat Dm e ++ c) = length w) by (rewrite length_app, repeat_length; lia).
    pose proof (wv_lower w) as L. destruct (wv_pos012 c Hc) as [_ U2].
    assert (HP: (4 ^ Z.of_nat (length c) <= 4 ^ Z.of_nat (length w))%Z) by (apply Z.pow_le_mono_r; lia).
    cbn [repeat app wv] in Hv. rewrite Ln in Hv.
    destruct d; cbn [dv] in Hv; try (exfalso; lia).
    cbn [repeat app]. f_equal. apply (IH w c true); [exact Hl | | exact Hc | lia].
    unfold ok in *. cbn [scan] in Hok. exact Hok.
Qed.
Definition par d := match d with D1 | D3 => true | _ => false end.
Lemma iinc_par tp ws d0 ws' d0' g: IInc tp ws d0 ws' d0' g -> par d0' = negb (par d0).
Proof. intros H. destruct H as [ws d0 Hd | | | ]; try reflexivity. destruct Hd as [-> | ->]; reflexivity. Qed.
Lemma iinc_nil tp ws d0 ws' d0' g: IInc tp ws d0 ws' d0' g -> g = [] -> ws' = ws.
Proof.
  intros H. destruct H; intros Hg; [reflexivity | ..]; exfalso; repeat (apply app_eq_nil in Hg; destruct Hg as [_ Hg]); discriminate.
Qed.
Lemma ok_dm k l: ok true l -> ok true (repeat Dm k ++ l).
Proof. induction k as [|k IH]; intros H; [exact H|]. unfold ok in *. cbn [repeat app scan]. apply IH. exact H. Qed.
Lemma inv_dm k L d: Inv L d -> Inv (repeat Dm k ++ L) d.
Proof.
  unfold Inv. intros H. destruct k as [|k]; [exact H|]. rewrite <- app_assoc.
  unfold ok. cbn [repeat app scan]. apply (ok_dm k (L ++ [lowc d])). apply ok_mono. exact H.
Qed.

Inductive VRun (tp : top) : list dg -> dg -> nat -> list dg -> dg -> nat -> Prop :=
  | VR0 L d0 : VRun tp L d0 O L d0 O
  | VRS L d0 L1 d1 k n L2 d2 K : IInc tp L d0 L1 d1 ([1]^^(3 * k)) -> Inv L d0 -> length L1 = length L ->
      wv (L1 ++ [d1]) = (wv (L ++ [d0]) + 1)%Z -> 3 * k + cls (L1 ++ [d1]) = cls (L ++ [d0]) + 2 ->
      VRun tp (repeat Dm k ++ L1) d1 n L2 d2 K -> VRun tp L d0 (S n) L2 d2 (k + K).
Lemma vrun_meas tp L d0 n L' d0' K: VRun tp L d0 n L' d0' K ->
  length L' = length L + K /\ lv (L' ++ [d0']) = (lv (L ++ [d0]) + 3 * Z.of_nat n)%Z /\
  cls (L' ++ [d0']) + 3 * K = cls (L ++ [d0]) + 2 * n + 7 * K /\ par d0' = xorb (par d0) (Nat.odd n).
Proof.
  induction 1 as [L d0 | L d0 L1 d1 k n L2 d2 K HI HIv Hl Hv Hc H IH].
  - repeat split; [lia | lia | lia |]. destruct (par d0); reflexivity.
  - destruct IH as [IHl [IHv [IHc IHp]]].
    rewrite <- app_assoc, lv_dm in IHv. rewrite <- app_assoc, (cls_app (repeat Dm k) (L1 ++ [d1])), cls_dm in IHc.
    rewrite length_app, repeat_length, Hl in IHl.
    assert (E: lv (L1 ++ [d1]) = (lv (L ++ [d0]) + 3)%Z) by (unfold lv; rewrite Hv, !length_app, Hl; cbn [length]; lia).
    repeat split; [lia | rewrite IHv, E, Nat2Z.inj_succ; lia | lia |].
    rewrite IHp, (iinc_par _ _ _ _ _ _ HI), Nat.odd_succ, <- Nat.negb_odd.
    destruct (par d0), (Nat.odd n); reflexivity.
Qed.
Lemma vrun_exists tp: dtop tp -> forall n L d0, Inv L d0 -> d0 <> Dm -> (exists d, In d L /\ d <> D2) ->
  exists L' d0' K, VRun tp L d0 n L' d0' K /\ Inv L' d0' /\ d0' <> Dm /\ (exists d, In d L' /\ d <> D2).
Proof.
  intros Hdt; induction n as [|n IH]; intros L d0 HI Hd0 Hx.
  - exists L, d0, O. split; [constructor|]. auto.
  - destruct (iinc_exists tp L d0 Hdt HI Hd0) as [L1 [d1 [N [HII [HI1 [Hd1 [Hl [Hv Hc]]]]]]]]; [intros _; exact Hx|].
    destruct (iinc_liftg (ctxW O) (fun _ => []) O _ _ _ _ _ _ HII ltac:(intros; exfalso; lia) Hdt HI) as [k [Hk _]]. rewrite lpow1_length in Hk. subst N.
    assert (Hx1: exists d, In d (repeat Dm k ++ L1) /\ d <> D2).
    { destruct k as [|k].
      - rewrite (iinc_nil _ _ _ _ _ _ HII eq_refl). exact Hx.
      - exists Dm. split; [left; reflexivity | discriminate]. }
    destruct (IH (repeat Dm k ++ L1) d1 (inv_dm k L1 d1 HI1) Hd1 Hx1) as [L' [d0' [K [HR [HI' [Hd' Hx']]]]]].
    exists L', d0', (k + K). split; [|auto].
    eapply VRS; [exact HII | exact HI | exact Hl | exact Hv | lia | exact HR].
Qed.

Lemma lv_upper w n: ok false w -> length w <= n -> (lv w <= 3 * 4 ^ Z.of_nat n - 2)%Z.
Proof.
  intros H Hn. pose proof (wv_upper w false H) as U. cbv beta iota in U.
  assert (4 ^ Z.of_nat (length w) <= 4 ^ Z.of_nat n)%Z by (apply Z.pow_le_mono_r; lia).
  unfold lv. lia.
Qed.
Lemma low_unique L d c y: Inv L d -> d <> Dm -> y <> Dm -> Forall pos012 c -> length c <= length L ->
  lv (L ++ [d]) = lv (c ++ [y]) -> L = repeat Dm (length L - length c) ++ c /\ d = y.
Proof.
  intros HI Hd Hy Hc Hl Hv.
  assert (Ev: lv (L ++ [d]) = lv ((repeat Dm (length L - length c) ++ c) ++ [y])) by (rewrite <- app_assoc, lv_dm; exact Hv).
  assert (Le: length (L ++ [d]) = length ((repeat Dm (length L - length c) ++ c) ++ [y]))
    by (rewrite !length_app, repeat_length; cbn [length]; lia).
  unfold lv in Ev. rewrite Le in Ev. rewrite (wv_snoc L), (wv_snoc (repeat Dm (length L - length c) ++ c)) in Ev.
  assert (Edy: d = y) by (destruct d, y; cbn [dv] in Ev; try congruence; lia).
  subst y. split; [|reflexivity].
  apply (inv_unique2 _ L c false); [lia | apply (ok_prefix _ _ [lowc d]); exact HI | exact Hc | lia].
Qed.

Lemma lv_app X Y: lv (X ++ Y) = ((lv X - 1) * 4 ^ Z.of_nat (length Y) + lv Y)%Z.
Proof. unfold lv. rewrite wv_app, length_app, Nat2Z.inj_add, Z.pow_add_r by lia. ring. Qed.
Lemma lv_rep2 j: lv (repeat D2 j) = (3 * 4 ^ Z.of_nat j - 2)%Z.
Proof. unfold lv. rewrite repeat_length, all2_wv. ring. Qed.

Definition cE j := [D0;D1;D1] ++ repeat D2 j ++ [D1].
Definition cO j := [D2;D0;D0] ++ repeat D2 j ++ [D1].
Lemma cE_len j: length (cE j) = j + 4.
Proof. unfold cE. rewrite !length_app, repeat_length. cbn. lia. Qed.
Lemma cO_len j: length (cO j) = j + 4.
Proof. unfold cO. rewrite !length_app, repeat_length. cbn. lia. Qed.
Lemma cls_rep2 j: cls (repeat D2 j) = 7 * j.
Proof. induction j as [|j IH]; cbn [repeat cls cl]; lia. Qed.
Lemma cE_cls j: cls (cE j) = 7 * j + 30.
Proof. unfold cE. rewrite !cls_app, cls_rep2. cbn. lia. Qed.
Lemma cO_cls j: cls (cO j) = 7 * j + 27.
Proof. unfold cO. rewrite !cls_app, cls_rep2. cbn. lia. Qed.
Lemma lv_x3 (x : list dg) j: lv (x ++ repeat D2 j ++ [D1; D3]) =
  ((lv x - 1) * (16 * 4 ^ Z.of_nat j) + 48 * 4 ^ Z.of_nat j - 11)%Z.
Proof.
  rewrite (lv_app x), (lv_app (repeat D2 j)), lv_rep2, !length_app, repeat_length.
  change (lv [D1; D3]) with 37%Z. cbn [length].
  rewrite Nat2Z.inj_add, Z.pow_add_r by lia. change (4 ^ Z.of_nat 2)%Z with 16%Z. ring.
Qed.
Lemma cE_lv j: lv (cE j ++ [D3]) = (1296 * 4 ^ Z.of_nat j - 11)%Z.
Proof. unfold cE. rewrite <- !app_assoc. change ([D1] ++ [D3]) with [D1; D3]. rewrite lv_x3. change (lv [D0;D1;D1]) with 79%Z. ring. Qed.
Lemma cO_lv j: lv (cO j ++ [D3]) = (2592 * 4 ^ Z.of_nat j - 11)%Z.
Proof. unfold cO. rewrite <- !app_assoc. change ([D1] ++ [D3]) with [D1; D3]. rewrite lv_x3. change (lv [D2;D0;D0]) with 160%Z. ring. Qed.
Lemma pos012_repeat2 j: Forall pos012 (repeat D2 j).
Proof. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold pos012; auto. Qed.
Lemma cE_pos j: Forall pos012 (cE j).
Proof.
  unfold cE. apply Forall_app; split; [|apply Forall_app; split; [apply pos012_repeat2|]];
    repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto.
Qed.
Lemma cO_pos j: Forall pos012 (cO j).
Proof.
  unfold cO. apply Forall_app; split; [|apply Forall_app; split; [apply pos012_repeat2|]];
    repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto.
Qed.
Lemma count3_cE j: count3 (cE j) = O.
Proof. unfold cE. rewrite !count3_app, count3_repeat2. reflexivity. Qed.
Lemma count3_cO j: count3 (cO j) = O.
Proof. unfold cO. rewrite !count3_app, count3_repeat2. reflexivity. Qed.
Lemma rev_cE j: rev (cE j) = D1 :: repeat D2 j ++ [D1;D1;D0].
Proof. unfold cE. rewrite !rev_app_distr, rev_repeat. reflexivity. Qed.
Lemma rev_cO j: rev (cO j) = D1 :: repeat D2 j ++ [D0;D0;D2].
Proof. unfold cO. rewrite !rev_app_distr, rev_repeat. reflexivity. Qed.

Lemma vrun_top tp n c L' d0' K: VRun tp [Dm] D2 n L' d0' K -> Inv L' d0' -> d0' <> Dm -> Forall pos012 c ->
  lv (c ++ [D3]) = (10 + 3 * Z.of_nat n)%Z -> (3 * 4 ^ Z.of_nat (length c) - 2 < 10 + 3 * Z.of_nat n)%Z ->
  L' = repeat Dm (S K - length c) ++ c /\ d0' = D3 /\ length c <= S K /\
  7 * (S K - length c) + cls c + 9 + 3 * K = 14 + 2 * n + 7 * K.
Proof.
  intros HR HI Hd Hc Hlv Hb.
  destruct (vrun_meas _ _ _ _ _ _ _ HR) as [Hl [Hv [Hcl _]]]. cbn [length] in Hl.
  assert (Hlv': lv (L' ++ [d0']) = (10 + 3 * Z.of_nat n)%Z) by (rewrite Hv; reflexivity).
  assert (Hlen: length c <= length L').
  { destruct (Nat.le_gt_cases (length c) (length L')) as [H|H]; [exact H|]. exfalso.
    pose proof (lv_upper (L' ++ [d0']) (length c) (Inv_word _ _ HI)) as U.
    rewrite length_app in U. cbn [length] in U. specialize (U ltac:(lia)). lia. }
  destruct (low_unique L' d0' c D3 HI Hd ltac:(discriminate) Hc Hlen) as [EL Ed]; [rewrite Hlv'; symmetry; exact Hlv|].
  rewrite Hl in EL, Hlen. subst d0'. split; [exact EL|]. split; [reflexivity|]. split; [lia|].
  rewrite EL, <- app_assoc, cls_app, cls_dm, cls_app in Hcl. cbn [cls cl app] in Hcl. lia.
Qed.

Definition is3 d := match d with D3 => true | _ => false end.
Fixpoint sv (p : bool) (l : list dg) : bool :=
  match l with
  | [] => true
  | d :: l => andb (if p then match d with D2 | D3 => false | _ => true end else true) (sv (is3 d) l)
  end.
Fixpoint s3m (l : list dg) : bool :=
  match l with [] => true | D3 :: (Dm :: _) as l => s3m l | D3 :: _ => false | _ :: l => s3m l end.
Fixpoint lst (p : bool) (l : list dg) : bool := match l with [] => p | d :: l => lst (is3 d) l end.
Lemma sv_app p X Y: sv p (X ++ Y) = andb (sv p X) (sv (lst p X) Y).
Proof. revert p; induction X as [|d X IH]; intros p; cbn [app sv lst]; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma sv_mono l: sv true l = true -> sv false l = true.
Proof. intros H. destruct l as [|d l]; [reflexivity|]. destruct d; cbn in *; congruence. Qed.
Lemma s3m_lst X: s3m X = true -> lst false X = false.
Proof.
  induction X as [|d X IH]; [reflexivity|]. intros H.
  destruct d; cbn [s3m lst is3] in *; try (apply IH; exact H).
  destruct X as [|e X]; [discriminate|]. destruct e; try discriminate. cbn [lst is3] in *. apply IH. exact H.
Qed.
Lemma s3m_sv X: s3m X = true -> sv false X = true.
Proof.
  induction X as [|d X IH]; [reflexivity|]. intros H.
  destruct d; cbn [s3m sv is3 andb] in *; try (apply IH; exact H).
  destruct X as [|e X]; [discriminate|]. destruct e; try discriminate. cbn [sv is3 andb] in *. apply IH. exact H.
Qed.
Lemma s3m_snoc X d: s3m X = true -> d <> D3 -> s3m (X ++ [d]) = true.
Proof.
  induction X as [|x X IH]; intros H Hd; [destruct d; cbn; congruence|].
  destruct x; cbn [app s3m] in *; try (apply IH; [exact H | exact Hd]).
  destruct X as [|e X]; [discriminate|]. destruct e; try discriminate. cbn [app s3m] in *. apply IH; [exact H | exact Hd].
Qed.
Lemma s3m_snoc3 X: s3m X = true -> s3m (X ++ [D3; Dm]) = true.
Proof.
  induction X as [|x X IH]; intros H; [reflexivity|].
  destruct x; cbn [app s3m] in *; try (apply IH; exact H).
  destruct X as [|e X]; [discriminate|]. destruct e; try discriminate. cbn [app s3m] in *. apply IH. exact H.
Qed.
Lemma s3m_unsnoc X d: d <> Dm -> s3m (X ++ [d]) = true -> s3m X = true.
Proof.
  intros Hd. induction X as [|x X IH]; intros H; [reflexivity|].
  destruct x; cbn [app s3m] in *; try (apply IH; exact H).
  destruct X as [|e X]; [destruct d; cbn in H; congruence|]. destruct e; try discriminate. cbn [app s3m] in *. apply IH. exact H.
Qed.
Lemma rp_s3m tp rout ds tx tp' rout': RP tp rout ds tx tp' rout' -> s3m (rev rout) = true -> s3m (rev rout') = true.
Proof.
  induction 1 as [tp rout | tp rout d ds tx tp' rout' Hd _ IH | tp rout dh ds tx tp' rout' Hdh _ IH
                 | ds tx tp' rout' _ IH | ds tx tp' rout' _ IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde _ IH1 _ IH2]; intros H.
  - exact H.
  - apply IH. cbn [rev]. apply s3m_snoc; [exact H | exact Hd].
  - apply IH. rewrite rev_two. cbn [rev] in H.
    assert (H0: s3m (rev rout) = true) by (apply (s3m_unsnoc _ dh); [destruct Hdh as [-> | ->]; discriminate | exact H]).
    destruct Hdh as [-> | ->]; cbn [sc]; [| apply s3m_snoc3; exact H0].
    replace (rev rout ++ [D1; Dm]) with ((rev rout ++ [D1]) ++ [Dm]) by (rewrite <- app_assoc; reflexivity).
    apply s3m_snoc; [apply s3m_snoc; [exact H0 | discriminate] | discriminate].
  - apply IH. reflexivity.
  - apply IH. reflexivity.
  - apply IH2. apply IH1. reflexivity.
Qed.
Lemma iinc_sv tp ws d0 ws' d0' g: IInc tp ws d0 ws' d0' g -> sv false (ws ++ [d0]) = true -> sv false (ws' ++ [d0']) = true.
Proof.
  intros HI. destruct HI as [ws d0 Hd0 | t ts tx rout Hr | t ts tx d1 rest Hd1 Hr | t ts tx d1 e rest tx2 rout2 Hde Hr Hr2]; intros H.
  - rewrite sv_app in *. apply andb_true_iff in H as [H1 H2]. rewrite H1. cbn [andb].
    revert H2. destruct (lst false ws); intros H2; [destruct Hd0 as [-> | ->]; cbn in *; congruence | reflexivity].
  - apply s3m_sv, s3m_snoc; [apply (rp_s3m _ _ _ _ _ _ Hr); reflexivity | discriminate].
  - pose proof (rp_s3m _ _ _ _ _ _ Hr eq_refl) as S. cbn [rev] in S.
    assert (Hd: d1 <> Dm) by (destruct Hd1 as [-> | ->]; discriminate).
    assert (S0: s3m (rev rest) = true) by (exact (s3m_unsnoc _ _ Hd S)).
    rewrite <- app_assoc, sv_app, (s3m_sv _ S0), (s3m_lst _ S0). cbn [app].
    destruct Hd1 as [-> | ->]; reflexivity.
  - apply s3m_sv, s3m_snoc; [apply (rp_s3m _ _ _ _ _ _ Hr2); reflexivity | discriminate].
Qed.
Lemma sv_3free l: count3 l = O -> sv false l = true.
Proof. induction l as [|d l IH]; intros H; [reflexivity|]. destruct d; cbn [count3 sv is3 andb] in *; try discriminate; auto. Qed.

Lemma wv_cons d l: wv (d :: l) = (dv d * 4 ^ Z.of_nat (length l) + wv l)%Z.
Proof. reflexivity. Qed.
Lemma wv_le3 w: (wv w <= 4 ^ Z.of_nat (length w) - 1)%Z.
Proof.
  induction w as [|d w IH]; cbn [wv length]; [lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. destruct d; cbn [dv]; lia.
Qed.
Lemma max_unique: forall a H, length H = a -> wv H = wv (repeat D2 a) -> H = repeat D2 a.
Proof.
  induction a as [|a IH]; intros [|d H] Hl Hv; cbn [length] in Hl; try discriminate; [reflexivity|].
  injection Hl as Hl. cbn [repeat wv length] in Hv |- *. rewrite repeat_length, Hl in Hv.
  pose proof (wv_lower H) as L. pose proof (wv_le3 H) as U. pose proof (all2_wv a) as A. pose proof (pow4_ge1 a) as P.
  rewrite Hl in L, U.
  assert (d = D2) as -> by (destruct d; cbn [dv] in Hv; try reflexivity; exfalso; lia).
  f_equal. apply IH; [exact Hl | cbn [dv] in Hv; lia].
Qed.
Lemma sv_top3 x y L: sv false (x :: y :: L) = true -> x = D3 -> y = Dm \/ y = D0 \/ y = D1.
Proof. intros H ->. destruct y; cbn in H; try discriminate; auto. Qed.
Lemma wv_m2 n: (3 * wv (Dm :: repeat D2 n) = - 4 ^ Z.of_nat n - 2)%Z.
Proof. cbn [wv length dv]. rewrite repeat_length. pose proof (all2_wv n). lia. Qed.
Lemma low_sv_bound x y L: sv false (x :: y :: L) = true -> (wv (x :: y :: L) <= 14 * 4 ^ Z.of_nat (length L) - 1)%Z.
Proof.
  intros Hs. cbn [wv length]. pose proof (wv_le3 L) as U.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct x; cbn [dv]; [destruct y; cbn [dv]; lia .. |].
  destruct (sv_top3 _ _ _ Hs eq_refl) as [-> | [-> | ->]]; cbn [dv]; lia.
Qed.
Lemma mul_small (q k x : Z): (0 < k -> q * k = x -> - k < x < k -> q = 0)%Z.
Proof. intros Hk E [L U]. destruct (Z.lt_trichotomy q 0) as [N | [N | N]]; [exfalso; nia | exact N | exfalso; nia]. Qed.
Lemma split_at {A} (w : list A) a: a <= length w -> exists H L, w = H ++ L /\ length H = a.
Proof. intros Ha. exists (firstn a w), (skipn a w). split; [symmetry; apply firstn_skipn | rewrite length_firstn; lia]. Qed.
Lemma unique_m2 a J w: sv false w = true -> length w = a + S (S J) ->
  wv w = wv (repeat D2 a ++ Dm :: repeat D2 (S J)) -> w = repeat D2 a ++ Dm :: repeat D2 (S J).
Proof.
  intros Hs Hl Hv. destruct (split_at w a ltac:(lia)) as [H [L [-> LH]]].
  rewrite length_app, LH in Hl.
  destruct L as [|x [|y L]]; cbn [length] in Hl; try lia.
  assert (LL: length L = J) by lia.
  assert (S3: sv false (x :: y :: L) = true).
  { rewrite sv_app in Hs. apply andb_true_iff in Hs as [_ Hs]. destruct (lst false H); [apply sv_mono|]; exact Hs. }
  pose proof (low_sv_bound x y L S3) as B. rewrite LL in B.
  pose proof (wv_lower (x :: y :: L)) as Lo. cbn [length] in Lo. rewrite LL in Lo.
  rewrite (wv_app H), (wv_app (repeat D2 a)) in Hv. cbn [length] in Hv. rewrite LL, repeat_length in Hv.
  pose proof (wv_m2 (S J)) as M. pose proof (pow4_ge1 J) as P.
  rewrite !Nat2Z.inj_succ, !Z.pow_succ_r in Lo by lia. rewrite !Nat2Z.inj_succ, !Z.pow_succ_r in Hv by lia.
  rewrite !Nat2Z.inj_succ, !Z.pow_succ_r in M by lia.
  assert (EH: wv H = wv (repeat D2 a)).
  { assert (E: ((wv H - wv (repeat D2 a)) * (16 * 4 ^ Z.of_nat J) = wv (Dm :: repeat D2 (S J)) - wv (x :: y :: L))%Z).
    { replace (4 * (4 * 4 ^ Z.of_nat J))%Z with (16 * 4 ^ Z.of_nat J)%Z in Hv by ring. revert Hv. rewrite Z.mul_sub_distr_r.
      generalize (wv H * (16 * 4 ^ Z.of_nat J))%Z (wv (repeat D2 a) * (16 * 4 ^ Z.of_nat J))%Z. intros A1 A2 Hv. lia. }
    assert (Q: (wv H - wv (repeat D2 a) = 0)%Z) by (apply (mul_small _ (16 * 4 ^ Z.of_nat J) _ ltac:(lia) E); lia).
    lia. }
  assert (EL: wv (x :: y :: L) = wv (Dm :: repeat D2 (S J))) by (rewrite EH in Hv; lia).
  rewrite (max_unique a H LH EH). f_equal.
  rewrite wv_cons in EL. cbn [length] in EL. rewrite LL, Nat2Z.inj_succ, Z.pow_succ_r in EL by lia.
  pose proof (wv_lower (y :: L)) as Lo2. cbn [length] in Lo2. rewrite LL, Nat2Z.inj_succ, Z.pow_succ_r in Lo2 by lia.
  assert (x = Dm) as -> by (destruct x; try reflexivity; exfalso; cbn [dv] in EL; lia).
  f_equal. apply (max_unique (S J)); [cbn; lia|].
  rewrite (wv_cons Dm (repeat D2 (S J))), repeat_length, Nat2Z.inj_succ, Z.pow_succ_r in EL by lia. cbn [dv] in EL. lia.
Qed.
Lemma count3_rev l: count3 (rev l) = count3 l.
Proof. induction l as [|d l IH]; [reflexivity|]. cbn [rev]. rewrite count3_app, IH. destruct d; cbn; lia. Qed.

Definition ctxD b i := if i <=? b then U (b - i) i else repeat Dm b.
Definition ctD b i : list Sym := if i =? b then EXT else [].
Lemma ctxD_ok b i: RP TLone [] (ctxD b i) (ctD b i) TLone (rev (ctxD b (S i))).
Proof.
  unfold ctxD, ctD. destruct (Nat.leb_spec i b) as [H|H]; destruct (Nat.leb_spec (S i) b) as [H'|H']; try lia.
  - rewrite (proj2 (Nat.eqb_neq i b)) by lia. replace (b - i) with (S (b - S i)) by lia. apply rp_wave.
  - assert (i = b) as -> by lia. rewrite Nat.eqb_refl, Nat.sub_diag.
    rewrite <- (app_nil_l EXT). apply RP_detach. rewrite <- (app_nil_r (rev (repeat Dm b))).
    apply rp_copy, count3_repeatm.
  - rewrite (proj2 (Nat.eqb_neq i b)) by lia. rewrite <- (app_nil_r (rev (repeat Dm b))). apply rp_copy, count3_repeatm.
Qed.
Lemma TR_D1 b s: forall i, b < i -> TR (ctD b) i s = [1]^^(3 * s).
Proof.
  induction s as [|s IH]; intros i Hi; [reflexivity|]. cbn [TR]. rewrite IH by lia.
  unfold ctD. rewrite (proj2 (Nat.eqb_neq i b)) by lia. replace (3 * S s) with (3 * s + 3) by lia.
  rewrite lpow_add. reflexivity.
Qed.
Lemma TR_D b s: forall i, i <= b -> b < i + s -> TR (ctD b) i s = [1]^^(3 * (i + s - S b)) ++ EXT ++ [1]^^(3 * (S b - i)).
Proof.
  induction s as [|s IH]; intros i Hi Hs; [lia|]. cbn [TR].
  destruct (Nat.eq_dec i b) as [->|Hne].
  - rewrite TR_D1 by lia. unfold ctD. rewrite Nat.eqb_refl.
    replace (b + S s - S b) with s by lia. replace (S b - b) with 1%nat by lia. reflexivity.
  - rewrite IH by lia. unfold ctD. rewrite (proj2 (Nat.eqb_neq i b)) by exact Hne.
    replace (S i + s - S b) with (i + S s - S b) by lia. rewrite <- !app_assoc. cbn [app].
    replace (3 * (S b - i)) with (3 * (S b - S i) + 3) by lia. rewrite lpow_add. reflexivity.
Qed.

Lemma par_step tp ws d0 ws' d0' g k: IInc tp ws d0 ws' d0' g -> ((d0 = D0 \/ d0 = D2) -> k = O) ->
  ((d0 = D1 \/ d0 = D3) -> 1 <= k) -> d0 <> Dm ->
  (par d0 = false /\ k = O /\ par d0' = true) \/ (par d0 = true /\ 1 <= k /\ par d0' = false).
Proof.
  intros HI Hf Hs Hd. pose proof (iinc_par _ _ _ _ _ _ HI) as Hp. rewrite Hp.
  destruct d0; cbn [par negb]; [congruence | left | right | left | right]; repeat split; auto.
Qed.

Definition ta d := match d with Dm => 2 | D0 => 2 | D1 => 3 | D2 => 3 | D3 => 4 end.
Definition tb d := match d with Dm => 3 | D0 => 2 | D1 => 3 | D2 => 2 | D3 => 3 end.
Fixpoint toks (ds : list dg) : list nat := match ds with [] => [] | d :: ds => ta d :: tb d :: toks ds end.
Definition tok (l : side) t := l <* [0] <* [1]^^t.
Definition tokside (ts : list nat) (l : side) := fold_left tok ts l.
Lemma Rl_tok d l: l <* Rl d = tok (tok l (ta d)) (tb d).
Proof. destruct d; reflexivity. Qed.
Lemma toks_app X Y: toks (X ++ Y) = toks X ++ toks Y.
Proof. induction X as [|d X IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma lstack_tok ds l: lstack ds l = tokside (toks (rev ds)) l.
Proof.
  induction ds as [|d ds IH]; [reflexivity|]. cbn [lstack rev]. rewrite IH, Rl_tok, toks_app.
  unfold tokside. rewrite fold_left_app. reflexivity.
Qed.
Lemma lone_reading ws W l0: toks W = 2 :: toks ws ++ [3] ->
  lstack (D2 :: rev ws) (base (TDig D2) l0) = lstack (rev W) (base TLone l0) <* [1;1;0].
Proof.
  intros H. rewrite !lstack_tok. cbn [rev]. rewrite !rev_involutive.
  change (base (TDig D2) l0) with (tokside [3;2] (l0 <* [0])).
  change (base TLone l0) with (tokside [3] (l0 <* [0])).
  change (tokside (toks W) (tokside [3] (l0 <* [0])) <* [1;1;0])
    with (tokside [2] (tokside (toks W) (tokside [3] (l0 <* [0])))).
  unfold tokside. rewrite <- !fold_left_app. f_equal.
  rewrite toks_app, H. cbn. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma toks_rep2 n: 2 :: toks (repeat D2 n) = toks (repeat Dm n) ++ [2].
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat toks]. cbn [ta tb]. rewrite IH. reflexivity. Qed.
Lemma toks_rep3 n: 3 :: toks (repeat Dm n) = toks (repeat D2 n) ++ [3].
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat toks ta tb app]. rewrite <- IH. reflexivity. Qed.
Lemma lr_even A j: toks (repeat Dm A ++ [D0; D1] ++ repeat Dm j) = 2 :: toks (repeat D2 A ++ [Dm] ++ repeat D2 j) ++ [3].
Proof.
  rewrite !toks_app. cbn [toks ta tb app].
  rewrite <- !app_assoc, app_comm_cons, toks_rep2, <- !app_assoc. f_equal. cbn [app]. rewrite <- toks_rep3. reflexivity.
Qed.
Lemma lr_odd A j: toks (repeat Dm A ++ [Dm; D2; Dm] ++ repeat Dm j) = 2 :: toks (repeat D2 A ++ [D1; D0] ++ repeat D2 j) ++ [3].
Proof.
  rewrite !toks_app. cbn [toks ta tb app].
  rewrite <- !app_assoc, app_comm_cons, toks_rep2, <- !app_assoc. f_equal. cbn [app]. rewrite <- toks_rep3. reflexivity.
Qed.

Lemma rp_waveR tp rout a c: RP tp rout (U (S a) c) [] tp (rev (U a (S c)) ++ rout).
Proof.
  unfold U at 1. apply rp_pre; [apply count3_repeat2|]. rewrite rev_repeat. cbn [repeat app].
  apply RP_fire; [right; reflexivity|]. cbn [sc].
  pose proof (rp_copy tp (repeat Dm c) (count3_repeatm c) (Dm :: D3 :: repeat D2 a ++ rout)) as Hc.
  rewrite rev_repeat in Hc.
  replace (rev (U a (S c)) ++ rout) with (repeat Dm c ++ Dm :: D3 :: repeat D2 a ++ rout); [exact Hc|].
  rewrite rev_U, repeat_snoc. cbn [repeat app]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rp_copy0 tp Q: count3 Q = O -> RP tp [] Q [] tp (rev Q).
Proof. intros H. rewrite <- (app_nil_r (rev Q)). apply rp_copy. exact H. Qed.

Definition tgt x := x = Dm \/ x = D0 \/ x = D1.
Definition nt x : nat := match x with Dm | D1 => 3 | _ => O end.
Definition ctxF Q0 x b i := if i <=? b then Q0 ++ [x] ++ U (b - i) i else Q0 ++ [sc x] ++ repeat Dm (S b).
Definition ctF x b i : list Sym := if i =? b then [1]^^(nt x) else [].
Lemma sc_ne3 x: tgt x -> sc x <> D3.
Proof. intros [-> | [-> | ->]]; discriminate. Qed.
Lemma tgt_ne3 x: tgt x -> x <> D3.
Proof. intros [-> | [-> | ->]]; discriminate. Qed.
Lemma count3_one d: d <> D3 -> count3 [d] = O.
Proof. destruct d; try reflexivity. congruence. Qed.

Lemma fire_tgt tp Q0 x c: topok tp -> count3 Q0 = O -> tgt x ->
  RP tp [] (Q0 ++ [x] ++ [D3] ++ repeat Dm c) ([1]^^(nt x)) tp (rev (Q0 ++ [sc x] ++ repeat Dm (S c))).
Proof.
  intros Htp HQ Hx. apply rp_pre; [exact HQ|]. rewrite app_nil_r. cbn [app].
  apply RP_can; [apply tgt_ne3; exact Hx|].
  assert (Hcp: forall rout, RP tp rout (repeat Dm (S c)) [] tp (rev (repeat Dm (S c)) ++ rout))
    by (intros rout; apply rp_copy, count3_repeatm).
  assert (sweepQ: forall e, e <> D3 -> RP tp [] (rev (e :: rev Q0)) [] tp (e :: rev Q0)).
  { intros e He. replace (rev (e :: rev Q0)) with (Q0 ++ [e]) by (cbn [rev]; rewrite rev_involutive; reflexivity).
    replace (e :: rev Q0) with (rev (Q0 ++ [e]) ++ []) by (rewrite app_nil_r, rev_app_distr; reflexivity).
    apply rp_copy. rewrite count3_app, HQ, count3_one by exact He. reflexivity. }
  replace (rev (Q0 ++ sc x :: repeat Dm (S c))) with (rev (repeat Dm (S c)) ++ sc x :: rev Q0)
    by (rewrite rev_app_distr; cbn [rev]; rewrite <- !app_assoc; reflexivity).
  destruct Hx as [-> | [-> | ->]]; cbn [nt sc lpow app].
  - exact (RP_trig tp (rev Q0) Dm D0 (repeat Dm c) [] tp (D0 :: rev Q0) [] tp _ Htp (or_introl (conj eq_refl eq_refl))
      (sweepQ D0 ltac:(discriminate)) (Hcp (D0 :: rev Q0))).
  - apply RP_fire; [left; reflexivity|]. cbn [sc].
    pose proof (rp_copy tp (repeat Dm c) (count3_repeatm c) (Dm :: D1 :: rev Q0)) as H.
    rewrite rev_repeat in H. cbn [repeat rev]. rewrite rev_repeat. rewrite <- app_assoc. exact H.
  - exact (RP_trig tp (rev Q0) D1 D2 (repeat Dm c) [] tp (D2 :: rev Q0) [] tp _ Htp (or_intror (conj eq_refl eq_refl))
      (sweepQ D2 ltac:(discriminate)) (Hcp (D2 :: rev Q0))).
Qed.

Lemma ctxF_ok tp Q0 x b i: topok tp -> count3 Q0 = O -> tgt x ->
  RP tp [] (ctxF Q0 x b i) (ctF x b i) tp (rev (ctxF Q0 x b (S i))).
Proof.
  intros Htp HQ Hx. unfold ctxF, ctF.
  assert (HQx: count3 (Q0 ++ [x]) = O) by (rewrite count3_app, HQ, count3_one by (apply tgt_ne3; exact Hx); reflexivity).
  destruct (Nat.leb_spec i b) as [H|H]; destruct (Nat.leb_spec (S i) b) as [H'|H']; try lia.
  - rewrite (proj2 (Nat.eqb_neq i b)) by lia. rewrite app_assoc. apply rp_pre; [exact HQx|]. rewrite app_nil_r.
    replace (b - i) with (S (b - S i)) by lia.
    replace (rev (Q0 ++ [x] ++ U (b - S i) (S i))) with (rev (U (b - S i) (S i)) ++ rev (Q0 ++ [x]))
      by (rewrite app_assoc, (rev_app_distr (Q0 ++ [x])); reflexivity).
    apply rp_waveR.
  - assert (i = b) as -> by lia. rewrite Nat.eqb_refl, Nat.sub_diag. unfold U. cbn [repeat app].
    apply fire_tgt; assumption.
  - rewrite (proj2 (Nat.eqb_neq i b)) by lia. rewrite <- (app_nil_r (rev _)). apply rp_copy.
    rewrite !count3_app, HQ, count3_repeatm, count3_one by (apply sc_ne3; exact Hx). reflexivity.
Qed.
Lemma TR_F1 x b s: forall i, b < i -> TR (ctF x b) i s = [1]^^(3 * s).
Proof.
  induction s as [|s IH]; intros i Hi; [reflexivity|]. cbn [TR]. rewrite IH by lia.
  unfold ctF. rewrite (proj2 (Nat.eqb_neq i b)) by lia. replace (3 * S s) with (3 * s + 3) by lia.
  rewrite lpow_add. reflexivity.
Qed.
Lemma TR_F x b s: forall i, i <= b -> b < i + s -> TR (ctF x b) i s = [1]^^(3 * s + nt x).
Proof.
  induction s as [|s IH]; intros i Hi Hs; [lia|]. cbn [TR].
  destruct (Nat.eq_dec i b) as [->|Hne].
  - rewrite TR_F1 by lia. unfold ctF. rewrite Nat.eqb_refl. change [1;1;1] with ([1]^^3). rewrite <- !lpow_add. f_equal. lia.
  - rewrite IH by lia. unfold ctF. rewrite (proj2 (Nat.eqb_neq i b)) by exact Hne. cbn [app].
    change [1;1;1] with ([1]^^3). rewrite <- lpow_add. f_equal. lia.
Qed.
Lemma TR_F0 x b s: forall i, i + s <= b -> TR (ctF x b) i s = [1]^^(3 * s).
Proof.
  induction s as [|s IH]; intros i Hi; [reflexivity|]. cbn [TR]. rewrite IH by lia.
  unfold ctF. rewrite (proj2 (Nat.eqb_neq i b)) by lia. cbn [app]. change [1;1;1] with ([1]^^3). rewrite <- lpow_add. f_equal. lia.
Qed.
Lemma TR_nil s: forall i, TR (fun _ => []) i s = [1]^^(3 * s).
Proof.
  induction s as [|s IH]; intros i; [reflexivity|]. cbn [TR]. rewrite IH. cbn [app].
  change [1;1;1] with ([1]^^3). rewrite <- lpow_add. f_equal. lia.
Qed.

Definition MLONE : list Sym := [1;0;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;1;0;1;1;1;0;1;1;0;1;1;1;0;1;1;1;1;0;1;1;1;0;1;1;0;1;1;1;0].
Lemma mlone_tok X: X <* MLONE = tokside [3;2;3;4;3;2;3;4;3;2;2;2;2] X <* [1;0].
Proof. reflexivity. Qed.
Lemma lone_merge REP W1 l0: toks (D2 :: REP) = 3 :: toks W1 ++ [2] ->
  lstack (D0 :: rev (W1 ++ [Dm;Dm;D3;Dm;D3;D0])) (base TLone l0) <* [1;0] = lstack (rev REP) (base (TDig D2) l0) <* MLONE.
Proof.
  intros H. rewrite mlone_tok, !lstack_tok. cbn [rev]. rewrite !rev_involutive.
  change (base (TDig D2) l0) with (tokside [3;2] (l0 <* [0])).
  change (base TLone l0) with (tokside [3] (l0 <* [0])).
  unfold tokside. rewrite <- !fold_left_app. do 2 f_equal.
  change ([3;2] ++ toks REP ++ [3;2;3;4;3;2;3;4;3;2;2;2;2]) with (toks (D2 :: REP) ++ [3;2;3;4;3;2;3;4;3;2;2;2;2]).
  rewrite H, !toks_app. cbn. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rec_out REP L T d0 M: (forall Y : side, Y <* M = lstack (d0 :: rev T) (Y <* [1]) <* [1;0]) ->
  decstack REP (L <* TB (TDig D2)) <* M = lstack (d0 :: rev (REP ++ T)) (base (TDig D2) L) <* [1;0].
Proof.
  intros H. rewrite H, dec_l, (TB_base (TDig D2) L (or_intror (or_introl eq_refl))), rev_app_distr.
  change (d0 :: rev T ++ rev REP) with ((d0 :: rev T) ++ rev REP). rewrite lstack_app. reflexivity.
Qed.

Lemma absorb_inv L d: Inv L d -> Inv (L ++ [d]) D0.
Proof.
  unfold Inv; intros H. destruct (ok_app_l _ _ _ H) as [s [E H0]]. rewrite <- app_assoc.
  apply (ok_app_r _ _ _ _ E). unfold ok in *. destruct d, s; cbn in *; congruence.
Qed.
Lemma lv_ge1 w: (1 <= lv w)%Z.
Proof. unfold lv. pose proof (wv_lower w). lia. Qed.
Lemma lv_cons x W: lv (x :: W) = (3 * dv x * 4 ^ Z.of_nat (length W) + lv W + 3 * 4 ^ Z.of_nat (length W))%Z.
Proof. unfold lv. cbn [wv length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. Qed.
Lemma lv_snoc_len W d: lv (W ++ [d]) = (3 * wv (W ++ [d]) + 4 ^ Z.of_nat (S (length W)))%Z.
Proof. unfold lv. rewrite length_app. cbn [length]. rewrite Nat.add_1_r. reflexivity. Qed.
Lemma ok_true_large X: ok true X -> ~ ok false X -> (2 * 4 ^ Z.of_nat (length X) - 1 <= 3 * wv X)%Z.
Proof.
  induction X as [|d X IH]; intros Ht Hf; [exfalso; apply Hf; unfold ok; discriminate|].
  cbn [length wv]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof (pow4_ge1 (length X)).
  unfold ok in *; destruct d; cbn [scan dv] in Ht, Hf |- *; try contradiction.
  - specialize (IH Ht Hf). lia.
  - pose proof (wv_lower X). lia.
Qed.
Lemma force_m L d: Inv L d -> L <> [] -> (lv (L ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (length L))%Z ->
  exists B, L = Dm :: B /\ Inv B d.
Proof.
  intros HI Hn Hv. destruct L as [|x B]; [congruence|]. clear Hn.
  cbn [app length] in Hv. rewrite lv_cons in Hv. rewrite length_app in Hv. cbn [length] in Hv.
  rewrite Nat.add_1_r in Hv. pose proof (lv_ge1 (B ++ [d])) as H1. pose proof (pow4_ge1 (S (length B))) as H4.
  assert (Ex: x = Dm) by (destruct x; cbn [dv] in Hv; [reflexivity | lia | lia | lia | lia]). subst x.
  exists B. split; [reflexivity|]. cbn [dv] in Hv.
  unfold Inv in *. cbn [app] in HI. unfold ok in HI. cbn [scan] in HI.
  destruct (scan false (B ++ [lowc d])) eqn:E; [unfold ok; rewrite E; discriminate|].
  exfalso. assert (Hf: ~ ok false (B ++ [lowc d])) by (unfold ok; rewrite E; tauto).
  pose proof (ok_true_large _ HI Hf) as HL. rewrite length_app in HL. cbn [length] in HL. rewrite Nat.add_1_r in HL.
  rewrite wv_snoc in HL. rewrite lv_snoc_len, wv_snoc in Hv.
  assert (dv (lowc d) <= dv d + 1)%Z by (destruct d; cbn; lia). lia.
Qed.
Lemma pow4_mod3 n: exists q, (4 ^ Z.of_nat n = 3 * q + 1)%Z.
Proof.
  induction n as [|n [q IH]]; [exists 0%Z; reflexivity|].
  exists (4 * q + 1)%Z. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma cls_U a c: cls (U a c) = 7 * a + 9 + 7 * c.
Proof. unfold U. rewrite !cls_app, cls_rep2, cls_dm. cbn [cls cl]. lia. Qed.
Lemma lz_len n: length ([0]^^n) = n.
Proof. rewrite lpow_length. cbn [length]. lia. Qed.
Ltac cn H := repeat first [rewrite cls_app in H | rewrite cls_rep2 in H | rewrite cls_dm in H | rewrite cls_U in H |
  progress cbn [cls cl app sc] in H].
Ltac cng := repeat first [rewrite cls_app | rewrite cls_rep2 | rewrite cls_dm | rewrite cls_U | progress cbn [cls cl app sc]].
Lemma count_to_top W d: (3 * wv (W ++ [d]) + 5 <= 2 * 4 ^ Z.of_nat (S (length W)))%Z ->
  exists k1, (3 * (wv (W ++ [d]) + Z.of_nat k1) = 2 * 4 ^ Z.of_nat (S (length W)) - 5)%Z.
Proof.
  intros H. destruct (pow4_mod3 (S (length W))) as [q Eq].
  exists (Z.to_nat (2 * q - 1 - wv (W ++ [d]))). rewrite Z2Nat.id by lia. lia.
Qed.

Fixpoint zm (r : nat) : list dg := match r with O => [] | S r => [D0; Dm] ++ zm r end.
Lemma zm_snoc r: zm r ++ [D0; Dm] = zm (S r).
Proof. induction r as [|r IH]; [reflexivity|]. cbn [zm]. rewrite <- app_assoc, IH. reflexivity. Qed.
Lemma count3_zm r: count3 (zm r) = O.
Proof. induction r as [|r IH]; [reflexivity|]. cbn [zm app count3]. exact IH. Qed.
Lemma zm_length r: length (zm r) = 2 * r.
Proof. induction r as [|r IH]; [reflexivity|]. cbn [zm app length]. lia. Qed.
Fixpoint SG (j s : nat) : list Sym :=
  match s with O => [] | S s => [1;1;1;1;1;1] ++ [0]^^(2 * (4 ^ j - 1)) ++ SG (pred j) s end.
Lemma SG_S j s (r : side): SG j (S s) *> r = [1;1;1;1;1;1] *> [0]^^(2 * (4 ^ j - 1)) *> SG (pred j) s *> r.
Proof. cbn [SG]. rewrite !Str_app_assoc. reflexivity. Qed.
Lemma pow4_nat j: (Z.of_nat (4 ^ j - 1) = 4 ^ Z.of_nat j - 1)%Z.
Proof.
  assert (H: 1 <= 4 ^ j) by (induction j; cbn; lia).
  rewrite Nat2Z.inj_sub by exact H. rewrite Nat2Z.inj_pow. reflexivity.
Qed.

Lemma lv_2s3 c: lv (repeat D2 c ++ [D3]) = (3 * 4 ^ Z.of_nat (S c) + 1)%Z.
Proof.
  unfold lv. rewrite length_app, repeat_length, wv_app. cbn [length wv dv]. pose proof (all2_wv c) as A.
  rewrite Nat.add_1_r, (Nat2Z.inj_succ c), Z.pow_succ_r by lia. cbn [Z.of_nat]. rewrite Z.pow_1_r. lia.
Qed.
Lemma lv_2s1 c: lv (repeat D2 c ++ [D1]) = (3 * 4 ^ Z.of_nat (S c) - 5)%Z.
Proof.
  unfold lv. rewrite length_app, repeat_length, wv_app. cbn [length wv dv]. pose proof (all2_wv c) as A.
  rewrite Nat.add_1_r, (Nat2Z.inj_succ c), Z.pow_succ_r by lia. cbn [Z.of_nat]. rewrite Z.pow_1_r. lia.
Qed.
Lemma lv_X2s3 X c: lv (X ++ repeat D2 c ++ [D3]) = ((lv X + 2) * 4 ^ Z.of_nat (S c) + 1)%Z.
Proof. rewrite lv_app, lv_2s3, length_app, repeat_length. cbn [length]. rewrite Nat.add_1_r. ring. Qed.
Lemma lv_zero X: lv (X ++ [D0]) = (4 * lv X)%Z.
Proof. rewrite lv_snoc. cbn [dv]. ring. Qed.
Lemma pow4_mono a b: a <= b -> (4 ^ Z.of_nat a <= 4 ^ Z.of_nat b)%Z.
Proof. intros H. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow4_S a: (4 ^ Z.of_nat (S a) = 4 * 4 ^ Z.of_nat a)%Z.
Proof. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. Qed.

Definition gw L r := L ++ repeat D2 (r - 2) ++ [D3].
Lemma gw_step L r: 2 <= r -> lv (gw L (S r)) = (4 * lv (gw L r) - 3)%Z.
Proof.
  intros Hr. unfold gw. replace (S r - 2) with (S (r - 2)) by lia. rewrite !lv_X2s3, (pow4_S (S (r - 2))). ring.
Qed.
Lemma gw_ok L r: scan false L = Some true -> ok false (gw L r).
Proof.
  intros H. unfold gw, ok. rewrite scan_app, H. induction (r - 2) as [|n IH]; cbn; [discriminate|exact IH].
Qed.
Lemma gw_length L r: 2 <= r -> length (gw L r) = length L + r - 1.
Proof. intros Hr. unfold gw. rewrite !length_app, repeat_length. cbn [length]. lia. Qed.

Remark SG_len j s: length (SG j (S s)) = 6 + 2 * (4 ^ j - 1) + length (SG (pred j) s).
Proof. cbn [SG]. rewrite !length_app, lz_len. cbn [length]. rewrite Nat.add_assoc. reflexivity. Qed.
Remark cls_zm r: cls (zm r) = 13 * r.
Proof. induction r as [|r IH]; [reflexivity|]. cbn [zm app cls cl]. lia. Qed.
Ltac cz H := repeat first [rewrite cls_app in H | rewrite cls_rep2 in H | rewrite cls_dm in H | rewrite cls_U in H |
  rewrite cls_zm in H | progress cbn [cls cl app sc] in H].
Ltac czg := repeat first [rewrite cls_app | rewrite cls_rep2 | rewrite cls_dm | rewrite cls_U | rewrite cls_zm |
  progress cbn [cls cl app sc]].

Lemma count3_pos012 A: Forall pos012 A -> count3 A = O.
Proof. induction 1 as [|d A Hd _ IH]; [reflexivity|]. destruct Hd as [-> | [-> | ->]]; exact IH. Qed.
Lemma lv_mod3 w: exists q, lv w = (3 * q + 1)%Z.
Proof. destruct (pow4_mod3 (length w)) as [q E]. exists (wv w + q)%Z. unfold lv. lia. Qed.
Lemma pa_conv B d: Inv B d -> (4 * lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  exists B1, B ++ [d] = Dm :: B1 /\ Inv B1 D0 /\ length B1 = length B /\ lv (B1 ++ [D0]) = (4 * lv (B ++ [d]))%Z.
Proof.
  intros HI Hv. destruct (force_m (B ++ [d]) D0 (absorb_inv B d HI) ltac:(destruct B; discriminate)) as [B1 [E HI1]].
  { rewrite lv_zero, length_app. cbn [length]. rewrite Nat.add_1_r. exact Hv. }
  exists B1. split; [exact E|]. split; [exact HI1|]. split.
  - apply (f_equal (@length dg)) in E. rewrite length_app in E. cbn [length] in E. lia.
  - rewrite <- lv_zero, E. symmetry. apply (lv_dm 1).
Qed.

Lemma SG_split j s1 s2 (r : side): SG j (s1 + s2) *> r = SG j s1 *> SG (j - s1) s2 *> r.
Proof.
  revert j; induction s1 as [|s1 IH]; intros j; [cbn [SG Str_app]; rewrite Nat.sub_0_r; reflexivity|].
  cbn [Nat.add]. rewrite !SG_S, IH. replace (pred j - s1) with (j - S s1) by lia. reflexivity.
Qed.

Lemma SG_app j s1 s2: SG j (s1 + s2) = SG j s1 ++ SG (j - s1) s2.
Proof.
  revert j; induction s1 as [|s1 IH]; intros j; [cbn [SG app Nat.add]; rewrite Nat.sub_0_r; reflexivity|].
  cbn [Nat.add SG]. rewrite IH. replace (pred j - s1) with (j - S s1) by lia. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma SG_split_len j s1 s2: length (SG j (s1 + s2)) = length (SG j s1) + length (SG (j - s1) s2).
Proof. rewrite SG_app, length_app. reflexivity. Qed.
Lemma SG11: length (SG 1 1) = 12.
Proof. reflexivity. Qed.

Definition dgt (a b : nat) : dg :=
  if (a =? 2) && (b =? 2) then D0 else if (a =? 2) && (b =? 3) then Dm else if (a =? 3) && (b =? 2) then D2 else D1.
Fixpoint repair (b : nat) (W : list dg) : list dg :=
  match W with [] => [dgt b 2] | d :: W => dgt b (ta d) :: repair (tb d) W end.
Definition REPof (W1 : list dg) : list dg := match W1 with [] => [] | d :: W => repair (tb d) W end.
Lemma dgt_tok a b: (a = 2 \/ a = 3) -> (b = 2 \/ b = 3) -> ta (dgt a b) = a /\ tb (dgt a b) = b /\ dgt a b <> D3.
Proof. intros [-> | ->] [-> | ->]; cbn; repeat split; discriminate. Qed.
Lemma ta_tb d: d <> D3 -> (ta d = 2 \/ ta d = 3) /\ (tb d = 2 \/ tb d = 3).
Proof. destruct d; cbn; intros H; [auto.. | congruence]. Qed.
Lemma toks_repair W: count3 W = O -> forall b, (b = 2 \/ b = 3) ->
  toks (repair b W) = b :: toks W ++ [2] /\ count3 (repair b W) = O.
Proof.
  induction W as [|d W IH]; intros H3 b Hb.
  - cbn [repair toks app]. destruct (dgt_tok b 2 Hb (or_introl eq_refl)) as [E1 [E2 E3]]. rewrite E1, E2.
    split; [reflexivity|]. rewrite (count3_can _ _ E3). reflexivity.
  - assert (Hd: d <> D3) by (intros ->; discriminate).
    assert (H3': count3 W = O) by (rewrite count3_can in H3 by exact Hd; exact H3).
    destruct (ta_tb d Hd) as [Ha Hb'].
    destruct (dgt_tok b (ta d) Hb Ha) as [E1 [E2 E3]].
    destruct (IH H3' (tb d) Hb') as [IH1 IH2].
    cbn [repair toks]. rewrite E1, E2, IH1. split; [reflexivity|]. rewrite (count3_can _ _ E3). exact IH2.
Qed.
Lemma REP_ok d W: count3 (d :: W) = O -> ta d = 2 ->
  toks (D2 :: REPof (d :: W)) = 3 :: toks (d :: W) ++ [2] /\ REPof (d :: W) <> [] /\ count3 (REPof (d :: W)) = O.
Proof.
  intros H3 Ha. assert (Hd: d <> D3) by (intros ->; discriminate).
  assert (H3': count3 W = O) by (rewrite count3_can in H3 by exact Hd; exact H3).
  destruct (ta_tb d Hd) as [_ Hb]. destruct (toks_repair W H3' (tb d) Hb) as [E C].
  cbn [REPof toks ta tb]. rewrite E. cbn [app]. rewrite <- Ha. split; [reflexivity|].
  split; [destruct W; discriminate | exact C].
Qed.

Lemma S3B_SG (K : nat -> nat -> list nat): (forall x, K 1%nat x = [x + 12]) ->
  (forall N x, 1 <= N -> K (S N) x = K N (2 * 4 ^ S N - 3 * S N - 8) ++ [x + 3 * S N + 9]) ->
  forall N x (T : side), 1 <= N -> S3B (K N x) *> [0]^^6 *> T = [0]^^(x + 3 * N + 9) *> SG N N *> T.
Proof.
  intros K1 KS. induction N as [|N IH]; intros x T HN; [lia|].
  destruct N as [|N].
  - rewrite K1. replace (x + 3 * 1 + 9) with (x + 12) by lia. cbn [S3B SG app]. rewrite !Str_app_assoc. reflexivity.
  - rewrite KS by lia. assert (S3B_app: forall l1 l2, S3B (l1 ++ l2) = S3B l2 ++ S3B l1).
    { induction l1 as [|k l1 IH1]; intros l2; cbn [app S3B]; [rewrite app_nil_r; reflexivity | rewrite IH1, <- app_assoc; reflexivity]. }
    rewrite S3B_app. cbn [S3B app]. rewrite !Str_app_assoc. rewrite (IH _ T ltac:(lia)).
    rewrite (SG_S (S (S N)) (S N)). cbn [pred].
    replace (2 * 4 ^ S (S N) - 3 * S (S N) - 8 + 3 * S N + 9) with (2 * (4 ^ S (S N) - 1))
      by (assert (4 * S N + 8 <= 4 ^ S (S N)) by (clear; induction N; cbn in *; lia); lia).
    reflexivity.
Qed.

Lemma repeat_app1 {X} (x : X) n: repeat x n ++ [x] = repeat x (S n).
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity. Qed.
Lemma lone_E A j: repeat Dm A ++ [D0; D1] ++ repeat Dm (S j) = (repeat Dm A ++ [D0; D1] ++ repeat Dm j) ++ [Dm].
Proof. rewrite <- !app_assoc, (repeat_app1 Dm j). reflexivity. Qed.
Lemma lone_O A j: repeat Dm A ++ [Dm; D2; Dm] ++ repeat Dm j = (repeat Dm (S A) ++ [D2] ++ repeat Dm j) ++ [Dm].
Proof.
  rewrite <- !app_assoc. cbn [app]. rewrite repeat_app1. rewrite <- (repeat_app1 Dm A), <- !app_assoc. reflexivity.
Qed.
Lemma count3_W A Y j: count3 Y = O -> count3 (repeat Dm A ++ Y ++ repeat Dm j) = O.
Proof. intros H. rewrite !count3_app, count3_repeatm, H, count3_repeatm. reflexivity. Qed.

Lemma scan_3free s B: count3 B = O -> exists s', scan s B = Some s'.
Proof.
  revert s; induction B as [|d B IH]; intros s H; [exists s; reflexivity|].
  destruct d; cbn [count3 scan] in *; try discriminate; apply IH; exact H.
Qed.
Definition tsum (l : list nat) : nat := fold_right Nat.add O l.
Lemma tsum_app X Y: tsum (X ++ Y) = tsum X + tsum Y.
Proof. induction X as [|a X IH]; cbn [app tsum fold_right]; [reflexivity|]. unfold tsum in *. rewrite IH. lia. Qed.
Lemma cls_toks W: tsum (toks W) + 2 * length W = cls W.
Proof. induction W as [|d W IH]; [reflexivity|]. cbn [toks tsum fold_right length cls]. unfold tsum in IH. destruct d; cbn; lia. Qed.
Lemma len_toks W: length (toks W) = 2 * length W.
Proof. induction W as [|d W IH]; [reflexivity|]. cbn [toks length]. lia. Qed.
Lemma cls_rep REP W1: toks (D2 :: REP) = 3 :: toks W1 ++ [2] -> cls REP = cls W1 /\ length REP = length W1.
Proof.
  intros H. pose proof (f_equal tsum H) as T. pose proof (f_equal (@length nat) H) as L.
  change (tsum (toks (D2 :: REP))) with (3 + (2 + tsum (toks REP))) in T.
  change (tsum (3 :: toks W1 ++ [2])) with (3 + tsum (toks W1 ++ [2])) in T. rewrite tsum_app in T.
  change (tsum [2]) with 2 in T.
  change (length (toks (D2 :: REP))) with (S (S (length (toks REP)))) in L. cbn [length] in L.
  rewrite length_app, !len_toks in L. cbn [length] in L.
  pose proof (cls_toks REP) as CR. pose proof (cls_toks W1) as CW. split; lia.
Qed.
Lemma cls_lone W ws: toks (W ++ [Dm]) = 2 :: toks ws ++ [3] -> cls W = cls ws.
Proof.
  intros H. pose proof (f_equal tsum H) as T. pose proof (f_equal (@length nat) H) as L.
  rewrite toks_app, tsum_app in T. rewrite toks_app, length_app in L. cbn [toks ta tb tsum fold_right length app] in T, L.
  rewrite tsum_app in T. rewrite length_app, !len_toks in L. cbn [tsum fold_right length] in T, L.
  pose proof (cls_toks W) as C1. pose proof (cls_toks ws) as C2. unfold tsum in *. lia.
Qed.
Lemma pow4_lin n: (6 * Z.of_nat n + 13 <= 4 ^ Z.of_nat (S (S n)))%Z.
Proof. induction n as [|n IH]; [cbn; lia|]. rewrite (pow4_S (S (S n))). lia. Qed.
Lemma ev_prog tm (c c' : Q * tape): c -[tm]->* c' -> fst c <> fst c' -> c -[tm]->+ c'.
Proof. intros H Hs. apply evstep_progress; [exact H|]. intros E. apply Hs. rewrite E. reflexivity. Qed.
Lemma zeros_shift a b (X : side): a + 4 = b + 1 -> [0]^^a *> [0;0;0;0] *> X = [0]^^b *> [0] *> X.
Proof.
  intros H. change ([0;0;0;0] *> X) with ([0]^^4 *> X). change ([0] *> X) with ([0]^^1 *> X).
  rewrite !lpow_add'. rewrite H. reflexivity.
Qed.

Lemma pow4_add a b: (4 ^ Z.of_nat (a + b) = 4 ^ Z.of_nat a * 4 ^ Z.of_nat b)%Z.
Proof. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. reflexivity. Qed.
Lemma pow4_ge n: (Z.of_nat n + 1 <= 4 ^ Z.of_nat n)%Z.
Proof. induction n as [|n IH]; [cbn; lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma p4nat j: Z.of_nat (4 ^ j) = (4 ^ Z.of_nat j)%Z.
Proof. rewrite Nat2Z.inj_pow. reflexivity. Qed.
Lemma p4nat_ge j: j + 1 <= 4 ^ j.
Proof. pose proof (pow4_ge j). rewrite <- p4nat in H. lia. Qed.
Lemma wv_m_in A C: wv (repeat D2 A ++ [Dm] ++ repeat D2 C) = (wv (repeat D2 (A + 1 + C)) - 3 * 4 ^ Z.of_nat C)%Z.
Proof.
  induction A as [|A IH].
  - cbn [repeat app Nat.add]. rewrite (wv_cons Dm), (wv_cons D2), !repeat_length. cbn [dv]. lia.
  - change (repeat D2 (S A) ++ [Dm] ++ repeat D2 C) with (D2 :: (repeat D2 A ++ [Dm] ++ repeat D2 C)).
    change (repeat D2 (S A + 1 + C)) with (D2 :: repeat D2 (A + 1 + C)).
    rewrite (wv_cons D2), (wv_cons D2 (repeat D2 (A + 1 + C))), IH, !length_app, !repeat_length. cbn [length dv].
    rewrite !Nat.add_assoc. lia.
Qed.
Lemma wv_10_in A C: wv (repeat D2 A ++ [D1; D0] ++ repeat D2 C) = (wv (repeat D2 (A + 2 + C)) - 6 * 4 ^ Z.of_nat C)%Z.
Proof.
  induction A as [|A IH].
  - cbn [repeat app Nat.add]. rewrite (wv_cons D1), (wv_cons D0), (wv_cons D2), (wv_cons D2 (repeat D2 C)).
    cbn [length dv]. rewrite !repeat_length. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
  - change (repeat D2 (S A) ++ [D1; D0] ++ repeat D2 C) with (D2 :: (repeat D2 A ++ [D1; D0] ++ repeat D2 C)).
    change (repeat D2 (S A + 2 + C)) with (D2 :: repeat D2 (A + 2 + C)).
    rewrite (wv_cons D2), (wv_cons D2 (repeat D2 (A + 2 + C))), IH, !length_app, !repeat_length. cbn [length dv].
    rewrite !Nat.add_assoc. lia.
Qed.
Lemma lv_y2 X n: lv (X ++ repeat D2 n) = ((lv X + 2) * 4 ^ Z.of_nat n - 2)%Z.
Proof. rewrite lv_app, lv_rep2, repeat_length. ring. Qed.
Lemma wv_from_lv w: (3 * wv w = lv w - 4 ^ Z.of_nat (length w))%Z.
Proof. unfold lv. ring. Qed.
Lemma wv_dm_neg X: (wv (Dm :: X) <= -1)%Z.
Proof. rewrite wv_cons. pose proof (wv_le3 X). cbn [dv]. lia. Qed.
Lemma scan_dm0 s a X: scan s (repeat Dm a ++ D0 :: X) = scan true X.
Proof. revert s; induction a as [|a IH]; intros s; [reflexivity | apply IH]. Qed.
Lemma scan_2s s n X: scan s (repeat D2 n ++ X) = scan s X.
Proof. induction n as [|n IH]; [reflexivity | exact IH]. Qed.

Lemma zeros_inf k: [0]^^k *> 0inf = 0inf.
Proof. apply lpow_all0. solve_const0_eq. Qed.

Definition one (tm : TM) (x : BoundedConfig.T) : BoundedConfig.T + BoundedConfig.T :=
  match BoundedConfig.step tm x with Some y => inl y | None => inr x end.
Definition run (tm : TM) (n : N) (x : BoundedConfig.T) : BoundedConfig.T :=
  match Eqb.N_iter_until (one tm) (inl x) n with inl y | inr y => y end.
Lemma run_spec tm n x l0 r0 :
  BoundedConfig.to_config x l0 r0 -[tm]->* BoundedConfig.to_config (run tm n x) l0 r0.
Proof.
  pose (G y := BoundedConfig.to_config x l0 r0 -[tm]->* BoundedConfig.to_config y l0 r0).
  assert (H : match Eqb.N_iter_until (one tm) (inl x) n with inl y | inr y => G y end).
  { apply Eqb.N_iter_until_spec; [|apply evstep_refl].
    intros y Hy. unfold one. pose proof (BoundedConfig.step_spec tm y) as S.
    destruct (BoundedConfig.step tm y); [|exact Hy].
    eapply evstep_trans; [exact Hy | apply evstep_one, S]. }
  unfold run. destruct (Eqb.N_iter_until (one tm) (inl x) n); exact H.
Qed.
Lemma start_eq (P K : nat) r :
  BoundedConfig.to_config (BoundedConfig.Build_T ([0]^^P) ([0]^^K) A R) 0inf r = 0inf {{A}}> [0]^^K *> r.
Proof. cbn [BoundedConfig.to_config]. rewrite lpow_all0 by solve_const0_eq. reflexivity. Qed.
Fixpoint Rls (ds : list dg) : list Sym := match ds with [] => [] | d :: ds => Rl d ++ Rls ds end.
Definition fin_list (T : nat) (tp : dg) (ws : list dg) (d0 : dg) : list Sym :=
  [1;0] ++ Rls (d0 :: rev ws) ++ Rl tp ++ [0] ++ [1]^^T.
Lemma lstack_Rls ds l : lstack ds l = l <* Rls ds.
Proof. induction ds as [|d ds IH]; cbn [lstack Rls]; [reflexivity|]. rewrite IH, Str_app_assoc. reflexivity. Qed.
Lemma Str_app5 (a b c d e : list Sym) (s : side) : (a ++ b ++ c ++ d ++ e) *> s = a *> b *> c *> d *> e *> s.
Proof. rewrite !Str_app_assoc. reflexivity. Qed.
Lemma fin_eq (l' : list Sym) T tp ws d0 r :
  cside_eqb l' (fin_list T tp ws d0) = true ->
  BoundedConfig.to_config (BoundedConfig.Build_T l' [] C R) 0inf r = RecT (0inf <* [1]^^T) (TDig tp) ws d0 r.
Proof.
  intro H. apply cside_eqb_spec in H. cbn [BoundedConfig.to_config]. rewrite H.
  unfold RecT, fin_list. cbn [base]. rewrite lstack_Rls.
  apply (f_equal (fun s : side => s {{C}}> r)), Str_app5.
Qed.
Definition check (tm : TM) (n : N) (P K T : nat) (tp : dg) (ws : list dg) (d0 : dg) : bool :=
  match run tm n (BoundedConfig.Build_T ([0]^^P) ([0]^^K) A R) with
  | BoundedConfig.Build_T l' [] C R => cside_eqb l' (fin_list T tp ws d0)
  | _ => false
  end.
Lemma base_of_check tm n P K T tp ws d0 r :
  check tm n P K T tp ws d0 = true ->
  0inf {{A}}> [0]^^K *> r -[tm]->* RecT (0inf <* [1]^^T) (TDig tp) ws d0 r.
Proof.
  unfold check. intro H.
  pose proof (run_spec tm n (BoundedConfig.Build_T ([0]^^P) ([0]^^K) A R) 0inf r) as E.
  destruct (run tm n (BoundedConfig.Build_T ([0]^^P) ([0]^^K) A R)) as [l' [|] [] []]; try discriminate.
  rewrite (fin_eq l' T tp ws d0 r H), (start_eq P K r) in E. exact E.
Qed.

Definition mfacts MT ML MZ n SA := 3 * S n + cls MT + cl ML = 52 + MZ /\ count3 (MT ++ [ML]) = O /\ ML <> Dm /\
  length MT = 6 /\ (forall s, ok s (MT ++ [lowc ML])) /\ SA <> C.
Section Gen.
Variables (tm : TM) (SA : Q) (EXT1 : list Sym) (MZ : nat) (MT : list dg) (ML : dg).
Variables (MY0 MREC : list Sym) (MYs : list (list Sym)).
Notation EXR := ([1;1;1;1;1;1;1;1;1;1;1;1] ++ EXT1).
Notation MR := (3 * S (length MYs)).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation Run l0 tp W d T W' d' T' K := (exists Rx, RecT l0 tp W d T -->* RecT (l0 <* [1]^^Rx) tp W' d' T' /\
  Rx + cls (W' ++ [d']) = cls (W ++ [d]) + K).
Hypothesis decode1 : forall d l r, d <> D3 -> l {{C}}> bt d *> [1] *> r -[tm]->* l <* dec d {{C}}> r.
Hypothesis erase1 : forall d l r, l <* Rl d {{SA}}> [0;0;0;0] *> r -[tm]->* l {{SA}}> [0] *> Er d *> r.
Hypothesis low1 : forall l r, l <* [1;0;1;1;1;0;1;1;1;0] {{C}}> [0;0] *> r -[tm]->* l {{SA}}> [0;0;0;0;0;1;1;1;1;1;1;1] *> r.
Hypothesis turn1 : forall l r, l <* [0] {{SA}}> [0;0;0;0] *> Er' D1 *> r -[tm]->* l <* [1;1;0;1;1;1;0;0;1;1;1] {{C}}> [1;1] *> r.
Hypothesis turn2 : forall l r, l <* [0] {{SA}}> [0;0;0;0] *> Er' D2 *> r -[tm]->* l <* [1;0;1;1;1;0;0;1;1;1] {{C}}> [1;1] *> r.
Hypothesis lowexit1 : forall l r, l {{C}}> [1;1;0;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1;0;1;1;0;1;1;1;0;1] {{C}}> r.
Hypothesis fast : forall l r, l <* [1;0;1;1;0] {{C}}> [0;0] *> r -[tm]->* l <* [1;0;1;1;1;0;1] {{C}}> r.
Hypothesis low3 : forall l r, l <* [1;0;1;1;1;0;1;1;1;1;0] {{C}}> [0;0] *> r -[tm]->* l {{SA}}> [0;0;0;0;0;0;1;1;1;1;1;1;1] *> r.
Hypothesis exit3_0 : forall l r, l <* dec D0 {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;0;1] {{C}}> r.
Hypothesis exit3_2 : forall l r, l <* dec D2 {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;1;0;1] {{C}}> r.
Hypothesis trig_m : forall l r, l <* dec Dm {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1] {{SA}}> [0] *> Er D0 *> [1;1;1;1;1;1;1] *> r.
Hypothesis trig_1 : forall l r, l <* dec D1 {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1] {{SA}}> [0] *> Er D2 *> [1;1;1;1;1;1;1] *> r.
Hypothesis exitT : forall l r, l {{C}}> [1;1;1;1;1;1;1;1;1] *> r -[tm]->* l <* [1;0;1;1;0;1;1;0;1] {{C}}> r.
Hypothesis fire2 : forall l r, l <* [1;0] {{C}}> bt D3 *> [1] *> r -[tm]->* l <* [1;1;0;1] <* dec Dm {{C}}> r.
Hypothesis fire3_m : forall l r, l <* [1;1;0;1;1;0] {{C}}> bt D3 *> r -[tm]->* l {{SA}}> [0] *> Er D0 *> [1;1;1;0] *> r.
Hypothesis fire3_1 : forall l r, l <* [1;1;0;1;1;1;0] {{C}}> bt D3 *> r -[tm]->* l {{SA}}> [0] *> Er D2 *> [1;1;1;0] *> r.
Hypothesis turnL : forall l r, l <* [0] <* [1;1;1;0] {{SA}}> [0;0;0;0] *> r -[tm]->* l <* [1;1;1] <* [1;1;0;0] {{C}}> [1;1] *> r.
Hypothesis detach : forall W r, W <* [1;1;0;0] {{C}}> bt D3 *> [1] *> r -[tm]->* W <* EXT <* [1;1;0;0] {{C}}> r.
Hypothesis top3 : forall l r, l <* [1] <* [0] {{SA}}> [0;0;0;0] *> Er' D3 *> r -[tm]->* l <{{SA}} OVT *> r.
Hypothesis era1 : forall l r, l <* [1] <{{SA}} r -[tm]->* l <{{SA}} [0] *> r.
Hypothesis exhaust : forall l r,
    l <* [1;1;0] <* [0] <* [1;1] <* [0] <* [1;1;1;0] <* [1;1;1;0;1;1;1;1;0] <* [1;0] {{C}}> [0;0;0;0;0;0;0] *> r -[tm]->*
    l <* [1;1;0] {{SA}}> [0;0;0;0;0;0;0;0;0;0] *> EXR *> r.
Hypothesis mark : forall l r, l <* [1;1;0;1] {{SA}}> [0;0;0;0] *> r -[tm]->* l {{SA}}> [1;0;1;1;1;1;1;1] *> r.
Hypothesis absorb : forall l r, l <* [1;0] {{C}}> [1;1;1;1;1;1] *> r -[tm]->* l <* [1;1;0;1;1;0] <* [1;0] {{C}}> r.
Hypothesis opening : forall l r, l <* [1;0] {{C}}> [0;1;1;1;1;1;1;1;0;1] *> r -[tm]->* l <* [0;0] <* [1;1;0;1;1;1] <* [1;1;0;0] {{C}}> r.
Hypothesis seed : forall r, 0inf <{{SA}} [0] *> r -[tm]->* 0inf {{A}}> [0;0] *> r.
Hypothesis rs_open : forall l r, l <* [1;1;0] <* [0;0] <* [1;1;1] {{SA}}> [0;0;0;0;0;0;0;0] *> r -[tm]->*
    l <* [1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;0] {{C}}> r.
Hypothesis low9 : forall l r, l <* [1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;0] {{C}}> [0;0] *> r -[tm]->*
    l {{SA}}> [0;0;0;0;0;0;0;0;0;0;0;1;1;1;1;1;1;1] *> r.
Hypothesis trig_mg : forall l r, l <* dec Dm {{C}}> [1;1;0;0] *> r -[tm]->* l <* [1] {{SA}}> [0] *> Er D0 *> r.
Hypothesis trig_1g : forall l r, l <* dec D1 {{C}}> [1;1;0;0] *> r -[tm]->* l <* [1] {{SA}}> [0] *> Er D2 *> r.
Hypothesis e2_0 : forall l r, l <* dec D0 {{C}}> [1;1;0;0;0;0] *> r -[tm]->* l <* [1] {{SA}}> [0] *> Er D2 *> r.
Hypothesis e2_2 : forall l r, l <* dec D2 {{C}}> [1;1;0;0;0;0;0] *> r -[tm]->*
    l <* [1] {{SA}}> [0;0;0;0;0;0;1;1;1;1;1;1;0] *> r.
Hypothesis e3_0 : forall l r, l <* dec D0 {{C}}> [1;1;0;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1] *> r -[tm]->*
    l <* [1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;0;1] {{C}}> r.
Hypothesis MF : mfacts MT ML MZ (length MYs) SA.
Hypothesis mg0 : forall l r, l <* MLONE {{C}}> EXT1 *> [0]^^MZ *> r -->* l {{SA}}> [0;0;0;0] *> MY0 *> r.
Hypothesis mrec : forall Y, Y <* MREC = lstack (ML :: rev MT) (Y <* [1]) <* [1;0].
Fixpoint mchain (Y : list Sym) (Ys : list (list Sym)) : Prop :=
  match Ys with
  | [] => forall l r, l {{C}}> [1;1] *> Y *> r -->* l <* MREC {{C}}> r
  | Y' :: Ys => (forall l r, l {{C}}> [1;1] *> Y *> r -->* l <* [1] {{SA}}> [0;0;0;0] *> Y' *> r) /\ mchain Y' Ys
  end.
Hypothesis mgc : mchain MY0 MYs.

Lemma erases ds l r:
  lstack ds l {{SA}}> [0;0;0;0] *> r -->* l {{SA}}> [0] *> Ers ds *> r.
Proof.
  revert l r; induction ds as [|d ds IH]; intros; cbn [lstack Ers].
  - finish.
  - follow erase1. rewrite Er_split. follow IH.
    rewrite Str_app_assoc. finish.
Qed.

Lemma exit3 d1 l r: d1 = D0 \/ d1 = D2 ->
  l <* dec d1 {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -->* l <* EX3 d1 {{C}}> r.
Proof. intros [-> | ->]; [apply exit3_0 | apply exit3_2]. Qed.

Lemma trig d1 e l r: (d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2) ->
  l <* dec d1 {{C}}> [1;1;0;0;1;1;1;1;1;1;1] *> r -->* l <* [1] {{SA}}> [0] *> Er e *> [1;1;1;1;1;1;1] *> r.
Proof. intros [[-> ->] | [-> ->]]; [apply trig_m | apply trig_1]. Qed.

Lemma fire2d ds dh l r: dh = D0 \/ dh = D2 ->
  decstack (ds ++ [dh]) l {{C}}> bt D3 *> [1] *> r -->* decstack (ds ++ [sc dh; Dm]) l {{C}}> r.
Proof.
  intros Hdh.
  replace (ds ++ [sc dh; Dm]) with ((ds ++ [sc dh]) ++ [Dm]) by (rewrite <- app_assoc; reflexivity).
  rewrite !decstack_app.
  destruct Hdh as [-> | ->]; cbn [sc].
  - change (decstack ds l <* dec D0) with (decstack ds l <* [1;1;0;1] <* [1;0]).
    follow fire2. finish.
  - change (decstack ds l <* dec D2) with (decstack ds l <* [1;1;1;0;1] <* [1;0]).
    follow fire2. finish.
Qed.

Lemma fire3 dh e l r: (dh = Dm /\ e = D0) \/ (dh = D1 /\ e = D2) ->
  l <* dec dh {{C}}> bt D3 *> r -->* l <* [1] {{SA}}> [0] *> Er e *> [1;1;1;0] *> r.
Proof.
  intros [[-> ->] | [-> ->]].
  - change (l <* dec Dm) with (l <* [1] <* [1;1;0;1;1;0]). apply fire3_m.
  - change (l <* dec D1) with (l <* [1] <* [1;1;0;1;1;1;0]). apply fire3_1.
Qed.

Lemma turnB tp l r: topok tp -> base tp l {{SA}}> [0;0;0;0] *> r -->* l <* [1;1;1] <* TB tp {{C}}> [1;1] *> r.
Proof.
  intros [-> | [-> | ->]]; cbn [base TB].
  - follow erase1. rewrite Er_split. follow turn1. finish.
  - follow erase1. rewrite Er_split. follow turn2. finish.
  - apply turnL.
Qed.

Lemma back tp ds W e R: topok tp ->
  decstack ds (W <* TB tp) <* [1] {{SA}}> [0] *> Er e *> R -->*
  W <* [1;1;1] <* TB tp {{C}}> [1;1] *> Ercat (rev ds) *> Er' e *> R.
Proof.
  intros Htp.
  rewrite dec_l, (TB_base tp W (topok_tb tp Htp)), Er_split.
  follow erases.
  rewrite Ers_cat. repeat rewrite Str_app_assoc.
  replace ([0] *> [0;0;0] *> Ercat (rev ds) *> Er' e *> R) with ([0;0;0;0] *> Ercat (rev ds) *> Er' e *> R)
    by reflexivity.
  follow (turnB tp W (Ercat (rev ds) *> Er' e *> R) Htp). finish.
Qed.

Lemma rpass tp rout ds tx tp' rout' W r: RP tp rout ds tx tp' rout' ->
  decstack (rev rout) (W <* TB tp) {{C}}> Bt ds *> r -->* decstack (rev rout') (W <* tx <* TB tp') {{C}}> r.
Proof.
  intros H; revert W r.
  induction H as [tp rout | tp rout d ds tx tp' rout' Hd _ IH | tp rout dh ds tx tp' rout' Hdh _ IH
                 | ds tx tp' rout' _ IH | ds tx tp' rout' _ IH
                 | tp rout dh e ds tx1 tp1 rout2 tx2 tp' rout' Htp Hde _ IH1 _ IH2]; intros W r.
  - finish.
  - cbn [Bt]. repeat rewrite Str_app_assoc.
    follow (decode1 d (decstack (rev rout) (W <* TB tp)) (Bt ds *> r) Hd).
    rewrite <- decstack_app. apply IH.
  - cbn [Bt]. repeat rewrite Str_app_assoc. cbn [rev].
    follow (fire2d (rev rout) dh (W <* TB tp) (Bt ds *> r) Hdh).
    replace (rev rout ++ [sc dh; Dm]) with (rev (Dm :: sc dh :: rout))
      by (cbn [rev]; rewrite <- app_assoc; reflexivity).
    apply IH.
  - cbn [Bt rev decstack TB]. repeat rewrite Str_app_assoc.
    change (W <* [1;0;1;1;1;0;0]) with (W <* [1;1;1;0;0] <* [1;0]).
    follow fire2. apply (IH W r).
  - cbn [Bt rev decstack TB]. repeat rewrite Str_app_assoc.
    follow (detach W (Bt ds *> r)).
    follow (IH (W <* EXT) r).
    rewrite !side_app. finish.
  - cbn [Bt]. repeat rewrite Str_app_assoc. cbn [rev]. rewrite decstack_app.
    follow (fire3 dh e (decstack (rev rout) (W <* TB tp)) ([1] *> Bt ds *> r) Hde).
    follow (back tp (rev rout) W e ([1;1;1;0] *> [1] *> Bt ds *> r) Htp).
    rewrite rev_involutive.
    replace (Ercat rout *> Er' e *> [1;1;1;0] *> [1] *> Bt ds *> r)
      with (Ercat (rev (rev (e :: rout))) *> [1;1;1;0] *> [1] *> Bt ds *> r)
      by (rewrite rev_involutive; cbn [Ercat]; rewrite Str_app_assoc; reflexivity).
    rewrite (dec_inputB _ _ (rev_cons_nn e rout)).
    follow (IH1 (W <* [1;1;1]) ([1;1] *> [1;1;1;0] *> [1] *> Bt ds *> r)).
    replace ([1;1] *> [1;1;1;0] *> [1] *> Bt ds *> r) with (Bt (Dm :: ds) *> r)
      by (cbn [Bt]; repeat rewrite Str_app_assoc; reflexivity).
    follow (IH2 (W <* [1;1;1] <* tx1) r).
    rewrite !side_app. finish.
Qed.

Lemma recT_fast l0 tp ws d0 r: d0 = D0 \/ d0 = D2 -> RecT l0 tp ws d0 ([0;0] *> r) -->* RecT l0 tp ws (sc d0) r.
Proof.
  unfold RecT; intros [-> | ->]; cbn [lstack sc].
  - change (lstack (rev ws) (base tp l0) <* Rl D0 <* [1;0])
      with (lstack (rev ws) (base tp l0) <* [1;1;0] <* [1;0;1;1;0]).
    follow fast. finish.
  - change (lstack (rev ws) (base tp l0) <* Rl D2 <* [1;0])
      with (lstack (rev ws) (base tp l0) <* [1;1;1;0] <* [1;0;1;1;0]).
    follow fast. finish.
Qed.

Lemma pass1 l0 tp t ts d tx tp' rout r: topok tp -> d = D1 \/ d = D3 -> RP tp [] (t :: ts) tx tp' rout ->
  RecT l0 tp (t :: ts) d ([0;0] *> r) -->* decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') {{C}}> [1;1] *> Zl d *> r.
Proof.
  intros Htp Hd HRP. unfold RecT.
  assert (E: lstack (d :: rev (t :: ts)) (base tp l0) <* [1;0] {{C}}> [0;0] *> r -->*
    lstack (rev (t :: ts)) (base tp l0) {{SA}}> [0;0;0;0] *> Zl d *> r) by (destruct Hd as [-> | ->];
    [change (lstack (D1 :: rev (t :: ts)) (base tp l0) <* [1;0]) with (lstack (rev (t :: ts)) (base tp l0) <* [1;0;1;1;1;0;1;1;1;0]);
       apply low1
    |change (lstack (D3 :: rev (t :: ts)) (base tp l0) <* [1;0]) with (lstack (rev (t :: ts)) (base tp l0) <* [1;0;1;1;1;0;1;1;1;1;0]);
       apply low3]).
  follow E. follow erases. rewrite Ers_cat. repeat rewrite Str_app_assoc. change ([0] *> [0;0;0] *> ?X) with ([0;0;0;0] *> X).
  follow (fun R => turnB tp l0 R Htp). rewrite dec_input, Bt_Bs.
  follow (rpass tp [] (t :: ts) tx tp' rout (l0 <* [1;1;1]) ([1;1] *> Zl d *> r) HRP). finish.
Qed.
Lemma recT_low1 l0 tp t ts tx tp' rout r: topok tp -> RP tp [] (t :: ts) tx tp' rout -> tbok tp' ->
  RecT l0 tp (t :: ts) D1 ([0;0] *> r) -->* RecT (l0 <* [1;1;1] <* tx) tp' (rev rout) D2 r.
Proof.
  intros Htp HRP Htp'. follow (pass1 l0 tp t ts D1 tx tp' rout r Htp (or_introl eq_refl) HRP).
  change ([1;1] *> Zl D1 *> r) with ([1;1;0;1;1;1;1;1;1;1] *> r). follow lowexit1.
  change (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* [1;0;1;1;0;1;1;1;0;1])
    with (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* [1] <* Rl D2 <* [1;0]).
  unfold RecT. rewrite dec_l, (TB_base tp' _ Htp'), rev_involutive. finish.
Qed.

Lemma recT_low3 l0 tp t ts tx tp' d1 rout r: topok tp -> d1 = D0 \/ d1 = D2 ->
  RP tp [] (t :: ts) tx tp' (d1 :: rout) -> tbok tp' ->
  RecT l0 tp (t :: ts) D3 ([0;0] *> r) -->* RecT (l0 <* [1;1;1] <* tx) tp' (rev rout ++ [sc d1]) D0 r.
Proof.
  intros Htp Hd1 HRP Htp'. follow (pass1 l0 tp t ts D3 tx tp' (d1 :: rout) r Htp (or_intror eq_refl) HRP).
  cbn [rev]. rewrite decstack_app. change ([1;1] *> Zl D3 *> r) with ([1;1;0;0;1;1;1;1;1;1;1] *> r).
  follow (exit3 d1 (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp')) r Hd1).
  unfold RecT. rewrite rev_app_distr. cbn [rev app].
  destruct Hd1 as [-> | ->]; cbn [sc].
  - change (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* EX3 D0)
      with (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* [1] <* Rl D1 <* Rl D0 <* [1;0]).
    rewrite dec_l, (TB_base tp' _ Htp'). finish.
  - change (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* EX3 D2)
      with (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp') <* [1] <* Rl D3 <* Rl D0 <* [1;0]).
    rewrite dec_l, (TB_base tp' _ Htp'). finish.
Qed.

Lemma recT_trans l0 tp t ts tx tp1 d1 e rout tx2 tp' rout2 r: topok tp ->
  (d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2) ->
  RP tp [] (t :: ts) tx tp1 (d1 :: rout) -> topok tp1 ->
  RP tp1 [] (rev (e :: rout)) tx2 tp' rout2 -> tbok tp' ->
  RecT l0 tp (t :: ts) D3 ([0;0] *> r) -->*
  RecT (l0 <* [1;1;1] <* tx <* [1;1;1] <* tx2) tp' (rev rout2) D0 r.
Proof.
  intros Htp Hde HRP Htp1 HRP2 Htp'. follow (pass1 l0 tp t ts D3 tx tp1 (d1 :: rout) r Htp (or_intror eq_refl) HRP).
  cbn [rev]. rewrite decstack_app. change ([1;1] *> Zl D3 *> r) with ([1;1;0;0;1;1;1;1;1;1;1] *> r).
  follow (trig d1 e (decstack (rev rout) (l0 <* [1;1;1] <* tx <* TB tp1)) r Hde).
  follow (back tp1 (rev rout) (l0 <* [1;1;1] <* tx) e ([1;1;1;1;1;1;1] *> r) Htp1).
  rewrite rev_involutive.
  replace (Ercat rout *> Er' e *> [1;1;1;1;1;1;1] *> r)
    with (Ercat (rev (rev (e :: rout))) *> [1;1;1;1;1;1;1] *> r)
    by (rewrite rev_involutive; cbn [Ercat]; rewrite Str_app_assoc; reflexivity).
  rewrite (dec_inputB _ _ (rev_cons_nn e rout)).
  follow (rpass tp1 [] (rev (e :: rout)) tx2 tp' rout2 (l0 <* [1;1;1] <* tx <* [1;1;1])
            ([1;1] *> [1;1;1;1;1;1;1] *> r) HRP2).
  replace ([1;1] *> [1;1;1;1;1;1;1] *> r) with ([1;1;1;1;1;1;1;1;1] *> r) by reflexivity.
  follow exitT.
  change (decstack (rev rout2) (l0 <* [1;1;1] <* tx <* [1;1;1] <* tx2 <* TB tp') <* [1;0;1;1;0;1;1;0;1])
    with (decstack (rev rout2) (l0 <* [1;1;1] <* tx <* [1;1;1] <* tx2 <* TB tp') <* [1] <* Rl D0 <* [1;0]).
  unfold RecT. rewrite dec_l, (TB_base tp' _ Htp'), rev_involutive. finish.
Qed.

Lemma recT_low1_0 l0 tp r: topok tp -> RecT l0 tp [] D1 ([0;0] *> r) -->* RecT (l0 <* [1;1;1]) tp [] D2 r.
Proof.
  intros Htp. unfold RecT. cbn [rev lstack].
  change (base tp l0 <* Rl D1 <* [1;0]) with (base tp l0 <* [1;0;1;1;1;0;1;1;1;0]).
  follow low1.
  replace ([0;0;0;0;0;1;1;1;1;1;1;1] *> r) with ([0;0;0;0] *> [0;1;1;1;1;1;1;1] *> r) by reflexivity.
  follow (turnB tp l0 ([0;1;1;1;1;1;1;1] *> r) Htp).
  replace ([1;1] *> [0;1;1;1;1;1;1;1] *> r) with ([1;1;0;1;1;1;1;1;1;1] *> r) by reflexivity.
  follow lowexit1.
  change (l0 <* [1;1;1] <* TB tp <* [1;0;1;1;0;1;1;1;0;1]) with (l0 <* [1;1;1] <* TB tp <* [1] <* Rl D2 <* [1;0]).
  rewrite (TB_base tp _ (topok_tb tp Htp)). finish.
Qed.

Lemma eras n l r: l <* [1]^^n <{{SA}} r -->* l <{{SA}} [0]^^n *> r.
Proof. shift_rule. apply era1. Qed.

Lemma ovf_top ds l R:
  lstack ds (base (TDig D3) (l <* [1])) {{SA}}> [0;0;0;0] *> R -->* l <{{SA}} OVT *> Ercat ds *> R.
Proof.
  follow erases. cbn [base]. rewrite Ers_cat. repeat rewrite Str_app_assoc.
  replace ([0] *> [0;0;0] *> Ercat ds *> R) with ([0;0;0;0] *> Ercat ds *> R) by reflexivity.
  follow erase1. rewrite Er_split. follow top3. finish.
Qed.

Lemma recT_ovf l n ws d0 r: d0 = D1 \/ d0 = D3 ->
  RecT (l <* [1]^^n <* [1]) (TDig D3) ws d0 ([0;0] *> r) -->* l <{{SA}} [0]^^n *> OVT *> Ercat (rev ws) *> Zl d0 *> r.
Proof.
  unfold RecT; intros [-> | ->]; cbn [lstack].
  - change (lstack (rev ws) (base (TDig D3) (l <* [1]^^n <* [1])) <* Rl D1 <* [1;0])
      with (lstack (rev ws) (base (TDig D3) (l <* [1]^^n <* [1])) <* [1;0;1;1;1;0;1;1;1;0]).
    follow low1.
    replace ([0;0;0;0;0;1;1;1;1;1;1;1] *> r) with ([0;0;0;0] *> Zl D1 *> r) by reflexivity.
    follow ovf_top. follow eras. finish.
  - change (lstack (rev ws) (base (TDig D3) (l <* [1]^^n <* [1])) <* Rl D3 <* [1;0])
      with (lstack (rev ws) (base (TDig D3) (l <* [1]^^n <* [1])) <* [1;0;1;1;1;0;1;1;1;1;0]).
    follow low3.
    replace ([0;0;0;0;0;0;1;1;1;1;1;1;1] *> r) with ([0;0;0;0] *> Zl D3 *> r) by reflexivity.
    follow ovf_top. follow eras. finish.
Qed.

Lemma ones3 a b (l : side): l <* [1]^^b <* [1;1;1] <* [1]^^a = l <* [1]^^(a + (2 + b))%nat <* [1].
Proof.
  change (l <* [1]^^b <* [1]^^3 <* [1]^^a = l <* [1]^^(a + (2 + b))%nat <* [1]^^1).
  rewrite !side_app, <- !lpow_add. f_equal. f_equal. lia.
Qed.

Lemma recT_trans_ovf l n tp t ts tx d1 e rout k r: tp = TDig D1 \/ tp = TDig D2 ->
  (d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2) ->
  RP tp [] (t :: ts) tx (TDig D3) (d1 :: rout) -> tx = [1]^^k ->
  RecT (l <* [1]^^n) tp (t :: ts) D3 ([0;0] *> r) -->*
  l <{{SA}} [0]^^(k + (2 + n))%nat *> OVT *> Ercat rout *> Er' e *> [1;1;1;1;1;1;1] *> r.
Proof.
  intros Htp Hde HRP Htx. assert (Htp': topok tp) by (unfold topok; tauto).
  follow (pass1 (l <* [1]^^n) tp t ts D3 tx (TDig D3) (d1 :: rout) r Htp' (or_intror eq_refl) HRP).
  cbn [rev]. rewrite decstack_app. change ([1;1] *> Zl D3 *> r) with ([1;1;0;0;1;1;1;1;1;1;1] *> r).
  follow (trig d1 e (decstack (rev rout) (l <* [1]^^n <* [1;1;1] <* tx <* TB (TDig D3))) r Hde).
  rewrite dec_l, (TB_base (TDig D3) _ (or_intror (or_intror (or_introl eq_refl)))), Er_split.
  match goal with |- context [base (TDig D3) ?W] =>
    replace W with (l <* [1]^^(k + (2 + n))%nat <* [1]) by (subst tx; symmetry; apply ones3) end.
  follow ovf_top. follow eras. rewrite rev_involutive. finish.
Qed.

Lemma sweep ks l R: S2T ks l <{{SA}} [0;0;0] *> R -->* l <{{SA}} [0;0;0] *> S3B ks *> R.
Proof.
  revert R; induction ks as [|k ks IH]; intros R; cbn [S2T S3B].
  - finish.
  - change (S2T ks l <* [1]^^(S (S k)) <* [0;1;1;0] <{{SA}} [0;0;0] *> R)
      with (S2T ks l <* [1]^^(S k) <* [1;1;0;1] {{SA}}> [0;0;0;0] *> R).
    follow mark.
    change (S2T ks l <* [1]^^(S k) {{SA}}> [1;0;1;1;1;1;1;1] *> R)
      with (S2T ks l <* [1]^^(S (S k)) <{{SA}} [0;1;1;1;1;1;1] *> R).
    follow eras.
    replace ([0]^^(S (S k)) *> [0;1;1;1;1;1;1] *> R) with ([0;0;0] *> ([0]^^k *> [1;1;1;1;1;1] *> R))
      by (cbn [lpow app]; cbn; rewrite lpow_shift1; reflexivity).
    follow IH. rewrite !Str_app_assoc. finish.
Qed.

Lemma s2end k ks l r:
  RecT (S2T (k :: ks) l <* [1;1]) TLone [] D3 ([0;0;0;0;0;0;0] *> r) -->*
  l <{{SA}} [0;0;0] *> S3B (k :: ks) *> [0;0;0;0;0;0] *> EXR *> r.
Proof.
  unfold RecT. cbn [S2T rev lstack base Rl].
  change (S2T ks l <* [1]^^(S (S k)) <* [0;1;1;0] <* [1;1] <* [0] <* [1;1;1;0] <* [1;1;1;0;1;1;1;1;0] <* [1;0])
    with (S2T ks l <* [1]^^(S (S k)) <* [1;1;0] <* [0] <* [1;1] <* [0] <* [1;1;1;0] <* [1;1;1;0;1;1;1;1;0] <* [1;0]).
  follow exhaust.
  change (S2T ks l <* [1]^^(S (S k)) <* [1;1;0] {{SA}}> [0;0;0;0;0;0;0;0;0;0] *> EXR *> r)
    with (S2T (k :: ks) l <{{SA}} [0;0;0] *> ([0;0;0;0;0;0] *> EXR *> r)).
  follow sweep. finish.
Qed.

Lemma recT_absorb l0 tp ws d0 r: RecT l0 tp ws d0 ([1;1;1;1;1;1] *> r) -->* RecT l0 tp (ws ++ [d0]) D0 r.
Proof. unfold RecT. rewrite rev_app_distr. cbn [rev app lstack]. follow absorb. finish. Qed.

Lemma incf_sound n tp ws d0 g tp' ws' d0' l0 r: incf n tp ws d0 = Some (g, tp', ws', d0') ->
  RecT l0 tp ws d0 ([0;0] *> r) -->* RecT (l0 <* g) tp' ws' d0' r.
Proof.
  intros H. destruct d0; cbn [incf] in H; try discriminate.
  - inversion H; subst. apply recT_fast; auto.
  - destruct (topokb tp) eqn:Et; [|discriminate]. destruct ws as [|t ts].
    + inversion H; subst. apply recT_low1_0. apply topokb_ok; exact Et.
    + destruct (rpf n tp [] (t :: ts)) as [[[tx tp1] rout]|] eqn:E; [|discriminate].
      destruct (tbokb tp1) eqn:Eb; [|discriminate]. inversion H; subst.
      rewrite <- side_app. apply recT_low1; [apply topokb_ok; exact Et | apply (rpf_sound n); exact E | apply tbokb_ok; exact Eb].
  - inversion H; subst. apply recT_fast; auto.
  - destruct (topokb tp) eqn:Et; [|discriminate]. destruct ws as [|t ts]; [discriminate|].
    destruct (rpf n tp [] (t :: ts)) as [[[tx tp1] [|d1 rout]]|] eqn:E; try discriminate.
    destruct d1; try discriminate.
    1, 3: destruct (topokb tp1) eqn:Et1; [|discriminate];
      match type of H with context [rpf ?n1 ?t1 [] ?X] => destruct (rpf n1 t1 [] X) as [[[tx2 tp2] rout2]|] eqn:E2; [|discriminate] end;
      destruct (tbokb tp2) eqn:Eb; [|discriminate]; inversion H; subst;
      match goal with |- _ -->* RecT ?L _ _ _ _ =>
        replace L with (l0 <* [1;1;1] <* tx <* [1;1;1] <* tx2) by (rewrite !Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; reflexivity) end;
      match type of E with _ = Some (_, _, ?e :: _) => eapply recT_trans with (d1 := e) end;
        [apply topokb_ok; exact Et | first [left; split; reflexivity | right; split; reflexivity]
        | apply (rpf_sound n); exact E | apply topokb_ok; exact Et1 | apply (rpf_sound n); exact E2 | apply tbokb_ok; exact Eb].
    all: destruct (tbokb tp1) eqn:Eb; [|discriminate]; inversion H; subst; rewrite <- side_app;
      match type of E with _ = Some (_, _, ?e :: _) => eapply recT_low3 with (d1 := e) end;
      [apply topokb_ok; exact Et | first [left; reflexivity | right; reflexivity] | apply (rpf_sound n); exact E | apply tbokb_ok; exact Eb].
Qed.

Lemma incs_sound n k: forall tp ws d0 g tp' ws' d0' l0 r, incs n k tp ws d0 = Some (g, tp', ws', d0') ->
  RecT l0 tp ws d0 ([0]^^(2 * k) *> r) -->* RecT (l0 <* g) tp' ws' d0' r.
Proof.
  induction k as [|k IH]; intros tp ws d0 g tp' ws' d0' l0 r H; cbn [incs] in H.
  - inversion H; subst. finish.
  - destruct (incf n tp ws d0) as [[[[g1 tp1] ws1] d1]|] eqn:E1; [|discriminate].
    destruct (incs n k tp1 ws1 d1) as [[[[g2 tp2] ws2] d2]|] eqn:E2; [|discriminate].
    inversion H; subst.
    replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [lpow app].
    change ([0] *> [0] *> [0]^^(2 * k) *> r) with ([0;0] *> ([0]^^(2 * k) *> r)).
    follow (incf_sound n tp ws d0 g1 tp1 ws1 d1 l0 ([0]^^(2 * k) *> r) E1).
    follow (IH tp1 ws1 d1 g2 tp' ws' d0' (l0 <* g1) r E2).
    rewrite side_app. finish.
Qed.

Lemma iinc_sound tp ws d0 ws' d0' g l0 r: IInc tp ws d0 ws' d0' g -> topok tp ->
  RecT l0 tp ws d0 ([0;0] *> r) -->* RecT (l0 <* g) tp ws' d0' r.
Proof.
  intros HI Htp. assert (Htb: tbok tp) by (apply topok_tb; exact Htp).
  destruct HI as [ws d0 Hd0 | t ts tx rout Hr | t ts tx d1 rest Hd1 Hr | t ts tx d1 e rest tx2 rout2 Hde Hr Hr2].
  - apply recT_fast; exact Hd0.
  - rewrite <- side_app. apply recT_low1; [exact Htp | exact Hr | exact Htb].
  - rewrite <- side_app. apply recT_low3; [exact Htp | exact Hd1 | exact Hr | exact Htb].
  - match goal with |- _ -->* RecT ?L _ _ _ _ =>
      replace L with (l0 <* [1;1;1] <* tx <* [1;1;1] <* tx2) by (rewrite !Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; reflexivity) end.
    eapply recT_trans; [exact Htp | exact Hde | exact Hr | exact Htp | exact Hr2 | exact Htb].
Qed.

Lemma lpow0_2 n (r : side): [0]^^(2 * S n) *> r = [0;0] *> ([0]^^(2 * n) *> r).
Proof. replace (2 * S n)%nat with (S (S (2 * n))) by lia. reflexivity. Qed.
Lemma vlift tp L d0 n L' d0' K: VRun tp L d0 n L' d0' K -> dtop tp -> forall a l0 r, K <= a ->
  RecT l0 tp (U a 0 ++ L) d0 ([0]^^(2 * n) *> r) -->* RecT (l0 <* [1]^^(3 * K)) tp (U (a - K) 0 ++ L') d0' r.
Proof.
  induction 1 as [L d0 | L d0 L1 d1 k n L2 d2 K HI HIv Hl Hv Hc H IH]; intros Hdt a l0 r Ha.
  - rewrite Nat.sub_0_r. cbn [Nat.mul lpow Str_app]. finish.
  - assert (Htp: topok tp) by (destruct Hdt as [-> | ->]; unfold topok; auto).
    destruct (iinc_liftg (ctxW a) (fun _ => []) a _ _ _ _ _ _ HI (ctxW_ok tp a) Hdt HIv) as [k' [Hk' [_ [_ Hlift]]]].
    rewrite lpow1_length in Hk'. assert (k' = k) by lia. subst k'.
    pose proof (Hlift O ltac:(lia)) as H0. unfold ctxW in H0. rewrite Nat.sub_0_r, Nat.add_0_l, TR_nil in H0.
    rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * n) *> r) H0 Htp).
    replace (U (a - k) k ++ L1) with (U (a - k) 0 ++ (repeat Dm k ++ L1))
      by (unfold U; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
    replace (3 * (k + K)) with (3 * K + 3 * k) by lia. rewrite <- ones_sides.
    replace (a - (k + K)) with (a - k - K) by lia.
    apply IH; [exact Hdt | lia].
Qed.

Lemma iinc_step tp ws d0 ws' d0' g l0 r c: IInc tp ws d0 ws' d0' g -> topok tp ->
  RecT (l0 <* g) tp ws' d0' r -->* c -> RecT l0 tp ws d0 ([0;0] *> r) -->* c.
Proof. intros H Ht H2. eapply evstep_trans; [apply (iinc_sound _ _ _ _ _ _ _ _ H Ht) | exact H2]. Qed.

Lemma incKQ tp Q: dtop tp -> count3 Q = O -> forall k ws d0 l0 r, Inv ws d0 -> d0 <> Dm ->
  (3 * (wv (ws ++ [d0]) + Z.of_nat k) < 2 * (4 ^ Z.of_nat (S (length ws)) - 1))%Z ->
  exists ws' d0' N, RecT l0 tp (Q ++ ws) d0 ([0]^^(2 * k) *> r) -->* RecT (l0 <* [1]^^N) tp (Q ++ ws') d0' r /\
    Inv ws' d0' /\ d0' <> Dm /\ length ws' = length ws /\ wv (ws' ++ [d0']) = (wv (ws ++ [d0]) + Z.of_nat k)%Z /\
    N + cls (ws' ++ [d0']) = cls (ws ++ [d0]) + 2 * k /\ (sv false (ws ++ [d0]) = true -> sv false (ws' ++ [d0']) = true).
Proof.
  intros Hdt HQ. assert (Htp: topok tp) by (destruct Hdt as [-> | ->]; unfold topok; auto).
  induction k as [|k IH]; intros ws d0 l0 r HI Hd0 Hb.
  - exists ws, d0, O. split; [cbn [lpow Str_app Nat.mul]; finish|]. repeat split; auto; lia.
  - assert (Hc: d0 = D1 -> exists d, In d ws /\ d <> D2).
    { intros ->. destruct (all2_dec ws) as [Ha|Hx]; [|exact Hx]. exfalso.
      rewrite (all2_of ws Ha) in Hb. rewrite wv_snoc in Hb. pose proof (all2_wv (length ws)) as A.
      rewrite repeat_length in Hb. rewrite !Nat2Z.inj_succ in Hb. rewrite Z.pow_succ_r in Hb by lia. cbn [dv] in Hb. lia. }
    destruct (iinc_exists tp ws d0 Hdt HI Hd0 Hc) as [ws1 [d01 [N1 [HII [HI1 [Hd1 [Lw1 [V1 C1]]]]]]]].
    destruct (iinc_liftg (fun _ => Q) (fun _ => []) N1 tp _ _ _ _ _ HII (fun i _ => rp_copy0 tp Q HQ) Hdt HI) as [k1 [Hk1 [_ [_ HL]]]].
    rewrite lpow1_length in Hk1. pose proof (HL O ltac:(lia)) as HL0. rewrite TR_nil in HL0. rewrite <- Hk1 in HL0.
    destruct (IH ws1 d01 (l0 <* [1]^^N1) r HI1 Hd1) as [ws' [d0' [N2 [S2 [HI2 [Hd2 [Lw2 [V2 [C2 Sv2]]]]]]]]];
      [rewrite V1, Lw1; rewrite Nat2Z.inj_succ in Hb; lia|].
    exists ws', d0', (N2 + N1)%nat. split.
    + rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * k) *> r) HL0 Htp). rewrite <- ones_sides. exact S2.
    + repeat split; auto; [lia | rewrite V2, V1, Nat2Z.inj_succ; lia | lia | intros Hs; exact (Sv2 (iinc_sv _ _ _ _ _ _ HII Hs))].
Qed.
Lemma count_maxQ tp Q: dtop tp -> count3 Q = O -> forall k ws d0 l0, Inv ws d0 -> d0 <> Dm ->
  (3 * (wv (ws ++ [d0]) + Z.of_nat k) = 2 * 4 ^ Z.of_nat (S (length ws)) - 5)%Z ->
  exists N, (forall r, RecT l0 tp (Q ++ ws) d0 ([0]^^(2 * k) *> r) -->*
    RecT (l0 <* [1]^^N) tp (Q ++ repeat D2 (length ws)) D1 r) /\ N + cls (repeat D2 (length ws) ++ [D1]) = cls (ws ++ [d0]) + 2 * k.
Proof.
  intros Hdt HQ k ws d0 l0 HI Hd0 Hv.
  assert (H: forall r, exists N, RecT l0 tp (Q ++ ws) d0 ([0]^^(2 * k) *> r) -->*
    RecT (l0 <* [1]^^N) tp (Q ++ repeat D2 (length ws)) D1 r /\ N + cls (repeat D2 (length ws) ++ [D1]) = cls (ws ++ [d0]) + 2 * k).
  { intros r. destruct (incKQ tp Q Hdt HQ k ws d0 l0 r HI Hd0) as [ws' [d0' [N [Hs [HI' [Hd' [Hl [Hw [Hc _]]]]]]]]]; [lia|].
    assert (E: ws' ++ [d0'] = repeat D2 (length ws) ++ [D1]).
    { apply (inv_unique _ _ false); [rewrite !length_app, repeat_length, Hl; reflexivity | apply Inv_word; exact HI'
        | apply Forall_app; split; [apply pos012_repeat2 | constructor; [unfold pos012; auto | constructor]] |].
      rewrite Hw, (wv_snoc (repeat D2 (length ws)) D1). pose proof (all2_wv (length ws)) as A. cbn [dv].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia. lia. }
    apply app_inj_tail in E. destruct E as [-> ->]. exists N. split; [exact Hs | exact Hc]. }
  destruct (H 0inf) as [N0 [_ C0]]. exists N0. split; [|exact C0].
  intros r. destruct (H r) as [N [Hs Hc]]. replace N0 with N by lia. exact Hs.
Qed.

Lemma inv_m2: Inv [Dm] D2.
Proof. unfold Inv, ok. cbn. discriminate. Qed.
Lemma pow4_pos j: 1 <= 4 ^ j.
Proof. induction j as [|j IH]; cbn; lia. Qed.
Lemma zeros_split a b (r : side): [0]^^(a + b) *> r = [0]^^a *> [0]^^b *> r.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.
Lemma ones_join (l : side) a b: l <* [1]^^a <* [1]^^b = l <* [1]^^(a + b).
Proof. rewrite ones_sides. f_equal. f_equal. lia. Qed.

Lemma climb_startQ tp Q a l0 r: dtop tp -> count3 Q = O ->
  RecT l0 tp (Q ++ repeat D2 (S (S a))) D1 ([0]^^10 *> r) -->* RecT (l0 <* [1]^^9) tp (Q ++ U a 0 ++ [Dm]) D2 r.
Proof.
  intros Hdt HQ. assert (Htp: topok tp) by (destruct Hdt as [-> | ->]; unfold topok; auto).
  assert (Hc: forall n, RP tp [] (Q ++ repeat D2 n) [] tp (rev (Q ++ repeat D2 n))).
  { intros n. rewrite <- (app_nil_r (rev _)). apply rp_copy. rewrite count3_app, HQ, count3_repeat2. reflexivity. }
  assert (Hn: forall n, Q ++ repeat D2 (S n) <> []) by (intros n; cbn [repeat]; apply app_cons_nn).
  assert (I1: IInc tp (Q ++ repeat D2 (S (S a))) D1 (Q ++ repeat D2 (S (S a))) D2 [1;1;1]).
  { pose proof (II_low1' tp (Q ++ repeat D2 (S (S a))) [] (rev (Q ++ repeat D2 (S (S a)))) (Hn _) (Hc _)) as H.
    rewrite rev_involutive in H. exact H. }
  assert (I2: IInc tp (Q ++ repeat D2 (S (S a))) D2 (Q ++ repeat D2 (S (S a))) D3 []) by (apply (II_fast tp _ D2); auto).
  assert (I3: IInc tp (Q ++ repeat D2 (S (S a))) D3 (Q ++ repeat D2 (S a) ++ [D3]) D0 [1;1;1]).
  { assert (R: RP tp [] (Q ++ repeat D2 (S (S a))) [] tp (D2 :: rev (Q ++ repeat D2 (S a)))).
    { replace (Q ++ repeat D2 (S (S a))) with (Q ++ repeat D2 (S a) ++ [D2]) by (rewrite repeat_app1; reflexivity).
      rewrite app_assoc. replace (D2 :: rev (Q ++ repeat D2 (S a))) with (rev ((Q ++ repeat D2 (S a)) ++ [D2]))
        by (rewrite rev_app_distr; reflexivity).
      rewrite <- (app_nil_r (rev _)). apply rp_copy. rewrite !count3_app, HQ, count3_repeat2. reflexivity. }
    pose proof (II_low3' tp _ [] D2 (rev (Q ++ repeat D2 (S a))) (Hn _) (or_intror eq_refl) R) as H.
    rewrite rev_involutive in H. cbn [sc] in H. rewrite <- app_assoc in H. exact H. }
  assert (I4: IInc tp (Q ++ repeat D2 (S a) ++ [D3]) D0 (Q ++ repeat D2 (S a) ++ [D3]) D1 []) by (apply (II_fast tp _ D0); auto).
  assert (I5: IInc tp (Q ++ repeat D2 (S a) ++ [D3]) D1 (Q ++ U a 0 ++ [Dm]) D2 [1;1;1]).
  { assert (R: RP tp [] (Q ++ repeat D2 (S a) ++ [D3]) [] tp (rev (Q ++ U a 0 ++ [Dm]))).
    { apply rp_pre; [exact HQ|]. rewrite app_nil_r.
      replace (rev (Q ++ U a 0 ++ [Dm])) with (rev (U a 0 ++ [Dm]) ++ rev Q) by (rewrite (rev_app_distr Q); reflexivity).
      change (repeat D2 (S a) ++ [D3]) with (U (S a) 0).
      replace (rev (U a 0 ++ [Dm])) with (rev (U a 1)) by (unfold U; rewrite <- !app_assoc; reflexivity).
      apply rp_waveR. }
    pose proof (II_low1' tp _ [] _ (app_cons_nn Q D2 (repeat D2 a ++ [D3])) R) as H.
    rewrite rev_involutive in H. exact H. }
  change ([0]^^10 *> r) with ([0;0] *> [0;0] *> [0;0] *> [0;0] *> [0;0] *> r).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I1 Htp). apply (iinc_step _ _ _ _ _ _ _ _ _ I2 Htp).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I3 Htp). apply (iinc_step _ _ _ _ _ _ _ _ _ I4 Htp).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I5 Htp).
  replace (l0 <* [1;1;1] <* [] <* [1;1;1] <* [] <* [1;1;1]) with (l0 <* [1]^^9) by (rewrite !side_app; reflexivity).
  finish.
Qed.
Lemma fire_even j l n r:
  RecT (l <* [1]^^n) (TDig D2) (U (288 * 4 ^ j - 5) 0 ++ [Dm]) D2 ([0]^^(2 * (432 * 4 ^ j - 5)) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 3 * (288 * 4 ^ j - 6) + 5) *> OVT *>
    Ercat (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j)) *> Zl D1 *> r.
Proof.
  pose proof (pow4_pos j) as HP. assert (HZ: Z.of_nat (4 ^ j) = (4 ^ Z.of_nat j)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hdt: dtop (TDig D2)) by (left; reflexivity).
  destruct (vrun_exists (TDig D2) Hdt (432 * 4 ^ j - 7) [Dm] D2 inv_m2 ltac:(discriminate)) as [L' [d0' [K [HR [HI' [Hd' _]]]]]];
    [exists Dm; split; [left; reflexivity | discriminate]|].
  destruct (vrun_top _ _ (cE j) _ _ _ HR HI' Hd' (cE_pos j)) as [EL [-> [Hlen Hcl]]].
  { rewrite cE_lv, <- HZ. lia. }
  { rewrite cE_len, Nat2Z.inj_add, Z.pow_add_r, <- HZ by lia. change (4 ^ Z.of_nat 4)%Z with 256%Z. lia. }
  rewrite cE_len, cE_cls in Hcl. rewrite cE_len in EL, Hlen.
  assert (EK: K = 288 * 4 ^ j - 6) by lia. subst K.
  replace (2 * (432 * 4 ^ j - 5)) with (2 * (432 * 4 ^ j - 7) + 4) by lia.
  rewrite zeros_split. change ([0]^^4 *> [0;0] *> r) with ([0;0] *> [0;0] *> [0;0] *> r).
  follow (vlift _ _ _ _ _ _ _ HR Hdt (288 * 4 ^ j - 5) (l <* [1]^^n) ([0;0] *> [0;0] *> [0;0] *> r) ltac:(lia)).
  replace (288 * 4 ^ j - 5 - (288 * 4 ^ j - 6)) with 1%nat by lia. rewrite EL. clear EL.
  remember (S (288 * 4 ^ j - 6) - (j + 4)) as e eqn:He.
  set (X := repeat Dm e ++ cE j).
  assert (HX: count3 X = O) by (unfold X; rewrite count3_app, count3_repeatm, count3_cE; reflexivity).
  assert (EX: rev X = D1 :: repeat D2 j ++ [D1;D1;D0] ++ repeat Dm e).
  { unfold X. rewrite rev_app_distr, rev_repeat, rev_cE. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  set (rout := (repeat D2 j ++ [D1;D1;D0] ++ repeat Dm e) ++ [Dm; D3]).
  assert (R1: RP (TDig D2) [] (D2 :: D3 :: X) [] (TDig D2) (D1 :: rout)).
  { apply RP_can; [discriminate|]. apply (RP_fire _ [] D2); [right; reflexivity|].
    unfold rout. change (D1 :: (repeat D2 j ++ [D1;D1;D0] ++ repeat Dm e) ++ [Dm; D3])
      with ((D1 :: repeat D2 j ++ [D1;D1;D0] ++ repeat Dm e) ++ [Dm; D3]).
    rewrite <- EX. apply rp_copy. exact HX. }
  set (Y := Dm :: repeat Dm e ++ [D0;D1;D1] ++ repeat D2 (S j)).
  assert (HY: count3 Y = O) by (unfold Y; cbn [count3]; rewrite !count3_app, count3_repeatm, count3_repeat2; reflexivity).
  assert (EY: rev (D2 :: rout) = D3 :: Y).
  { unfold rout, Y. cbn [rev]. rewrite !rev_app_distr, !rev_repeat. cbn [rev app].
    rewrite <- !app_assoc. cbn [app]. rewrite <- (repeat_app1 D2 j), <- ?app_assoc. reflexivity. }
  assert (R2: RP (TDig D2) [] (rev (D2 :: rout)) [] (TDig D3) (rev Y ++ [Dm])).
  { rewrite EY. apply RP_top. apply rp_copy. exact HY. }
  change (U 1 0 ++ X) with (D2 :: D3 :: X).
  follow (recT_trans (l <* [1]^^n <* [1]^^(3 * (288 * 4 ^ j - 6))) (TDig D2) D2 (D3 :: X) [] (TDig D2) D1 D2 rout
            [] (TDig D3) (rev Y ++ [Dm]) ([0;0] *> [0;0] *> r) (or_intror (or_introl eq_refl))
            (or_intror (conj eq_refl eq_refl)) R1 (or_intror (or_introl eq_refl)) R2 (or_intror (or_intror (or_introl eq_refl)))).
  follow (recT_fast (l <* [1]^^n <* [1]^^(3 * (288 * 4 ^ j - 6)) <* [1;1;1] <* [] <* [1;1;1] <* []) (TDig D3)
            (rev (rev Y ++ [Dm])) D0 ([0;0] *> r) (or_introl eq_refl)).
  replace (l <* [1]^^n <* [1]^^(3 * (288 * 4 ^ j - 6)) <* [1;1;1] <* [] <* [1;1;1] <* [])
    with (l <* [1]^^(n + 3 * (288 * 4 ^ j - 6) + 5) <* [1]).
  2:{ change (l <* [1]^^n <* [1]^^(3 * (288 * 4 ^ j - 6)) <* [1;1;1] <* [] <* [1;1;1] <* [])
        with (l <* [1]^^n <* [1]^^(3 * (288 * 4 ^ j - 6)) <* [1]^^3 <* [1]^^3).
      rewrite !ones_join. change (l <* [1]^^(n + 3 * (288 * 4 ^ j - 6) + 5) <* [1])
        with (l <* [1]^^(n + 3 * (288 * 4 ^ j - 6) + 5) <* [1]^^1). rewrite ones_join. f_equal. f_equal. lia. }
  follow (recT_ovf l (n + 3 * (288 * 4 ^ j - 6) + 5) (rev (rev Y ++ [Dm])) D1 r (or_introl eq_refl)).
  replace (rev (rev (rev Y ++ [Dm]))) with (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j)).
  { finish. }
  rewrite rev_involutive. replace (288 * 4 ^ j - 7 - j) with (e + 2) by lia. rewrite repeat_app.
  unfold Y. cbn [rev]. rewrite !rev_app_distr, !rev_repeat. cbn [rev app repeat].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma fire_odd j l n r:
  RecT (l <* [1]^^n) (TDig D2) (U (576 * 4 ^ j - 5) 0 ++ [Dm]) D2 ([0]^^(2 * (864 * 4 ^ j - 7)) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 3 * (576 * 4 ^ j - 5) + 2) *> OVT *>
    Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j)) *> Er' D2 *> [1;1;1;1;1;1;1] *> r.
Proof.
  pose proof (pow4_pos j) as HP. assert (HZ: Z.of_nat (4 ^ j) = (4 ^ Z.of_nat j)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hdt: dtop (TDig D2)) by (left; reflexivity).
  destruct (vrun_exists (TDig D2) Hdt (864 * 4 ^ j - 7) [Dm] D2 inv_m2 ltac:(discriminate)) as [L' [d0' [K [HR [HI' [Hd' _]]]]]];
    [exists Dm; split; [left; reflexivity | discriminate]|].
  destruct (vrun_top _ _ (cO j) _ _ _ HR HI' Hd' (cO_pos j)) as [EL [-> [Hlen Hcl]]].
  { rewrite cO_lv, <- HZ. lia. }
  { rewrite cO_len, Nat2Z.inj_add, Z.pow_add_r, <- HZ by lia. change (4 ^ Z.of_nat 4)%Z with 256%Z. lia. }
  rewrite cO_len, cO_cls in Hcl. rewrite cO_len in EL, Hlen.
  assert (EK: K = 576 * 4 ^ j - 5) by lia. subst K.
  follow (vlift _ _ _ _ _ _ _ HR Hdt (576 * 4 ^ j - 5) (l <* [1]^^n) ([0;0] *> r) ltac:(lia)).
  replace (576 * 4 ^ j - 5 - (576 * 4 ^ j - 5)) with 0%nat by lia. rewrite EL. clear EL.
  remember (S (576 * 4 ^ j - 5) - (j + 4)) as e eqn:He.
  set (X := repeat Dm e ++ cO j).
  assert (HX: count3 X = O) by (unfold X; rewrite count3_app, count3_repeatm, count3_cO; reflexivity).
  set (rout := repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j)).
  assert (EX: rev X ++ [Dm] = D1 :: rout).
  { unfold X, rout. rewrite rev_app_distr, rev_repeat, rev_cO. cbn [app]. rewrite <- !app_assoc. cbn [app].
    replace (576 * 4 ^ j - 7 - j) with (S e) by lia. rewrite <- repeat_app1. reflexivity. }
  assert (R1: RP (TDig D2) [] (D3 :: X) [] (TDig D3) (D1 :: rout)).
  { apply RP_top. rewrite <- EX. apply rp_copy. exact HX. }
  change (U 0 0 ++ X) with (D3 :: X). rewrite ones_join.
  follow (recT_trans_ovf l (n + 3 * (576 * 4 ^ j - 5)) (TDig D2) D3 X [] D1 D2 rout 0 r (or_intror eq_refl)
            (or_intror (conj eq_refl eq_refl)) R1 eq_refl).
  finish.
Qed.

Lemma fire17 l n r: RecT (l <* [1]^^n) (TDig D2) (repeat D2 15) D1 ([0]^^(2 * 26) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 50) *> OVT *> Ercat ([D0;D0] ++ repeat Dm 13) *> Zl D3 *> r.
Proof.
  follow (incs_sound 1000 26 (TDig D2) (repeat D2 15) D1 ([1]^^51) (TDig D3) (repeat Dm 13 ++ [D0;D0]) D3
            (l <* [1]^^n) ([0;0] *> r) ltac:(vm_compute; reflexivity)).
  rewrite ones_join. replace (n + 51) with (n + 50 + 1) by lia. rewrite <- ones_join.
  follow (recT_ovf l (n + 50) (repeat Dm 13 ++ [D0;D0]) D3 r (or_intror eq_refl)). finish.
Qed.
Lemma fire35 l n r: RecT (l <* [1]^^n) (TDig D2) (repeat D2 33) D1 ([0]^^(2 * 54) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 104) *> OVT *> Ercat ([Dm;D2] ++ repeat Dm 31) *> Zl D3 *> r.
Proof.
  follow (incs_sound 1000 54 (TDig D2) (repeat D2 33) D1 ([1]^^105) (TDig D3) (repeat Dm 31 ++ [D2;Dm]) D3
            (l <* [1]^^n) ([0;0] *> r) ltac:(vm_compute; reflexivity)).
  rewrite ones_join. replace (n + 105) with (n + 104 + 1) by lia. rewrite <- ones_join.
  follow (recT_ovf l (n + 104) (repeat Dm 31 ++ [D2;Dm]) D3 r (or_intror eq_refl)). finish.
Qed.
Lemma fire71 l n r: RecT (l <* [1]^^n) (TDig D2) (repeat D2 69) D1 ([0]^^(2 * 108) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 212) *> OVT *> Ercat ([D1;D1;D0] ++ repeat Dm 66) *> Zl D1 *> r.
Proof.
  follow (incs_sound 1000 108 (TDig D2) (repeat D2 69) D1 ([1]^^213) (TDig D3) (repeat Dm 66 ++ [D0;D1;D1]) D1
            (l <* [1]^^n) ([0;0] *> r) ltac:(vm_compute; reflexivity)).
  rewrite ones_join. replace (n + 213) with (n + 212 + 1) by lia. rewrite <- ones_join.
  follow (recT_ovf l (n + 212) (repeat Dm 66 ++ [D0;D1;D1]) D1 r (or_introl eq_refl)). finish.
Qed.
Lemma fire143 l n r: RecT (l <* [1]^^n) (TDig D2) (repeat D2 141) D1 ([0]^^(2 * 214) *> [0;0] *> r) -->*
  l <{{SA}} [0]^^(n + 428) *> OVT *> Ercat ([D0;D2] ++ repeat Dm 138) *> Er' D0 *> [1;1;1;1;1;1;1] *> r.
Proof.
  follow (incs_sound 1000 214 (TDig D2) (repeat D2 141) D1 ([1]^^426) (TDig D2) (D3 :: repeat Dm 137 ++ [D2;D0;Dm]) D3
            (l <* [1]^^n) ([0;0] *> r) ltac:(vm_compute; reflexivity)).
  rewrite ones_join.
  assert (R: RP (TDig D2) [] (D3 :: repeat Dm 137 ++ [D2;D0;Dm]) [] (TDig D3) (Dm :: [D0;D2] ++ repeat Dm 138))
    by (apply (rpf_sound 1000); vm_compute; reflexivity).
  follow (recT_trans_ovf l (n + 426) (TDig D2) D3 (repeat Dm 137 ++ [D2;D0;Dm]) [] Dm D0 ([D0;D2] ++ repeat Dm 138) 0 r
            (or_intror eq_refl) (or_introl (conj eq_refl eq_refl)) R eq_refl).
  finish.
Qed.

Lemma replay (Cf : side -> Q * tape) N (IH: forall r, 0inf {{A}}> [0]^^N *> r -->* Cf r) Z X:
  N <= S (S Z) -> 0inf <{{SA}} [0]^^(S Z) *> X -->* Cf ([0]^^(S (S Z) - N) *> X).
Proof.
  intros HN. change ([0]^^(S Z) *> X) with ([0] *> ([0]^^Z *> X)). follow (seed ([0]^^Z *> X)).
  replace ([0;0] *> [0]^^Z *> X) with ([0]^^N *> [0]^^(S (S Z) - N) *> X); [apply IH|].
  rewrite <- Str_app_assoc, <- lpow_add. replace (N + (S (S Z) - N)) with (S (S Z)) by lia. reflexivity.
Qed.

Definition S2L l0 tp ws d0 := lstack (d0 :: rev ws) (base tp l0) <* [0;0] <* [1;1;0;1;1;1].
Lemma tblone: tbok TLone.
Proof. unfold tbok; auto. Qed.
Lemma s1_open l0 tp ws d0 D R: D <> [] ->
  RecT l0 tp ws d0 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (rev D) *> R) -->* S2L l0 tp ws d0 <* [1;1;0;0] {{C}}> Bt D *> [1;1] *> R.
Proof.
  intros HD. unfold RecT, S2L.
  change ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (rev D) *> R) with ([0;1;1;1;1;1;1;1;0;1] *> ([1;1] *> Ercat (rev D) *> R)).
  rewrite (dec_inputB D R HD). apply opening.
Qed.
Lemma s1_low1 l0 tp ws d0 D r: D <> [] -> count3 D = O ->
  RecT l0 tp ws d0 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (rev D) *> Zl D1 *> r) -->* RecT (S2L l0 tp ws d0) TLone D D2 r.
Proof.
  intros HD H3. follow (s1_open l0 tp ws d0 D (Zl D1 *> r) HD).
  follow (rpass TLone [] D [] TLone (rev D ++ []) (S2L l0 tp ws d0) ([1;1] *> Zl D1 *> r) (rp_copy TLone D H3 [])).
  rewrite app_nil_r, rev_involutive.
  change ([1;1] *> Zl D1 *> r) with ([1;1;0;1;1;1;1;1;1;1] *> r). follow lowexit1.
  change (decstack D (S2L l0 tp ws d0 <* [] <* TB TLone) <* [1;0;1;1;0;1;1;1;0;1])
    with (decstack D (S2L l0 tp ws d0 <* TB TLone) <* [1] <* Rl D2 <* [1;0]).
  rewrite dec_l, (TB_base TLone _ tblone). finish.
Qed.
Lemma s1_m1 l0 tp ws d0 D r: D <> [] -> count3 D = O ->
  RecT l0 tp ws d0 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (rev D) *> [1;1;1;1;1;1;1] *> r) -->*
  RecT (S2L l0 tp ws d0) TLone D D0 r.
Proof.
  intros HD H3. follow (s1_open l0 tp ws d0 D ([1;1;1;1;1;1;1] *> r) HD).
  follow (rpass TLone [] D [] TLone (rev D ++ []) (S2L l0 tp ws d0) ([1;1] *> [1;1;1;1;1;1;1] *> r) (rp_copy TLone D H3 [])).
  rewrite app_nil_r, rev_involutive.
  change ([1;1] *> [1;1;1;1;1;1;1] *> r) with ([1;1;1;1;1;1;1;1;1] *> r). follow exitT.
  change (decstack D (S2L l0 tp ws d0 <* [] <* TB TLone) <* [1;0;1;1;0;1;1;0;1])
    with (decstack D (S2L l0 tp ws d0 <* TB TLone) <* [1] <* Rl D0 <* [1;0]).
  rewrite dec_l, (TB_base TLone _ tblone). finish.
Qed.
Lemma s1_z3 l0 tp ws d0 d1 rest r: d1 = D0 \/ d1 = D2 -> count3 rest = O ->
  RecT l0 tp ws d0 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (d1 :: rest) *> Zl D3 *> r) -->*
  RecT (S2L l0 tp ws d0) TLone (rev rest ++ [sc d1]) D0 r.
Proof.
  intros Hd1 H3. rewrite <- (rev_involutive (d1 :: rest)).
  assert (H3': count3 (rev (d1 :: rest)) = O) by (rewrite count3_rev; cbn [count3]; destruct Hd1 as [-> | ->]; exact H3).
  follow (s1_open l0 tp ws d0 (rev (d1 :: rest)) (Zl D3 *> r) (rev_cons_nn d1 rest)).
  follow (rpass TLone [] (rev (d1 :: rest)) [] TLone (rev (rev (d1 :: rest)) ++ []) (S2L l0 tp ws d0) ([1;1] *> Zl D3 *> r)
            (rp_copy TLone _ H3' [])).
  rewrite app_nil_r, rev_involutive. cbn [rev]. rewrite decstack_app.
  change ([1;1] *> Zl D3 *> r) with ([1;1;0;0;1;1;1;1;1;1;1] *> r).
  follow (exit3 d1 (decstack (rev rest) (S2L l0 tp ws d0 <* [] <* TB TLone)) r Hd1).
  unfold RecT. rewrite rev_app_distr. cbn [rev app].
  destruct Hd1 as [-> | ->]; cbn [sc].
  - change (decstack (rev rest) (S2L l0 tp ws d0 <* [] <* TB TLone) <* EX3 D0)
      with (decstack (rev rest) (S2L l0 tp ws d0 <* TB TLone) <* [1] <* Rl D1 <* Rl D0 <* [1;0]).
    rewrite dec_l, (TB_base TLone _ tblone). finish.
  - change (decstack (rev rest) (S2L l0 tp ws d0 <* [] <* TB TLone) <* EX3 D2)
      with (decstack (rev rest) (S2L l0 tp ws d0 <* TB TLone) <* [1] <* Rl D3 <* Rl D0 <* [1;0]).
    rewrite dec_l, (TB_base TLone _ tblone). finish.
Qed.
Lemma s1_z3t l0 tp ws d0 d1 e rest r: (d1 = Dm /\ e = D0) \/ (d1 = D1 /\ e = D2) -> count3 rest = O ->
  RecT l0 tp ws d0 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> Ercat (d1 :: rest) *> Zl D3 *> r) -->*
  RecT (S2L l0 tp ws d0 <* [1;1;1]) TLone (rev rest ++ [e]) D0 r.
Proof.
  intros Hde H3. rewrite <- (rev_involutive (d1 :: rest)).
  assert (H3': count3 (rev (d1 :: rest)) = O) by (rewrite count3_rev; cbn [count3]; destruct Hde as [[-> _] | [-> _]]; exact H3).
  assert (H3e: count3 (rev (e :: rest)) = O) by (rewrite count3_rev; cbn [count3]; destruct Hde as [[_ ->] | [_ ->]]; exact H3).
  follow (s1_open l0 tp ws d0 (rev (d1 :: rest)) (Zl D3 *> r) (rev_cons_nn d1 rest)).
  follow (rpass TLone [] (rev (d1 :: rest)) [] TLone (rev (rev (d1 :: rest)) ++ []) (S2L l0 tp ws d0) ([1;1] *> Zl D3 *> r)
            (rp_copy TLone _ H3' [])).
  rewrite app_nil_r, rev_involutive. cbn [rev]. rewrite decstack_app.
  change ([1;1] *> Zl D3 *> r) with ([1;1;0;0;1;1;1;1;1;1;1] *> r).
  follow (trig d1 e (decstack (rev rest) (S2L l0 tp ws d0 <* [] <* TB TLone)) r Hde).
  follow (back TLone (rev rest) (S2L l0 tp ws d0 <* []) e ([1;1;1;1;1;1;1] *> r) (or_intror (or_intror eq_refl))).
  rewrite rev_involutive.
  replace (Ercat rest *> Er' e *> [1;1;1;1;1;1;1] *> r) with (Ercat (rev (rev (e :: rest))) *> [1;1;1;1;1;1;1] *> r)
    by (rewrite rev_involutive; cbn [Ercat]; rewrite Str_app_assoc; reflexivity).
  rewrite (dec_inputB _ _ (rev_cons_nn e rest)).
  follow (rpass TLone [] (rev (e :: rest)) [] TLone (rev (rev (e :: rest)) ++ []) (S2L l0 tp ws d0 <* [] <* [1;1;1])
            ([1;1] *> [1;1;1;1;1;1;1] *> r) (rp_copy TLone _ H3e [])).
  change ([1;1] *> [1;1;1;1;1;1;1] *> r) with ([1;1;1;1;1;1;1;1;1] *> r). follow exitT.
  rewrite app_nil_r, rev_involutive.
  change (decstack (rev (e :: rest)) (S2L l0 tp ws d0 <* [] <* [1;1;1] <* [] <* TB TLone) <* [1;0;1;1;0;1;1;0;1])
    with (decstack (rev (e :: rest)) (S2L l0 tp ws d0 <* [1;1;1] <* TB TLone) <* [1] <* Rl D0 <* [1;0]).
  rewrite dec_l, (TB_base TLone _ tblone), rev_involutive.
  unfold RecT. rewrite rev_app_distr, rev_involutive. cbn [rev app]. finish.
Qed.

Lemma s2_det b L d0 L1 d1 k l0 r: IInc TLone L d0 L1 d1 ([1]^^(3 * k)) -> Inv L d0 -> b < k ->
  RecT l0 TLone (U b 0 ++ L) d0 ([0;0] *> r) -->*
  RecT (l0 <* [1]^^(3 * S b) <* EXT <* [1]^^(3 * (k - S b))) TLone (repeat Dm b ++ L1) d1 r.
Proof.
  intros HI HIv Hb.
  destruct (iinc_liftg (ctxD b) (ctD b) (3 * k) TLone _ _ _ _ _ HI (fun i _ => ctxD_ok b i) (or_intror eq_refl) HIv) as [k' [Hk' [_ [_ Hl]]]].
  rewrite lpow1_length in Hk'. assert (k' = k) by lia. subst k'.
  pose proof (Hl O ltac:(lia)) as H0. unfold ctxD at 1 in H0. cbn [Nat.leb Nat.sub] in H0.
  unfold ctxD in H0. rewrite (proj2 (Nat.leb_gt (0 + k) b)) in H0 by lia.
  rewrite (TR_D b k O) in H0 by lia.
  follow (iinc_sound _ _ _ _ _ _ l0 r H0 (or_intror (or_intror eq_refl))).
  rewrite !side_app. replace (0 + k - S b) with (k - S b) by lia. replace (S b - 0) with (S b) by lia.
  rewrite <- !app_assoc. finish.
Qed.

Lemma s2_climb F: forall b L d0 l0, 2 * b + (if par d0 then 0 else 1) < F -> Inv L d0 -> d0 <> Dm ->
  (exists d, In d L /\ d <> D2) ->
  exists T L' d' R, (forall r, RecT l0 TLone (U b 0 ++ L) d0 ([0]^^(2 * T) *> r) -->*
    RecT (l0 <* [1]^^(3 * S b) <* EXT <* [1]^^R) TLone L' d' r) /\
    Inv L' d' /\ d' <> Dm /\ length L' = b + length L /\ T <= F /\
    lv (L' ++ [d']) = (lv (L ++ [d0]) + 3 * Z.of_nat T)%Z /\
    3 * S b + R + cls (L' ++ [d']) = 7 * b + cls (L ++ [d0]) + 2 * T.
Proof.
  induction F as [|F IH]; intros b L d0 l0 HF HI Hd0 Hx; [lia|].
  assert (Hdt: dtop TLone) by (right; reflexivity). assert (Htp: topok TLone) by (unfold topok; auto).
  destruct (iinc_exists TLone L d0 Hdt HI Hd0 (fun _ => Hx)) as [L1 [d1 [N [HII [HI1 [Hd1 [Hl [Hv Hc]]]]]]]].
  destruct (iinc_liftg (ctxW b) (fun _ => []) b _ _ _ _ _ _ HII (ctxW_ok TLone b) Hdt HI) as [k [Hk [Hfast [Hslow Hlift]]]].
  rewrite lpow1_length in Hk. subst N.
  assert (Elv: lv (L1 ++ [d1]) = (lv (L ++ [d0]) + 3)%Z) by (unfold lv; rewrite Hv, !length_app, Hl; cbn [length]; lia).
  destruct (Nat.le_gt_cases k b) as [Hkb | Hkb].
  - pose proof (Hlift O ltac:(lia)) as HL. unfold ctxW in HL. rewrite Nat.sub_0_r, Nat.add_0_l, TR_nil in HL.
    assert (Hx1: exists d, In d (repeat Dm k ++ L1) /\ d <> D2).
    { destruct k as [|k]; [rewrite (iinc_nil _ _ _ _ _ _ HII eq_refl); exact Hx | exists Dm; split; [left; reflexivity | discriminate]]. }
    pose proof (par_step _ _ _ _ _ _ k HII Hfast Hslow Hd0) as Hp.
    assert (HF1: 2 * (b - k) + (if par d1 then 0 else 1) < F)
      by (destruct Hp as [[E1 [E2 E3]] | [E1 [E2 E3]]]; rewrite E1 in HF; rewrite E3; lia).
    destruct (IH (b - k) (repeat Dm k ++ L1) d1 (l0 <* [1]^^(3 * k)) HF1 (inv_dm k L1 d1 HI1) Hd1 Hx1)
      as [T [L' [d' [R [S1 [HI' [Hd' [HlL [HT [Hlv Hcl]]]]]]]]]].
    exists (S T), L', d', R. split.
    + intros r. rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * T) *> r) HL Htp).
      replace (U (b - k) k ++ L1) with (U (b - k) 0 ++ (repeat Dm k ++ L1))
        by (unfold U; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
      replace (l0 <* [1]^^(3 * S b)) with (l0 <* [1]^^(3 * k) <* [1]^^(3 * S (b - k)))
        by (rewrite ones_sides; f_equal; f_equal; lia).
      apply S1.
    + rewrite <- app_assoc, lv_dm in Hlv. rewrite <- app_assoc, (cls_app (repeat Dm k)), cls_dm in Hcl.
      rewrite length_app, repeat_length, Hl in HlL.
      repeat split; auto; [lia | lia | rewrite Hlv, Elv; lia | lia].
  - exists 1%nat, (repeat Dm b ++ L1), d1, (3 * (k - S b)). split.
    + intros r. change ([0]^^(2 * 1) *> r) with ([0;0] *> r). apply (s2_det b L d0 L1 d1 k l0 r HII HI Hkb).
    + split; [apply inv_dm; exact HI1|]. split; [exact Hd1|].
      split; [rewrite length_app, repeat_length, Hl; reflexivity|]. split; [lia|].
      rewrite <- app_assoc, lv_dm, (cls_app (repeat Dm b)), cls_dm. split; [rewrite Elv; lia | lia].
Qed.

Lemma pow4_bound a: 2 * a + 8 <= 4 ^ S (S a).
Proof. induction a as [|a IH]; [cbn; lia|]. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma s2_phase N l0 r: 2 <= N ->
  RecT l0 TLone (repeat D2 N) D1 ([0]^^(2 * 4 ^ N) *> r) -->*
  RecT (l0 <* [1]^^(3 * N + 6) <* EXT <* [1]^^(2 * 4 ^ N - 3 * N - 8)) TLone (repeat D2 (N - 1)) D1 r.
Proof.
  intros HN. destruct N as [|[|a]]; [lia|lia|]. clear HN.
  assert (Hdt: dtop TLone) by (right; reflexivity).
  destruct (s2_climb (S (2 * a + 2)) a [Dm] D2 (l0 <* [1]^^9) ltac:(cbn [par]; lia) inv_m2 ltac:(discriminate)
    ltac:(exists Dm; split; [left; reflexivity | discriminate])) as [T [L' [d' [R [S1 [HI' [Hd' [Hl [HT [Hlv Hcl]]]]]]]]]].
  cbn [length] in Hl. change (lv ([Dm] ++ [D2])) with 10%Z in Hlv. change (cls ([Dm] ++ [D2])) with 14 in Hcl.
  pose proof (pow4_bound a) as Hb.
  set (k := 4 ^ S (S a) - 5 - T).
  assert (HZ: Z.of_nat (4 ^ S (S a)) = (4 ^ Z.of_nat (S (S a)))%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (Hk: (3 * (wv (L' ++ [d']) + Z.of_nat k) = 2 * 4 ^ Z.of_nat (S (length L')) - 5)%Z).
  { unfold k. rewrite Hl. unfold lv in Hlv. rewrite length_app, Hl in Hlv. cbn [length] in Hlv.
    replace (a + 1 + 1) with (S (S a)) in Hlv by lia. replace (S (a + 1)) with (S (S a)) by lia.
    rewrite Nat2Z.inj_sub, Nat2Z.inj_sub, HZ by lia. lia. }
  destruct (count_maxQ TLone [] Hdt eq_refl k L' d' (l0 <* [1]^^9 <* [1]^^(3 * S a) <* EXT <* [1]^^R) HI' Hd' Hk) as [Nc [S2 Hc2]].
  rewrite Hl in S2, Hc2. replace (a + 1) with (S a) in S2, Hc2 by lia.
  replace (2 * 4 ^ S (S a)) with (10 + 2 * T + 2 * k) by (unfold k; lia).
  rewrite !zeros_split.
  follow (climb_startQ TLone [] a l0 ([0]^^(2 * T) *> [0]^^(2 * k) *> r) Hdt eq_refl).
  follow (S1 ([0]^^(2 * k) *> r)). follow S2.
  replace (S (S a) - 1) with (S a) by lia.
  rewrite cls_app, cls_rep2 in Hc2. cbn [cls cl] in Hc2.
  replace (l0 <* [1]^^9 <* [1]^^(3 * S a) <* EXT <* [1]^^R <* [1]^^Nc)
    with (l0 <* [1]^^(3 * S (S a) + 6) <* EXT <* [1]^^(2 * 4 ^ S (S a) - 3 * S (S a) - 8)).
  { finish. }
  rewrite (ones_sides l0), ones_sides.
  replace (3 * S a + 9) with (3 * S (S a) + 6) by lia.
  replace (Nc + R) with (2 * 4 ^ S (S a) - 3 * S (S a) - 8) by (unfold k in Hc2; lia).
  reflexivity.
Qed.

Lemma s2_last l0 r: RecT l0 TLone [D2] D1 ([0]^^12 *> r) -->* RecT (l0 <* [1]^^9 <* EXT) TLone [] D3 r.
Proof.
  follow (incs_sound 10 6 TLone [D2] D1 (EXT ++ [1;1;1;1;1;1;1;1;1]) TLone [] D3 l0 r ltac:(vm_compute; reflexivity)).
  rewrite side_app. finish.
Qed.

Fixpoint KS (N x : nat) : list nat :=
  match N with O => [] | S O => [x + 12] | S N' => KS N' (2 * 4 ^ N - 3 * N - 8) ++ [x + 3 * N + 9] end.
Fixpoint Z2 (N : nat) : nat := match N with O => O | S O => 12 | S N' => 2 * 4 ^ N + Z2 N' end.
Lemma side1_eq (l : side) a b: a = b -> l <* [1]^^a = l <* [1]^^b.
Proof. intros ->. reflexivity. Qed.
Lemma S2T_app ks ks' l: S2T (ks ++ ks') l = S2T ks (S2T ks' l).
Proof. induction ks as [|k ks IH]; cbn [app S2T]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma s2_run N: 1 <= N -> forall l x r,
  RecT (l <* [1;1] <* [1]^^x) TLone (repeat D2 N) D1 ([0]^^(Z2 N) *> r) -->* RecT (S2T (KS N x) l <* [1;1]) TLone [] D3 r.
Proof.
  induction N as [|N IH]; intros HN l x r; [lia|].
  destruct N as [|N].
  - cbn [KS Z2 repeat]. follow s2_last. cbn [S2T].
    replace (l <* [1;1] <* [1]^^x <* [1]^^9 <* EXT) with (l <* [1]^^(S (S (x + 12))) <* [0;1;1;0] <* [1;1]).
    { finish. }
    unfold EXT. change [1;1;0;1;1;0;1;1;1] with ([1;1] ++ [0;1;1;0] ++ [1;1;1]). rewrite <- !side_app.
    change [1;1;1] with ([1]^^3). change [1;1] with ([1]^^2). rewrite !ones_sides. do 2 f_equal. apply side1_eq. lia.
  - change (Z2 (S (S N))) with (2 * 4 ^ S (S N) + Z2 (S N)). rewrite zeros_split.
    follow (s2_phase (S (S N)) (l <* [1;1] <* [1]^^x) ([0]^^(Z2 (S N)) *> r) ltac:(lia)).
    replace (S (S N) - 1) with (S N) by lia.
    replace (l <* [1;1] <* [1]^^x <* [1]^^(3 * S (S N) + 6) <* EXT)
      with (S2T [x + 3 * S (S N) + 9] l <* [1;1]).
    2:{ cbn [S2T]. unfold EXT. change [1;1;0;1;1;0;1;1;1] with ([1;1] ++ [0;1;1;0] ++ [1;1;1]). rewrite <- !side_app.
        change [1;1;1] with ([1]^^3). change [1;1] with ([1]^^2). rewrite !ones_sides. do 2 f_equal. apply side1_eq. lia. }
    follow (IH ltac:(lia) (S2T [x + 3 * S (S N) + 9] l) (2 * 4 ^ S (S N) - 3 * S (S N) - 8) r).
    change (KS (S (S N)) x) with (KS (S N) (2 * 4 ^ S (S N) - 3 * S (S N) - 8) ++ [x + 3 * S (S N) + 9]).
    rewrite S2T_app. finish.
Qed.

Lemma back' tp ds W R: topok tp ->
  decstack ds (W <* TB tp) <* [1] {{SA}}> [0;0;0;0] *> R -->* W <* [1;1;1] <* TB tp {{C}}> [1;1] *> Ercat (rev ds) *> R.
Proof.
  intros Htp. rewrite dec_l, (TB_base tp W (topok_tb tp Htp)).
  follow erases. rewrite Ers_cat. repeat rewrite Str_app_assoc.
  replace ([0] *> [0;0;0] *> Ercat (rev ds) *> R) with ([0;0;0;0] *> Ercat (rev ds) *> R) by reflexivity.
  follow (turnB tp W (Ercat (rev ds) *> R) Htp). finish.
Qed.
Lemma ctl: topok TLone.
Proof. unfold topok; auto. Qed.
Lemma rcopy ds W R: ds <> [] -> count3 ds = O ->
  W <* TB TLone {{C}}> [1;1] *> Ercat (rev ds) *> R -->* decstack ds (W <* TB TLone) {{C}}> [1;1] *> R.
Proof.
  intros Hn H3. rewrite (dec_inputB ds R Hn).
  pose proof (rpass TLone [] ds [] TLone (rev ds ++ []) W ([1;1] *> R) (rp_copy TLone ds H3 [])) as S.
  rewrite app_nil_r, rev_involutive in S. cbn [rev decstack] in S. exact S.
Qed.
Lemma Ercat_snoc ds d: Ercat (rev (ds ++ [d])) = Ercat (rev ds) ++ Er' d.
Proof. rewrite rev_app_distr. reflexivity. Qed.

Lemma restart W' l0 r: count3 W' = O ->
  lstack (rev (W' ++ [Dm])) (base TLone l0) <* [1;1;0] <* [0;0] <* [1;1;1] {{SA}}> [0]^^10 *> r -->*
  RecT (l0 <* [1]^^9) TLone (W' ++ [D2]) D2 r.
Proof.
  intros H3. change ([0]^^10 *> r) with ([0;0;0;0;0;0;0;0] *> [0;0] *> r).
  follow rs_open. follow low9.
  change ([0;0;0;0;0;0;0;0;0;0;0;1;1;1;1;1;1;1] *> r) with ([0;0;0;0] *> ([0;0;0;0;0;0;0] *> [1;1;1;1;1;1;1] *> r)).
  follow erases. rewrite Ers_cat. repeat rewrite Str_app_assoc.
  change ([0] *> [0;0;0] *> Ercat (rev (W' ++ [Dm])) *> ?R) with ([0;0;0;0] *> Ercat (rev (W' ++ [Dm])) *> R).
  follow (fun R => turnB TLone l0 R ctl).
  assert (H3m: count3 (W' ++ [Dm]) = O) by (rewrite count3_app, H3; reflexivity).
  follow (fun R => rcopy (W' ++ [Dm]) (l0 <* [1;1;1]) R (app_cons_nn W' Dm []) H3m).
  rewrite decstack_app. change ([1;1] *> [0;0;0;0;0;0;0] *> ?R) with ([1;1;0;0] *> [0;0;0;0;0] *> R).
  follow trig_mg. follow (fun R => back TLone W' (l0 <* [1;1;1]) D0 R ctl).
  rewrite <- (Str_app_assoc (Ercat (rev W')) (Er' D0)), <- Ercat_snoc.
  assert (H30: count3 (W' ++ [D0]) = O) by (rewrite count3_app, H3; reflexivity).
  follow (fun R => rcopy (W' ++ [D0]) (l0 <* [1;1;1] <* [1;1;1]) R (app_cons_nn W' D0 []) H30).
  rewrite decstack_app. change ([1;1] *> [0;0;0;0;0] *> ?R) with ([1;1;0;0;0;0] *> [0] *> R).
  follow e2_0. follow (fun R => back TLone W' (l0 <* [1;1;1] <* [1;1;1]) D2 R ctl).
  rewrite <- (Str_app_assoc (Ercat (rev W')) (Er' D2)), <- Ercat_snoc.
  assert (H32: count3 (W' ++ [D2]) = O) by (rewrite count3_app, H3; reflexivity).
  follow (fun R => rcopy (W' ++ [D2]) (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1]) R (app_cons_nn W' D2 []) H32).
  change ([1;1] *> [0] *> [1;1;1;1;1;1;1] *> r) with ([1;1;0;1;1;1;1;1;1;1] *> r). follow lowexit1.
  change (decstack (W' ++ [D2]) (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1] <* TB TLone) <* [1;0;1;1;0;1;1;1;0;1])
    with (decstack (W' ++ [D2]) (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1] <* TB TLone) <* [1] <* Rl D2 <* [1;0]).
  rewrite dec_l, (TB_base TLone _ (topok_tb _ ctl)). unfold RecT. cbn [lstack].
  replace (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1]) with (l0 <* [1]^^9) by (rewrite !side_app; reflexivity).
  finish.
Qed.

Lemma restart17 W'' l0 r: count3 W'' = O ->
  lstack (rev (W'' ++ [D0; D1])) (base TLone l0) <* [1;1;0] <* [0;0] <* [1;1;1] {{SA}}> [0]^^10 *> r -->*
  RecT (l0 <* [1]^^9) TLone (W'' ++ [D1; D0]) D2 r.
Proof.
  intros H3. change ([0]^^10 *> r) with ([0;0;0;0;0;0;0;0] *> [0;0] *> r).
  follow rs_open. follow low9.
  change ([0;0;0;0;0;0;0;0;0;0;0;1;1;1;1;1;1;1] *> r) with ([0;0;0;0] *> ([0;0;0;0;0;0;0] *> [1;1;1;1;1;1;1] *> r)).
  follow erases. rewrite Ers_cat. repeat rewrite Str_app_assoc.
  change ([0] *> [0;0;0] *> Ercat (rev (W'' ++ [D0; D1])) *> ?R) with ([0;0;0;0] *> Ercat (rev (W'' ++ [D0; D1])) *> R).
  follow (fun R => turnB TLone l0 R ctl).
  assert (Hn: W'' ++ [D0; D1] <> []) by (destruct W''; discriminate).
  assert (H3a: count3 (W'' ++ [D0; D1]) = O) by (rewrite count3_app, H3; reflexivity).
  follow (fun R => rcopy (W'' ++ [D0; D1]) (l0 <* [1;1;1]) R Hn H3a).
  replace (W'' ++ [D0; D1]) with ((W'' ++ [D0]) ++ [D1]) by (rewrite <- app_assoc; reflexivity).
  rewrite decstack_app. change ([1;1] *> [0;0;0;0;0;0;0] *> ?R) with ([1;1;0;0] *> [0;0;0;0;0] *> R).
  follow trig_1g. follow (fun R => back TLone (W'' ++ [D0]) (l0 <* [1;1;1]) D2 R ctl).
  rewrite <- (Str_app_assoc (Ercat (rev (W'' ++ [D0]))) (Er' D2)), <- Ercat_snoc.
  assert (H3b: count3 ((W'' ++ [D0]) ++ [D2]) = O) by (rewrite !count3_app, H3; reflexivity).
  follow (fun R => rcopy ((W'' ++ [D0]) ++ [D2]) (l0 <* [1;1;1] <* [1;1;1]) R (app_cons_nn (W'' ++ [D0]) D2 []) H3b).
  rewrite decstack_app. change ([1;1] *> [0;0;0;0;0] *> ?R) with ([1;1;0;0;0;0;0] *> R).
  follow e2_2. change ([0;0;0;0;0;0;1;1;1;1;1;1;0] *> ?R) with ([0;0;0;0] *> [0;0;1;1;1;1;1;1;0] *> R).
  follow (fun R => back' TLone (W'' ++ [D0]) (l0 <* [1;1;1] <* [1;1;1]) R ctl).
  assert (H3c: count3 (W'' ++ [D0]) = O) by (rewrite count3_app, H3; reflexivity).
  follow (fun R => rcopy (W'' ++ [D0]) (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1]) R (app_cons_nn W'' D0 []) H3c).
  rewrite decstack_app.
  change ([1;1] *> [0;0;1;1;1;1;1;1;0] *> [1;1;1;1;1;1;1] *> r) with ([1;1;0;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1] *> r).
  follow e3_0.
  change (decstack W'' (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1] <* TB TLone) <* [1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;1;0;1])
    with (decstack W'' (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1] <* TB TLone) <* [1] <* Rl D1 <* Rl D0 <* Rl D2 <* [1;0]).
  rewrite dec_l, (TB_base TLone _ (topok_tb _ ctl)). unfold RecT.
  rewrite rev_app_distr. cbn [rev app lstack].
  replace (l0 <* [1;1;1] <* [1;1;1] <* [1;1;1]) with (l0 <* [1]^^9) by (rewrite !side_app; reflexivity).
  finish.
Qed.

Lemma dtl: dtop TLone.
Proof. right; reflexivity. Qed.

Lemma count_lowQ Q: count3 Q = O -> forall k ws d0 c y l0 r, Inv ws d0 -> d0 <> Dm -> y <> Dm -> Forall pos012 c ->
  length c <= length ws -> lv (c ++ [y]) = (lv (ws ++ [d0]) + 3 * Z.of_nat k)%Z ->
  (3 * (wv (ws ++ [d0]) + Z.of_nat k) < 2 * (4 ^ Z.of_nat (S (length ws)) - 1))%Z ->
  exists N, RecT l0 TLone (Q ++ ws) d0 ([0]^^(2 * k) *> r) -->*
    RecT (l0 <* [1]^^N) TLone (Q ++ repeat Dm (length ws - length c) ++ c) y r /\
    N + cls ((repeat Dm (length ws - length c) ++ c) ++ [y]) = cls (ws ++ [d0]) + 2 * k.
Proof.
  intros HQ k ws d0 c y l0 r HI Hd0 Hy Hc Hlc Hlv Hb.
  destruct (incKQ TLone Q dtl HQ k ws d0 l0 r HI Hd0 Hb) as [ws' [d0' [N [Hs [HI' [Hd' [Hl [Hw [Hcl _]]]]]]]]].
  destruct (low_unique ws' d0' c y HI' Hd' Hy Hc ltac:(lia)) as [E1 E2].
  { unfold lv in Hlv |- *. rewrite !length_app in *. rewrite Hw, Hl. cbn [length] in *. lia. }
  subst d0'. rewrite Hl in E1. rewrite E1 in Hs, Hcl. exists N. split; [exact Hs | exact Hcl].
Qed.

Lemma s3_climb Q0 x F: count3 Q0 = O -> tgt x -> forall b L d0 l0, 2 * b + (if par d0 then 0 else 1) < F ->
  Inv L d0 -> d0 <> Dm -> (exists d, In d L /\ d <> D2) ->
  exists T L' d' R, (forall r, RecT l0 TLone (Q0 ++ [x] ++ U b 0 ++ L) d0 ([0]^^(2 * T) *> r) -->*
    RecT (l0 <* [1]^^R) TLone (Q0 ++ [sc x] ++ L') d' r) /\
    Inv L' d' /\ d' <> Dm /\ length L' = S b + length L /\ T <= F /\
    lv (L' ++ [d']) = (lv (L ++ [d0]) + 3 * Z.of_nat T)%Z /\
    R + cls (L' ++ [d']) + cl (sc x) = cl x + 7 * b + 9 + cls (L ++ [d0]) + 2 * T.
Proof.
  intros HQ Hx. induction F as [|F IH]; intros b L d0 l0 HF HI Hd0 Hxl; [lia|].
  destruct (iinc_exists TLone L d0 dtl HI Hd0 (fun _ => Hxl)) as [L1 [d1 [N [HII [HI1 [Hd1 [Hl [Hv Hc]]]]]]]].
  destruct (iinc_liftg (ctxF Q0 x b) (ctF x b) N TLone _ _ _ _ _ HII (fun i _ => ctxF_ok TLone Q0 x b i ctl HQ Hx) dtl HI)
    as [k [Hk [Hfast [Hslow HL]]]].
  rewrite lpow1_length in Hk. subst N.
  pose proof (HL O ltac:(lia)) as HL0. unfold ctxF in HL0. rewrite (proj2 (Nat.leb_le 0 b)) in HL0 by lia.
  rewrite Nat.sub_0_r, Nat.add_0_l in HL0.
  assert (Elv: lv (L1 ++ [d1]) = (lv (L ++ [d0]) + 3)%Z) by (unfold lv; rewrite Hv, !length_app, Hl; cbn [length]; lia).
  destruct (Nat.le_gt_cases k b) as [Hkb | Hkb].
  - rewrite (TR_F0 x b k O) in HL0 by lia. rewrite (proj2 (Nat.leb_le k b)) in HL0 by lia.
    rewrite <- !app_assoc in HL0.
    assert (Hx1: exists d, In d (repeat Dm k ++ L1) /\ d <> D2).
    { destruct k as [|k]; [rewrite (iinc_nil _ _ _ _ _ _ HII eq_refl); exact Hxl | exists Dm; split; [left; reflexivity | discriminate]]. }
    pose proof (par_step _ _ _ _ _ _ k HII Hfast Hslow Hd0) as Hp.
    assert (HF1: 2 * (b - k) + (if par d1 then 0 else 1) < F)
      by (destruct Hp as [[E1 [E2 E3]] | [E1 [E2 E3]]]; rewrite E1 in HF; rewrite E3; lia).
    destruct (IH (b - k) (repeat Dm k ++ L1) d1 (l0 <* [1]^^(3 * k)) HF1 (inv_dm k L1 d1 HI1) Hd1 Hx1)
      as [T [L' [d' [R [S1 [HI' [Hd' [HlL [HT [Hlv Hcl]]]]]]]]]].
    exists (S T), L', d', (R + 3 * k). split.
    + intros r. rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * T) *> r) HL0 ctl).
      replace (U (b - k) k ++ L1) with (U (b - k) 0 ++ (repeat Dm k ++ L1))
        by (unfold U; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
      follow (S1 r). rewrite ones_sides. finish.
    + rewrite <- app_assoc, lv_dm in Hlv. rewrite <- app_assoc, (cls_app (repeat Dm k)), cls_dm in Hcl.
      rewrite length_app, repeat_length, Hl in HlL.
      repeat split; auto; [lia | lia | rewrite Hlv, Elv; lia | lia].
  - rewrite (TR_F x b k O) in HL0 by lia. rewrite (proj2 (Nat.leb_gt k b)) in HL0 by lia.
    rewrite <- !app_assoc in HL0.
    exists 1%nat, (repeat Dm (S b) ++ L1), d1, (3 * k + nt x). split.
    + intros r. change ([0]^^(2 * 1) *> r) with ([0;0] *> r).
      follow (iinc_sound _ _ _ _ _ _ l0 r HL0 ctl). finish.
    + split; [apply inv_dm; exact HI1|]. split; [exact Hd1|].
      split; [rewrite length_app, repeat_length, Hl; reflexivity|]. split; [lia|].
      rewrite <- app_assoc, lv_dm, (cls_app (repeat Dm (S b))), cls_dm. split; [rewrite Elv; lia|].
      destruct Hx as [-> | [-> | ->]]; cbn [sc cl nt]; lia.
Qed.

Lemma cycle Q0 x a l0: count3 Q0 = O -> tgt x ->
  exists T L' d' R, (forall r, RecT l0 TLone (Q0 ++ [x] ++ repeat D2 (S (S a))) D1 ([0]^^(10 + 2 * T) *> r) -->*
    RecT (l0 <* [1]^^R) TLone (Q0 ++ [sc x] ++ L') d' r) /\
    Inv L' d' /\ d' <> Dm /\ length L' = S (S a) /\ T <= 2 * a + 3 /\
    lv (L' ++ [d']) = (10 + 3 * Z.of_nat T)%Z /\
    R + cls (L' ++ [d']) + cl (sc x) = cl x + 7 * a + 32 + 2 * T.
Proof.
  intros HQ Hx.
  destruct (s3_climb Q0 x (S (2 * a + 2)) HQ Hx a [Dm] D2 (l0 <* [1]^^9) ltac:(cbn [par]; lia) inv_m2 ltac:(discriminate)
    ltac:(exists Dm; split; [left; reflexivity | discriminate])) as [T [L' [d' [R [S1 [HI' [Hd' [Hl [HT [Hlv Hcl]]]]]]]]]].
  cbn [length] in Hl. change (lv ([Dm] ++ [D2])) with 10%Z in Hlv. change (cls ([Dm] ++ [D2])) with 14 in Hcl.
  exists T, L', d', (R + 9). split.
  - intros r. rewrite zeros_split.
    assert (HQx: count3 (Q0 ++ [x]) = O) by (rewrite count3_app, HQ, count3_one by (apply tgt_ne3; exact Hx); reflexivity).
    rewrite app_assoc. follow (climb_startQ TLone (Q0 ++ [x]) a l0 ([0]^^(2 * T) *> r) dtl HQx).
    rewrite <- !app_assoc. follow (S1 r). rewrite ones_sides. finish.
  - repeat split; auto; lia.
Qed.
Lemma mround REP L Y r: REP <> [] -> count3 REP = O ->
  lstack (rev REP) (base (TDig D2) L) {{SA}}> [0;0;0;0] *> Y *> r -->*
  decstack REP (L <* [1;1;1] <* TB (TDig D2)) {{C}}> [1;1] *> Y *> r.
Proof.
  intros Hn H3. follow erases. rewrite Ers_cat. repeat rewrite Str_app_assoc.
  replace ([0] *> [0;0;0] *> Ercat (rev REP) *> Y *> r) with ([0;0;0;0] *> Ercat (rev REP) *> Y *> r) by reflexivity.
  follow (turnB (TDig D2) L (Ercat (rev REP) *> Y *> r) (or_intror (or_introl eq_refl))).
  rewrite (dec_inputB REP _ Hn).
  pose proof (rp_copy (TDig D2) REP H3 []) as Hc. rewrite app_nil_r in Hc.
  follow (rpass _ _ _ _ _ _ (L <* [1;1;1]) ([1;1] *> Y *> r) Hc).
  rewrite rev_involutive. finish.
Qed.
Lemma mrounds Ys: forall Y L REP r, REP <> [] -> count3 REP = O -> mchain Y Ys ->
  lstack (rev REP) (base (TDig D2) L) {{SA}}> [0;0;0;0] *> Y *> r -->*
  decstack REP (L <* [1]^^(3 * S (length Ys)) <* TB (TDig D2)) <* MREC {{C}}> r.
Proof.
  induction Ys as [|Y' Ys IH]; intros Y L REP r Hn H3 H; cbn [mchain length] in *; follow (mround REP L Y r Hn H3).
  - follow H. finish.
  - destruct H as [H1 H2]. follow H1. rewrite dec_l, (TB_base (TDig D2) _ (or_intror (or_introl eq_refl))).
    follow (IH Y' (L <* [1;1;1]) REP r Hn H3 H2).
    replace (3 * S (S (length Ys))) with (3 * S (length Ys) + 3) by lia. rewrite lpow_add, Str_app_assoc. finish.
Qed.
Lemma merge REP W1 l0 r: REP <> [] -> count3 REP = O -> toks (D2 :: REP) = 3 :: toks W1 ++ [2] ->
  RecT l0 TLone (W1 ++ [Dm;Dm;D3;Dm;D3;D0]) D0 (EXT1 *> [0]^^MZ *> r) -->* RecT (l0 <* [1]^^MR) (TDig D2) (REP ++ MT) ML r.
Proof.
  intros Hn H3 Ht. unfold RecT. rewrite (lone_merge REP W1 l0 Ht).
  follow mg0. follow (mrounds MYs MY0 l0 REP r Hn H3 mgc).
  rewrite (rec_out REP _ MT ML MREC mrec). finish.
Qed.

Lemma count3_snoc Q d: count3 Q = O -> d <> D3 -> count3 (Q ++ [d]) = O.
Proof. intros HQ Hd. rewrite count3_app, HQ. destruct d; [reflexivity..|congruence]. Qed.

Lemma pa_step Q B d k l0 r: count3 Q = O -> Inv B d -> d <> Dm -> 3 <= length B ->
  (lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (length B))%Z ->
  (6 * Z.of_nat (length B) + 1 <= lv (B ++ [d]) + 3 * Z.of_nat k - 3 * 4 ^ Z.of_nat (length B))%Z ->
  (lv (B ++ [d]) + 3 * Z.of_nat k - 3 * 4 ^ Z.of_nat (length B) + 5 <= 3 * 4 ^ Z.of_nat (length B - 1))%Z ->
  exists B' d' R, RecT l0 TLone (Q ++ B) d ([0]^^(2 * k) *> r) -->* RecT (l0 <* [1]^^R) TLone (Q ++ [D0; Dm] ++ B') d' r /\
    Inv B' d' /\ d' <> Dm /\ length B' = length B - 2 /\
    lv (B' ++ [d']) = (lv (B ++ [d]) + 3 * Z.of_nat k - 3 * 4 ^ Z.of_nat (length B))%Z /\
    R + cls ((Q ++ [D0; Dm] ++ B') ++ [d']) = cls ((Q ++ B) ++ [d]) + 2 * k.
Proof.
  intros HQ HI Hd Hl Hv Hm Ht.
  destruct (force_m B d HI ltac:(destruct B; [cbn in Hl; lia | discriminate]) Hv) as [B0 [-> HI1]].
  cbn [length] in Hl, Hv, Hm, Ht |- *. replace (S (length B0) - 1) with (length B0) in Ht by lia.
  change ((Dm :: B0) ++ [d]) with (repeat Dm 1 ++ (B0 ++ [d])) in Hv, Hm, Ht |- *. rewrite lv_dm in Hv, Hm, Ht |- *.
  pose proof (lv_snoc_len B0 d) as EL. pose proof (pow4_ge1 (length B0)) as P0.
  assert (P1: (4 ^ Z.of_nat (S (length B0)) = 4 * 4 ^ Z.of_nat (length B0))%Z) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
  destruct (count_to_top B0 d ltac:(lia)) as [k1 Hk1].
  assert (HQm: count3 (Q ++ [Dm]) = O) by (apply count3_snoc; [exact HQ | discriminate]).
  destruct (count_maxQ TLone (Q ++ [Dm]) dtl HQm k1 B0 d l0 HI1 Hd Hk1) as [N1 [S1 C1]].
  destruct (cycle Q Dm (length B0 - 2) (l0 <* [1]^^N1) HQ ltac:(left; reflexivity))
    as [T [L' [d' [R2 [S2 [HI2 [Hd2 [Hl2 [HT [Hlv2 C2]]]]]]]]]].
  replace (S (S (length B0 - 2))) with (length B0) in S2, Hl2 by lia. cbn [sc] in S2.
  set (k3 := k - k1 - 5 - T).
  assert (Hk3: (Z.of_nat k3 = Z.of_nat k - Z.of_nat k1 - 5 - Z.of_nat T)%Z) by (unfold k3; lia).
  assert (HQ0: count3 (Q ++ [D0]) = O) by (apply count3_snoc; [exact HQ | discriminate]).
  pose proof (lv_snoc_len L' d') as EL2. rewrite Hl2 in EL2.
  destruct (incKQ TLone (Q ++ [D0]) dtl HQ0 k3 L' d' (l0 <* [1]^^N1 <* [1]^^R2) r HI2 Hd2) as [ws' [d0' [N3 [S3 [HI3 [Hd3 [Hl3 [Hw3 [C3 _]]]]]]]]].
  { rewrite Hl2. lia. }
  pose proof (lv_snoc_len ws' d0') as EL3. rewrite Hl3, Hl2 in EL3.
  destruct (force_m ws' d0' HI3 ltac:(destruct ws'; [cbn in Hl3; lia | discriminate])) as [B' [-> HI4]].
  { rewrite Hl3, Hl2. lia. }
  exists B', d0', (N3 + (R2 + N1)). split; [|split; [exact HI4|split; [exact Hd3|split; [|split]]]].
  - replace (2 * k) with (2 * k1 + ((10 + 2 * T) + 2 * k3)) by lia. rewrite !zeros_split.
    replace (Q ++ Dm :: B0) with ((Q ++ [Dm]) ++ B0) by (rewrite <- app_assoc; reflexivity).
    follow (S1 ([0]^^(10 + 2 * T) *> [0]^^(2 * k3) *> r)). rewrite <- app_assoc.
    follow (S2 ([0]^^(2 * k3) *> r)). replace (Q ++ [D0] ++ L') with ((Q ++ [D0]) ++ L') by (rewrite <- app_assoc; reflexivity).
    follow S3. rewrite !ones_sides. replace (Q ++ [D0; Dm] ++ B') with ((Q ++ [D0]) ++ Dm :: B') by (rewrite <- app_assoc; reflexivity).
    finish.
  - cbn [length] in Hl3. lia.
  - assert (E4: lv (B' ++ [d0']) = lv ((Dm :: B') ++ [d0'])) by (symmetry; apply (lv_dm 1)). lia.
  - cn C1. cn C2. cn C3. cng. lia.
Qed.

Lemma xstep Q x B d c y k l0 r: count3 Q = O -> tgt x -> Inv B d -> d <> Dm -> 2 <= length B ->
  Forall pos012 c -> y <> Dm -> length c <= length B ->
  (lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (lv (c ++ [y]) = lv (B ++ [d]) + 3 * Z.of_nat k - 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (6 * Z.of_nat (length B) + 7 <= lv (c ++ [y]))%Z -> (lv (c ++ [y]) + 3 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  Run l0 TLone (Q ++ [x] ++ B) d ([0]^^(2 * k) *> r) (Q ++ [sc x] ++ repeat Dm (length B - length c) ++ c) y r
    (2 * k).
Proof.
  intros HQ Hx HI Hd Hl Hc Hy Hlc Hv Hval Hm Ht.
  pose proof (lv_snoc_len B d) as EL. pose proof (pow4_ge1 (length B)) as P0.
  assert (P1: (4 ^ Z.of_nat (S (length B)) = 4 * 4 ^ Z.of_nat (length B))%Z) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
  destruct (count_to_top B d ltac:(lia)) as [k1 Hk1].
  assert (HQx: count3 (Q ++ [x]) = O) by (apply count3_snoc; [exact HQ | apply tgt_ne3; exact Hx]).
  destruct (count_maxQ TLone (Q ++ [x]) dtl HQx k1 B d l0 HI Hd Hk1) as [N1 [S1 C1]].
  destruct (cycle Q x (length B - 2) (l0 <* [1]^^N1) HQ Hx) as [T [L' [d' [R2 [S2 [HI2 [Hd2 [Hl2 [HT [Hlv2 C2]]]]]]]]]].
  replace (S (S (length B - 2))) with (length B) in S2, Hl2 by lia.
  set (k3 := k - k1 - 5 - T).
  assert (Hk3: (Z.of_nat k3 = Z.of_nat k - Z.of_nat k1 - 5 - Z.of_nat T)%Z) by (unfold k3; lia).
  assert (HQs: count3 (Q ++ [sc x]) = O) by (apply count3_snoc; [exact HQ | apply sc_ne3; exact Hx]).
  pose proof (lv_snoc_len L' d') as EL2. rewrite Hl2 in EL2.
  destruct (count_lowQ (Q ++ [sc x]) HQs k3 L' d' c y (l0 <* [1]^^N1 <* [1]^^R2) r HI2 Hd2 Hy Hc) as [N3 [S3 C3]];
    [lia | lia | rewrite Hl2; lia|].
  exists (N3 + (R2 + N1)). split; cycle 1.
  { rewrite Hl2 in C3. cn C1. cn C2. cn C3. cng. lia. }
  replace (2 * k) with (2 * k1 + ((10 + 2 * T) + 2 * k3)) by lia. rewrite !zeros_split.
  replace (Q ++ [x] ++ B) with ((Q ++ [x]) ++ B) by (rewrite <- app_assoc; reflexivity).
  follow (S1 ([0]^^(10 + 2 * T) *> [0]^^(2 * k3) *> r)). rewrite <- app_assoc.
  follow (S2 ([0]^^(2 * k3) *> r)).
  replace (Q ++ [sc x] ++ L') with ((Q ++ [sc x]) ++ L') by (rewrite <- app_assoc; reflexivity).
  follow S3. rewrite !ones_sides, Hl2, <- app_assoc. finish.
Qed.

Definition pz d := match d with D0 => Dm | D1 => D0 | D2 => D1 | d => d end.
Lemma lv_pos_bound C y: Forall pos012 C -> (dv y <= 3)%Z -> (lv (C ++ [y]) <= 3 * 4 ^ Z.of_nat (S (length C)) + 1)%Z.
Proof.
  intros HC Hy. rewrite lv_snoc_len, wv_snoc. destruct (wv_pos012 C HC) as [_ Hw].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma dv_le3 d: (dv d <= 3)%Z.
Proof. destruct d; cbn; lia. Qed.
Lemma pat_step Q A z e C y k l0 r: count3 (Q ++ A) = O -> (z = D0 \/ z = D1 \/ z = D2) -> Forall pos012 C -> y <> Dm ->
  1 <= e -> 2 <= e + length C ->
  (3 * Z.of_nat k = lv (C ++ [y]) + 5)%Z -> (6 * Z.of_nat (e + length C) + 7 <= lv (C ++ [y]))%Z ->
  Run l0 TLone (Q ++ A ++ [pz z] ++ repeat D2 (e + length C)) D1 ([0]^^(2 * k) *> r)
    (Q ++ A ++ [z] ++ repeat Dm e ++ C) y r (2 * k).
Proof.
  intros HQ Hz HC Hy He Hl Hk Hm.
  assert (Hx: tgt (pz z)) by (unfold tgt; destruct Hz as [-> | [-> | ->]]; cbn; auto).
  assert (Hs: sc (pz z) = z) by (destruct Hz as [-> | [-> | ->]]; reflexivity).
  destruct (cycle (Q ++ A) (pz z) (e + length C - 2) l0 HQ Hx) as [T [L' [d' [R2 [S2 [HI2 [Hd2 [Hl2 [HT [Hlv2 C2]]]]]]]]]].
  replace (S (S (e + length C - 2))) with (e + length C) in S2, Hl2 by lia. rewrite Hs in S2.
  set (k3 := k - 5 - T).
  assert (Hk3: (Z.of_nat k3 = Z.of_nat k - 5 - Z.of_nat T)%Z) by (unfold k3; lia).
  assert (HQz: count3 ((Q ++ A) ++ [z]) = O) by (apply count3_snoc; [exact HQ | destruct Hz as [-> | [-> | ->]]; discriminate]).
  pose proof (lv_snoc_len L' d') as EL2. rewrite Hl2 in EL2.
  pose proof (lv_pos_bound C y HC (dv_le3 y)) as HB.
  assert (P: (4 * 4 ^ Z.of_nat (S (length C)) <= 4 ^ Z.of_nat (S (e + length C)))%Z).
  { replace (4 * 4 ^ Z.of_nat (S (length C)))%Z with (4 ^ Z.of_nat (S (S (length C))))%Z
      by (rewrite (Nat2Z.inj_succ (S (length C))), Z.pow_succ_r by lia; ring).
    apply Z.pow_le_mono_r; lia. }
  destruct (count_lowQ ((Q ++ A) ++ [z]) HQz k3 L' d' C y (l0 <* [1]^^R2) r HI2 Hd2 Hy HC) as [N3 [S3 C3]];
    [lia | lia | rewrite Hl2; lia|].
  exists (N3 + R2). split; cycle 1.
  { rewrite Hs in C2. rewrite Hl2 in C3. cn C2. cn C3. cng. lia. }
  replace (2 * k) with ((10 + 2 * T) + 2 * k3) by lia. rewrite zeros_split.
  rewrite app_assoc. follow (S2 ([0]^^(2 * k3) *> r)).
  replace ((Q ++ A) ++ [z] ++ L') with (((Q ++ A) ++ [z]) ++ L') by (rewrite <- app_assoc; reflexivity).
  follow S3. rewrite ones_sides, Hl2. replace (e + length C - length C) with e by lia. rewrite <- !app_assoc. finish.
Qed.

Lemma wave_fire Q x a l0: count3 Q = O -> tgt x ->
  exists T L' d' R, (forall r, RecT l0 TLone (Q ++ [x] ++ U (S a) 0) D0 ([0]^^(4 + 2 * T) *> r) -->*
    RecT (l0 <* [1]^^R) TLone (Q ++ [sc x] ++ L') d' r) /\
    Inv L' d' /\ d' <> Dm /\ length L' = S (S a) /\ T <= 2 * a + 2 /\ lv (L' ++ [d']) = (10 + 3 * Z.of_nat T)%Z /\
    R + cls ((Q ++ [sc x] ++ L') ++ [d']) = cls ((Q ++ [x] ++ U (S a) 0) ++ [D0]) + (4 + 2 * T).
Proof.
  intros HQ Hx.
  assert (HQx: count3 (Q ++ [x]) = O) by (apply count3_snoc; [exact HQ | apply tgt_ne3; exact Hx]).
  assert (I1: IInc TLone (Q ++ [x] ++ U (S a) 0) D0 (Q ++ [x] ++ U (S a) 0) D1 []) by (apply (II_fast TLone _ D0); auto).
  assert (R: RP TLone [] (Q ++ [x] ++ U (S a) 0) [] TLone (rev (Q ++ [x] ++ U a 1))).
  { rewrite app_assoc. apply rp_pre; [exact HQx|].
    replace (rev (Q ++ [x] ++ U a 1)) with (rev (U a 1) ++ rev (Q ++ [x]) ++ []) by (rewrite app_nil_r, app_assoc, (rev_app_distr (Q ++ [x]) (U a 1)); reflexivity).
    apply rp_waveR. }
  assert (I2: IInc TLone (Q ++ [x] ++ U (S a) 0) D1 (Q ++ [x] ++ U a 1) D2 [1;1;1]).
  { pose proof (II_low1' TLone _ [] _ (app_cons_nn Q x (U (S a) 0)) R) as H. rewrite rev_involutive in H. exact H. }
  destruct (s3_climb Q x (2 * a + 2) HQ Hx a [Dm] D2 (l0 <* [1;1;1]) ltac:(cbn [par]; lia) inv_m2 ltac:(discriminate)
    ltac:(exists Dm; split; [left; reflexivity | discriminate])) as [T [L' [d' [R1 [S1 [HI' [Hd' [Hl [HT [Hlv C1]]]]]]]]]].
  cbn [length] in Hl. change (lv ([Dm] ++ [D2])) with 10%Z in Hlv.
  assert (Ccell: R1 + 3 + cls ((Q ++ [sc x] ++ L') ++ [d']) = cls ((Q ++ [x] ++ U (S a) 0) ++ [D0]) + (4 + 2 * T)).
  { cn C1. cng. lia. }
  exists T, L', d', (R1 + 3). split; [|repeat split; auto; lia].
  intros r. change ([0]^^(4 + 2 * T) *> r) with ([0;0] *> [0;0] *> [0]^^(2 * T) *> r).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I1 ctl). apply (iinc_step _ _ _ _ _ _ _ _ _ I2 ctl).
  replace (Q ++ [x] ++ U a 1) with (Q ++ [x] ++ U a 0 ++ [Dm]) by (unfold U; rewrite <- !app_assoc; reflexivity).
  follow (S1 r). rewrite <- (ones_sides l0 3 R1). finish.
Qed.
Lemma k3_low Q x a c y e k l0 r: count3 Q = O -> tgt x -> Forall pos012 c -> y <> Dm -> e + length c = S (S a) ->
  (3 * Z.of_nat k = lv (c ++ [y]) - 4)%Z -> (6 * Z.of_nat a + 16 <= lv (c ++ [y]))%Z ->
  (lv (c ++ [y]) + 3 <= 3 * 4 ^ Z.of_nat (S (S (S a))))%Z ->
  Run l0 TLone (Q ++ [x] ++ U (S a) 0) D0 ([0]^^(2 * k) *> r) (Q ++ [sc x] ++ repeat Dm e ++ c) y r (2 * k).
Proof.
  intros HQ Hx Hc Hy Hl Hk Hm Ht.
  destruct (wave_fire Q x a l0 HQ Hx) as [T [L' [d' [R1 [S1 [HI' [Hd' [HlL [HT [Hlv C1]]]]]]]]]].
  set (k3 := k - 2 - T).
  assert (Hk3: (Z.of_nat k3 = Z.of_nat k - 2 - Z.of_nat T)%Z) by (unfold k3; lia).
  assert (HQs: count3 (Q ++ [sc x]) = O) by (apply count3_snoc; [exact HQ | apply sc_ne3; exact Hx]).
  pose proof (lv_snoc_len L' d') as EL. rewrite HlL in EL.
  destruct (count_lowQ (Q ++ [sc x]) HQs k3 L' d' c y (l0 <* [1]^^R1) r HI' Hd' Hy Hc) as [N3 [S3 C3]];
    [lia | lia | rewrite HlL; lia|].
  exists (N3 + R1). split; cycle 1.
  { rewrite HlL in C3. cn C1. cn C3. cng. lia. }
  replace (2 * k) with ((4 + 2 * T) + 2 * k3) by lia. rewrite zeros_split.
  follow (S1 ([0]^^(2 * k3) *> r)).
  replace (Q ++ [sc x] ++ L') with ((Q ++ [sc x]) ++ L') by (rewrite <- app_assoc; reflexivity).
  follow S3. rewrite ones_sides, HlL. replace (S (S a) - length c) with e by lia. rewrite <- app_assoc. finish.
Qed.
Lemma k3_max Q x a k l0 r: count3 Q = O -> tgt x -> Z.of_nat k = (4 ^ Z.of_nat (S (S (S a))) - 1)%Z ->
  Run l0 TLone (Q ++ [x] ++ U (S a) 0) D0 ([0]^^(2 * k) *> r) (Q ++ [sc x] ++ repeat D2 (S (S a))) D3 r (2 * k).
Proof.
  intros HQ Hx Hk.
  destruct (wave_fire Q x a l0 HQ Hx) as [T [L' [d' [R1 [S1 [HI' [Hd' [HlL [HT [Hlv C1]]]]]]]]]].
  pose proof (lv_snoc_len L' d') as EL. rewrite HlL in EL.
  assert (P3: (4 * Z.of_nat a + 12 <= 4 ^ Z.of_nat (S (S (S a))))%Z).
  { clear. induction a as [|a IH]; [cbn; lia|]. rewrite (Nat2Z.inj_succ (S (S (S a)))), Z.pow_succ_r by lia. lia. }
  set (k2 := k - 4 - T).
  assert (Hk2: (3 * (wv (L' ++ [d']) + Z.of_nat k2) = 2 * 4 ^ Z.of_nat (S (length L')) - 5)%Z) by (unfold k2; rewrite HlL; lia).
  assert (HQs: count3 (Q ++ [sc x]) = O) by (apply count3_snoc; [exact HQ | apply sc_ne3; exact Hx]).
  destruct (count_maxQ TLone (Q ++ [sc x]) dtl HQs k2 L' d' (l0 <* [1]^^R1) HI' Hd' Hk2) as [N2 [S2 C2]]. rewrite HlL in S2, C2.
  assert (Hc: RP TLone [] ((Q ++ [sc x]) ++ repeat D2 (S (S a))) [] TLone (rev ((Q ++ [sc x]) ++ repeat D2 (S (S a))))).
  { rewrite <- (app_nil_r (rev _)). apply rp_copy. rewrite count3_app, HQs, count3_repeat2. reflexivity. }
  assert (I3: IInc TLone ((Q ++ [sc x]) ++ repeat D2 (S (S a))) D1 ((Q ++ [sc x]) ++ repeat D2 (S (S a))) D2 [1;1;1]).
  { pose proof (II_low1' TLone _ [] _ ltac:(apply app_cons_nn) Hc) as H. rewrite rev_involutive in H. exact H. }
  assert (I4: IInc TLone ((Q ++ [sc x]) ++ repeat D2 (S (S a))) D2 ((Q ++ [sc x]) ++ repeat D2 (S (S a))) D3 [])
    by (apply (II_fast TLone _ D2); auto).
  exists (3 + (N2 + R1)). split; cycle 1.
  { cn C1. cn C2. cng. lia. }
  replace (2 * k) with ((4 + 2 * T) + (2 * k2 + 4)) by lia. rewrite !zeros_split.
  follow (S1 ([0]^^(2 * k2) *> [0]^^4 *> r)).
  replace (Q ++ [sc x] ++ L') with ((Q ++ [sc x]) ++ L') by (rewrite <- app_assoc; reflexivity).
  follow (S2 ([0]^^4 *> r)). change ([0]^^4 *> r) with ([0;0] *> [0;0] *> r).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I3 ctl). apply (iinc_step _ _ _ _ _ _ _ _ _ I4 ctl).
  rewrite <- app_assoc, !ones_sides. finish.
Qed.

Lemma end3 Q l0 r: count3 Q = O ->
  RecT l0 TLone (Q ++ [Dm; D2; D3]) D0 ([0]^^6 *> r) -->* RecT (l0 <* [1;1;1]) TLone (Q ++ [Dm; D3; Dm]) D3 r.
Proof.
  intros HQ.
  assert (R: RP TLone [] (Q ++ [Dm; D2; D3]) [] TLone (rev (Q ++ [Dm; D3; Dm]))).
  { apply rp_pre; [exact HQ|]. rewrite app_nil_r. apply RP_can; [discriminate|]. apply RP_can; [discriminate|].
    apply RP_fire; [right; reflexivity|]. cbn [sc]. rewrite rev_app_distr. apply RP_nil. }
  assert (I1: IInc TLone (Q ++ [Dm; D2; D3]) D0 (Q ++ [Dm; D2; D3]) D1 []) by (apply (II_fast TLone _ D0); auto).
  assert (I2: IInc TLone (Q ++ [Dm; D2; D3]) D1 (Q ++ [Dm; D3; Dm]) D2 [1;1;1]).
  { pose proof (II_low1' TLone _ [] _ (app_cons_nn Q Dm [D2; D3]) R) as H. rewrite rev_involutive in H. exact H. }
  assert (I3: IInc TLone (Q ++ [Dm; D3; Dm]) D2 (Q ++ [Dm; D3; Dm]) D3 []) by (apply (II_fast TLone _ D2); auto).
  change ([0]^^6 *> r) with ([0;0] *> [0;0] *> [0;0] *> r).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I1 ctl). apply (iinc_step _ _ _ _ _ _ _ _ _ I2 ctl).
  apply (iinc_step _ _ _ _ _ _ _ _ _ I3 ctl). finish.
Qed.

Lemma climb_n Q0 x: count3 Q0 = O -> tgt x -> forall n b L d0 l0 r, Inv L d0 -> d0 <> Dm -> (exists d, In d L /\ d <> D2) ->
  (lv (L ++ [d0]) + 3 * Z.of_nat n + 3 <= 3 * 4 ^ Z.of_nat (S (S b + length L)))%Z ->
  exists ws d R, RecT l0 TLone (Q0 ++ [x] ++ U b 0 ++ L) d0 ([0]^^(2 * n) *> r) -->* RecT (l0 <* [1]^^R) TLone (Q0 ++ ws) d r /\
    R + cls ((Q0 ++ ws) ++ [d]) = cls ((Q0 ++ [x] ++ U b 0 ++ L) ++ [d0]) + 2 * n /\ d <> Dm /\
    ((exists b' L', ws = [x] ++ U b' 0 ++ L' /\ Inv L' d /\ (exists e, In e L' /\ e <> D2) /\ b' + length L' = b + length L /\
       lv (L' ++ [d]) = (lv (L ++ [d0]) + 3 * Z.of_nat n)%Z) \/
     (exists L', ws = [sc x] ++ L' /\ Inv L' d /\ length L' = S b + length L /\
       lv (L' ++ [d]) = (lv (L ++ [d0]) + 3 * Z.of_nat n)%Z)).
Proof.
  intros HQ Hx. induction n as [|n IH]; intros b L d0 l0 r HI Hd0 Hxl Hb.
  - exists ([x] ++ U b 0 ++ L), d0, O. split; [cbn [lpow Str_app Nat.mul]; finish|]. split; [lia|]. split; [exact Hd0|].
    left. exists b, L. repeat split; auto; lia.
  - destruct (iinc_exists TLone L d0 dtl HI Hd0 (fun _ => Hxl)) as [L1 [d1 [N [HII [HI1 [Hd1 [Hl [Hv Hc]]]]]]]].
    destruct (iinc_liftg (ctxF Q0 x b) (ctF x b) N TLone _ _ _ _ _ HII (fun i _ => ctxF_ok TLone Q0 x b i ctl HQ Hx) dtl HI)
      as [k [Hk [Hfast [Hslow HL]]]].
    rewrite lpow1_length in Hk. subst N.
    pose proof (HL O ltac:(lia)) as HL0. unfold ctxF in HL0. rewrite (proj2 (Nat.leb_le 0 b)) in HL0 by lia.
    rewrite Nat.sub_0_r, Nat.add_0_l in HL0.
    assert (Elv: lv (L1 ++ [d1]) = (lv (L ++ [d0]) + 3)%Z) by (unfold lv; rewrite Hv, !length_app, Hl; cbn [length]; lia).
    destruct (Nat.le_gt_cases k b) as [Hkb | Hkb].
    + rewrite (TR_F0 x b k O) in HL0 by lia. rewrite (proj2 (Nat.leb_le k b)) in HL0 by lia.
      rewrite <- !app_assoc in HL0.
      assert (Hx1: exists d, In d (repeat Dm k ++ L1) /\ d <> D2).
      { destruct k as [|k]; [rewrite (iinc_nil _ _ _ _ _ _ HII eq_refl); exact Hxl | exists Dm; split; [left; reflexivity | discriminate]]. }
      assert (E1: lv ((repeat Dm k ++ L1) ++ [d1]) = lv (L1 ++ [d1])) by (rewrite <- app_assoc; apply lv_dm).
      destruct (IH (b - k) (repeat Dm k ++ L1) d1 (l0 <* [1]^^(3 * k)) r (inv_dm k L1 d1 HI1) Hd1 Hx1) as [ws [d [R [S1 [C1 [Hd' Hor]]]]]].
      { rewrite E1, Elv, length_app, repeat_length, Hl.
        replace (S (S (b - k) + (k + length L))) with (S (S b + length L)) by lia. lia. }
      exists ws, d, (R + 3 * k). split; [|split; [|split; [exact Hd'|]]].
      * rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * n) *> r) HL0 ctl).
        replace (U (b - k) k ++ L1) with (U (b - k) 0 ++ (repeat Dm k ++ L1))
          by (unfold U; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
        follow S1. rewrite ones_sides. finish.
      * cn C1. cn Hc. cng. lia.
      * rewrite length_app, repeat_length, Hl, E1, Elv in Hor.
        destruct Hor as [[b' [L' [Ew [HI' [Hx' [Hl' Hv']]]]]] | [L' [Ew [HI' [Hl' Hv']]]]].
        -- left. exists b', L'. repeat split; auto; lia.
        -- right. exists L'. repeat split; auto; lia.
    + rewrite (TR_F x b k O) in HL0 by lia. rewrite (proj2 (Nat.leb_gt k b)) in HL0 by lia.
      rewrite <- !app_assoc in HL0.
      assert (HQs: count3 (Q0 ++ [sc x]) = O) by (apply count3_snoc; [exact HQ | apply sc_ne3; exact Hx]).
      assert (E1: lv ((repeat Dm (S b) ++ L1) ++ [d1]) = lv (L1 ++ [d1])) by (rewrite <- app_assoc; apply lv_dm).
      pose proof (lv_snoc_len (repeat Dm (S b) ++ L1) d1) as E2. rewrite length_app, repeat_length, Hl in E2.
      destruct (incKQ TLone (Q0 ++ [sc x]) dtl HQs n (repeat Dm (S b) ++ L1) d1 (l0 <* [1]^^(3 * k + nt x)) r (inv_dm (S b) L1 d1 HI1) Hd1)
        as [ws' [d0' [N3 [S3 [HI3 [Hd3 [Hl3 [Hw3 [C3 _]]]]]]]]].
      { rewrite length_app, repeat_length, Hl. lia. }
      rewrite length_app, repeat_length, Hl in Hl3.
      pose proof (lv_snoc_len ws' d0') as E3. rewrite Hl3 in E3.
      assert (Hnt: nt x + cl (sc x) = cl x + 2) by (destruct Hx as [-> | [-> | ->]]; reflexivity).
      exists ([sc x] ++ ws'), d0', (N3 + (3 * k + nt x)). split; [|split; [|split; [exact Hd3|right]]].
      * rewrite lpow0_2. follow (iinc_sound _ _ _ _ _ _ l0 ([0]^^(2 * n) *> r) HL0 ctl).
        replace (Q0 ++ [sc x] ++ repeat Dm (S b) ++ L1) with ((Q0 ++ [sc x]) ++ repeat Dm (S b) ++ L1)
          by (rewrite <- app_assoc; reflexivity).
        follow S3. rewrite ones_sides, <- app_assoc. finish.
      * cn C3. cn Hc. cng. lia.
      * exists ws'. repeat split; auto. lia.
Qed.

Lemma settle Q0 x b L d k l0 r: count3 Q0 = O -> tgt x -> Inv L d -> d <> Dm -> (exists e, In e L /\ e <> D2) ->
  2 * b + 2 <= k -> (lv (L ++ [d]) + 3 * Z.of_nat k + 3 <= 3 * 4 ^ Z.of_nat (S (S b + length L)))%Z ->
  exists L3 d3 R, RecT l0 TLone (Q0 ++ [x] ++ U b 0 ++ L) d ([0]^^(2 * k) *> r) -->* RecT (l0 <* [1]^^R) TLone (Q0 ++ [sc x] ++ L3) d3 r /\
    Inv L3 d3 /\ d3 <> Dm /\ length L3 = S b + length L /\ lv (L3 ++ [d3]) = (lv (L ++ [d]) + 3 * Z.of_nat k)%Z /\
    R + cls ((Q0 ++ [sc x] ++ L3) ++ [d3]) = cls ((Q0 ++ [x] ++ U b 0 ++ L) ++ [d]) + 2 * k.
Proof.
  intros HQ Hx HI Hd Hxl Hk Hb.
  destruct (s3_climb Q0 x (2 * b + 2) HQ Hx b L d l0 ltac:(destruct (par d); lia) HI Hd Hxl)
    as [T [L' [d' [R1 [S1 [HI' [Hd' [Hl' [HT [Hlv C1]]]]]]]]]].
  assert (HQs: count3 (Q0 ++ [sc x]) = O) by (apply count3_snoc; [exact HQ | apply sc_ne3; exact Hx]).
  pose proof (lv_snoc_len L' d') as E2. rewrite Hl' in E2.
  destruct (Nat.le_gt_cases T k) as [HTk | HTk]; [|lia].
  destruct (incKQ TLone (Q0 ++ [sc x]) dtl HQs (k - T) L' d' (l0 <* [1]^^R1) r HI' Hd') as [ws' [d0' [N3 [S3 [HI3 [Hd3 [Hl3 [Hw3 [C3 _]]]]]]]]].
  { rewrite Hl'. lia. }
  rewrite Hl' in Hl3. pose proof (lv_snoc_len ws' d0') as E3. rewrite Hl3 in E3.
  assert (Ccell: N3 + R1 + cls ((Q0 ++ [sc x] ++ ws') ++ [d0']) = cls ((Q0 ++ [x] ++ U b 0 ++ L) ++ [d]) + 2 * k).
  { cn C1. cn C3. cng. lia. }
  exists ws', d0', (N3 + R1). split; [|repeat split; auto; lia].
  replace (2 * k) with (2 * T + 2 * (k - T)) by lia. rewrite zeros_split.
  follow (S1 ([0]^^(2 * (k - T)) *> r)).
  replace (Q0 ++ [sc x] ++ L') with ((Q0 ++ [sc x]) ++ L') by (rewrite <- app_assoc; reflexivity).
  follow S3. rewrite ones_sides, <- app_assoc. finish.
Qed.

Lemma phaseA L N: scan false L = Some true -> forall s r l0 B d tape, 2 <= r -> 2 * (r + s) + length L <= N + 1 ->
  (6 * Z.of_nat N + 1 <= lv (gw L r))%Z ->
  Inv B d -> d <> Dm -> length B = N - r -> lv (B ++ [d]) = lv (gw L r) ->
  exists B' d' R, RecT l0 TLone (zm r ++ B) d (SG (N - r + 1) s *> tape) -->* RecT (l0 <* [1]^^R) TLone (zm (r + s) ++ B') d' tape /\
    Inv B' d' /\ d' <> Dm /\ length B' = N - (r + s) /\ lv (B' ++ [d']) = lv (gw L (r + s)) /\
    R + cls ((zm (r + s) ++ B') ++ [d']) = cls ((zm r ++ B) ++ [d]) + length (SG (N - r + 1) s).
Proof.
  intros HLr. induction s as [|s IH]; intros r l0 B d tape Hr HN Hg HI Hd Hl Hv.
  - exists B, d, O. rewrite Nat.add_0_r. split; [cbn [SG Str_app lpow]; finish|]. repeat split; auto; try (cbn [SG length]; lia).
  - assert (CL: length (SG (N - r + 1) (S s)) = 6 + 2 * (4 ^ (N - r + 1) - 1) + length (SG (N - S r + 1) s))
      by (rewrite SG_len; replace (pred (N - r + 1)) with (N - S r + 1) by lia; reflexivity).
    rewrite SG_S. pose proof (lv_upper (gw L r) (length L + r - 1) (gw_ok L r HLr) ltac:(rewrite gw_length; lia)) as Hup.
    set (M0 := N - r + 1) in *.
    assert (HI1: Inv (B ++ [d]) D0) by (apply absorb_inv; exact HI).
    assert (E1: lv ((B ++ [d]) ++ [D0]) = (4 * lv (gw L r))%Z) by (rewrite lv_zero, Hv; reflexivity).
    assert (Hk: Z.of_nat (4 ^ M0 - 1) = (4 ^ Z.of_nat M0 - 1)%Z) by apply pow4_nat.
    assert (L1: length (B ++ [d]) = M0) by (rewrite length_app, Hl; cbn [length]; unfold M0; lia).
    assert (Pa: (4 ^ Z.of_nat (S (length L + r - 1)) <= 4 ^ Z.of_nat (M0 - 1))%Z) by (apply pow4_mono; unfold M0; lia).
    pose proof (pow4_S (length L + r - 1)) as PS. pose proof (pow4_S (M0 - 1)) as PS'.
    replace (S (M0 - 1)) with M0 in PS' by (unfold M0; lia).
    destruct (pa_step (zm r) (B ++ [d]) D0 (4 ^ M0 - 1) l0 (SG (pred M0) s *> tape) (count3_zm r) HI1 ltac:(discriminate))
      as [B1 [d1 [R1 [S1 [HI2 [Hd2 [Hl2 [Hv2 C1]]]]]]]]; rewrite ?L1; [lia | lia | lia | lia |].
    rewrite L1, E1, Hk in Hv2. rewrite L1 in Hl2.
    assert (Eg: lv (B1 ++ [d1]) = lv (gw L (S r))) by (rewrite gw_step by lia; lia).
    assert (Hg1: (6 * Z.of_nat N + 1 <= lv (gw L (S r)))%Z) by (rewrite gw_step by lia; lia).
    replace (pred M0) with (N - S r + 1) in S1 by (unfold M0; lia).
    destruct (IH (S r) (l0 <* [1]^^R1) B1 d1 tape ltac:(lia) ltac:(lia) Hg1 HI2 Hd2 ltac:(unfold M0 in Hl2; lia) Eg)
      as [B' [d' [R2 [S2 [HI' [Hd' [Hl' [Hv' C2]]]]]]]].
    exists B', d', (R2 + R1). replace (r + S s) with (S r + s) by lia. split; [|repeat split; auto].
    + follow recT_absorb. rewrite <- app_assoc. follow S1. rewrite app_assoc, zm_snoc. follow S2.
      rewrite ones_sides. finish.
    + rewrite CL. cz C1. cz C2. czg. lia.
Qed.

Lemma scan_dms s a Y: scan s (repeat Dm a ++ D1 :: Y) = scan true Y.
Proof. revert s; induction a as [|a IH]; intros s; cbn [repeat app scan]; [reflexivity | apply IH]. Qed.
Lemma inv_tail a c: Inv (repeat Dm a ++ [D1; D1] ++ repeat D2 c ++ [D3]) D0.
Proof.
  unfold Inv, ok. cbn [lowc]. rewrite <- !app_assoc. cbn [app]. rewrite scan_dms. cbn [scan].
  induction c as [|c IH]; cbn [repeat app scan]; [discriminate | exact IH].
Qed.
Lemma lv11: lv [D1; D1] = 31%Z.
Proof. reflexivity. Qed.
Lemma pow4_c4 c: (64 * 4 ^ Z.of_nat (S c) <= 4 ^ Z.of_nat (c + 4))%Z.
Proof.
  replace (c + 4) with (S (S (S (S c)))) by lia. rewrite (pow4_S (S (S (S c)))), (pow4_S (S (S c))), (pow4_S (S c)). pose proof (pow4_ge1 c). lia.
Qed.
Lemma pow4_big n: 1 <= n -> (6 * Z.of_nat n + 21 <= 3 * 4 ^ Z.of_nat (S n))%Z.
Proof.
  intros H. induction n as [|n IH]; [lia|]. destruct n as [|n]; [cbn; lia|].
  rewrite (pow4_S (S (S n))). specialize (IH ltac:(lia)). lia.
Qed.
Lemma pow4_add2 n: (4 ^ Z.of_nat (S (S n)) = 16 * 4 ^ Z.of_nat n)%Z.
Proof. rewrite (pow4_S (S n)), (pow4_S n). ring. Qed.

Lemma tstep Q0 s k' c l0 tape: count3 Q0 = O -> (6 * Z.of_nat (k' + c + 3) + 7 <= 132 * 4 ^ Z.of_nat (S c) + 1)%Z ->
  Run l0 TLone (Q0 ++ zm s ++ repeat Dm (S k') ++ [D1; D1] ++ repeat D2 c) D3
    ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (k' + c + 4) - 1)) *> tape)
    (Q0 ++ zm s ++ [D0] ++ repeat Dm k' ++ [D1; D1] ++ repeat D2 (S c)) D3 tape (6 + 2 * (4 ^ (k' + c + 4) - 1)).
Proof.
  intros HQ Hm.
  set (B := repeat Dm k' ++ [D1; D1] ++ repeat D2 c ++ [D3]).
  assert (HQs: count3 (Q0 ++ zm s) = O) by (rewrite count3_app, HQ, count3_zm; reflexivity).
  assert (LB: length B = k' + c + 3) by (unfold B; rewrite !length_app, !repeat_length; cbn [length]; lia).
  assert (EB: lv (B ++ [D0]) = (132 * 4 ^ Z.of_nat (S c) + 4)%Z) by (rewrite lv_zero; unfold B; rewrite lv_dm, lv_X2s3, lv11; ring).
  assert (EC: lv (([D1; D1] ++ repeat D2 (S c)) ++ [D3]) = (132 * 4 ^ Z.of_nat (S c) + 1)%Z)
    by (rewrite <- app_assoc, lv_X2s3, lv11, (pow4_S (S c)); ring).
  assert (P5: (4 ^ Z.of_nat (c + 4) <= 4 ^ Z.of_nat (S (k' + c + 3)))%Z) by (apply pow4_mono; lia).
  pose proof (pow4_c4 c) as P6.
  destruct (xstep (Q0 ++ zm s) Dm B D0 ([D1; D1] ++ repeat D2 (S c)) D3 (4 ^ (k' + c + 4) - 1) l0 tape HQs
    ltac:(left; reflexivity) ltac:(unfold B; apply inv_tail) ltac:(discriminate) ltac:(lia)) as [R [S1 C1]].
  { apply Forall_app. split; [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto | apply pos012_repeat2]. }
  { discriminate. }
  { rewrite length_app, repeat_length, LB. cbn [length]. lia. }
  { rewrite LB. lia. }
  { rewrite EC, EB, LB, pow4_nat. replace (S (k' + c + 3)) with (k' + c + 4) by lia. ring. }
  { rewrite EC, LB. lia. }
  { rewrite EC, LB. lia. }
  exists R. split; cycle 1.
  { rewrite LB, length_app, repeat_length in C1. cbn [length] in C1. unfold B in C1. cz C1. czg. lia. }
  follow recT_absorb.
  replace ((Q0 ++ zm s ++ repeat Dm (S k') ++ [D1; D1] ++ repeat D2 c) ++ [D3]) with ((Q0 ++ zm s) ++ [Dm] ++ B)
    by (unfold B; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
  follow S1. cbn [sc]. rewrite LB, length_app, repeat_length. cbn [length].
  replace (k' + c + 3 - (2 + S c)) with k' by lia. rewrite <- !app_assoc. finish.
Qed.
Lemma tinner Q0: count3 Q0 = O -> forall u s c l0 tape, (6 * Z.of_nat (2 * u + c + 3) + 7 <= 132 * 4 ^ Z.of_nat (S c) + 1)%Z ->
  Run l0 TLone (Q0 ++ zm s ++ repeat Dm (2 * u + 1) ++ [D1; D1] ++ repeat D2 c) D3 (SG (2 * u + c + 4) (S u) *> tape)
    (Q0 ++ zm (s + u) ++ [D0] ++ [D1; D1] ++ repeat D2 (c + S u)) D3 tape (length (SG (2 * u + c + 4) (S u))).
Proof.
  intros HQ. induction u as [|u IH]; intros s c l0 tape Hm.
  - rewrite SG_S. cbn [SG Str_app pred]. replace (2 * 0 + c + 4) with (0 + c + 4) by lia.
    destruct (tstep Q0 s 0 c l0 tape HQ ltac:(lia)) as [R [S1 C1]]. exists R. replace (2 * 0 + 1) with 1%nat by lia.
    split; cycle 1. { rewrite !length_app, lz_len. cbn [length]. cz C1. czg. lia. }
    follow S1. rewrite Nat.add_0_r, Nat.add_1_r. finish.
  - rewrite SG_S. replace (2 * S u + c + 4) with (S (2 * u + 1) + c + 4) by lia.
    replace (2 * S u + 1) with (S (S (2 * u + 1))) by lia.
    destruct (tstep Q0 s (S (2 * u + 1)) c l0 (SG (pred (S (2 * u + 1) + c + 4)) (S u) *> tape) HQ ltac:(lia)) as [R1 [S1 C1]].
    replace (pred (S (2 * u + 1) + c + 4)) with (2 * u + S c + 4) in S1 by lia.
    pose proof (pow4_mono (S c) (S (S c)) ltac:(lia)) as P.
    destruct (IH (S s) (S c) (l0 <* [1]^^R1) tape ltac:(lia)) as [R2 [S2 C2]].
    exists (R2 + R1). split; cycle 1.
    { rewrite SG_len. replace (pred (S (2 * u + 1) + c + 4)) with (2 * u + S c + 4) by lia. cz C1. cz C2. czg. lia. }
    follow S1.
    replace (Q0 ++ zm s ++ [D0] ++ repeat Dm (S (2 * u + 1)) ++ [D1; D1] ++ repeat D2 (S c))
      with (Q0 ++ zm (S s) ++ repeat Dm (2 * u + 1) ++ [D1; D1] ++ repeat D2 (S c))
      by (rewrite <- zm_snoc; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
    follow S2. rewrite ones_sides. replace (S s + u) with (s + S u) by lia. replace (S c + S u) with (c + S (S u)) by lia. finish.
Qed.

Lemma ttail Q0 x1 c l0 tape: count3 Q0 = O -> tgt x1 -> 1 <= c ->
  Run l0 TLone (Q0 ++ [x1] ++ [D1] ++ repeat D2 c) D3 (SG (c + 2) 2 *> tape)
    (Q0 ++ [sc x1] ++ [Dm; Dm; Dm] ++ repeat D2 c) D3 tape (length (SG (c + 2) 2)).
Proof.
  intros HQ Hx Hc.
  assert (HQ1: count3 (Q0 ++ [x1]) = O) by (apply count3_snoc; [exact HQ | apply tgt_ne3; exact Hx]).
  destruct (k3_max (Q0 ++ [x1]) D1 (c - 1) (4 ^ (c + 2) - 1) l0 (SG (pred (c + 2)) 1 *> tape) HQ1
    ltac:(right; right; reflexivity)) as [R1 [S1 C1]].
  { rewrite pow4_nat. replace (S (S (S (c - 1)))) with (c + 2) by lia. reflexivity. }
  pose proof (lv_2s3 c) as E. pose proof (pow4_big c Hc) as PL.
  assert (PM: (4 ^ Z.of_nat (S (S (S (c + 1)))) = 64 * 4 ^ Z.of_nat (S c))%Z)
    by (replace (S (S (S (c + 1)))) with (S (S (S (S c)))) by lia; rewrite (pow4_add2 (S (S c))), (pow4_S (S c)); ring).
  destruct (k3_low Q0 x1 (c + 1) (repeat D2 c) D3 3 (4 ^ S c - 1) (l0 <* [1]^^R1) tape HQ Hx
    (pos012_repeat2 c) ltac:(discriminate)) as [R2 [S2 C2]]; [rewrite repeat_length; lia | rewrite pow4_nat, E; lia | rewrite E; lia | rewrite E; lia |].
  exists (R2 + R1). split; cycle 1.
  { rewrite SG_len, SG_len. cbn [SG length]. replace (pred (c + 2)) with (S c) by lia. cz C1. cz C2. czg. lia. }
  rewrite SG_S. follow recT_absorb.
  replace ((Q0 ++ [x1] ++ [D1] ++ repeat D2 c) ++ [D3]) with ((Q0 ++ [x1]) ++ [D1] ++ U (S (c - 1)) 0)
    by (unfold U; replace (S (c - 1)) with c by lia; rewrite <- !app_assoc; reflexivity).
  follow S1. cbn [sc]. replace (pred (c + 2)) with (S c) by lia. rewrite SG_S. follow recT_absorb.
  replace (((Q0 ++ [x1]) ++ [D2] ++ repeat D2 (S (S (c - 1)))) ++ [D3]) with (Q0 ++ [x1] ++ U (S (c + 1)) 0)
    by (unfold U; replace (S (S (c - 1))) with (S c) by lia; replace (c + 1) with (S c) by lia; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
  cbn [SG pred Str_app]. follow S2. cbn [repeat]. rewrite ones_sides. finish.
Qed.

Lemma phaseB P: count3 P = O -> forall s q j l0 tape, s + 1 <= j ->
  Run l0 TLone (P ++ zm q ++ [Dm] ++ repeat D2 j) D3 (SG j s *> tape) (P ++ zm (q + s) ++ [Dm] ++ repeat D2 (j - s))
    D3 tape (length (SG j s)).
Proof.
  intros HP. induction s as [|s IH]; intros q j l0 tape Hj.
  - exists O. rewrite Nat.add_0_r, Nat.sub_0_r. cbn [SG Str_app lpow]. split; [finish|]. cbn [length]. lia.
  - assert (HQ: count3 (P ++ zm q) = O) by (rewrite count3_app, HP, count3_zm; reflexivity).
    pose proof (lv_2s3 (j - 1)) as E. replace (S (j - 1)) with j in E by lia.
    pose proof (pow4_lin (j - 2)) as PL. replace (S (S (j - 2))) with j in PL by lia.
    assert (PM: (4 ^ Z.of_nat (S (S (S (j - 1)))) = 16 * 4 ^ Z.of_nat j)%Z)
      by (replace (S (S (S (j - 1)))) with (S (S j)) by lia; apply pow4_add2).
    destruct (k3_low (P ++ zm q) Dm (j - 1) (repeat D2 (j - 1)) D3 2 (4 ^ j - 1) l0 (SG (pred j) s *> tape) HQ
      ltac:(left; reflexivity) (pos012_repeat2 (j - 1)) ltac:(discriminate)) as [R1 [S1 C1]];
      [rewrite repeat_length; lia | rewrite pow4_nat, E; lia | rewrite E; lia | rewrite E; lia |].
    destruct (IH (S q) (j - 1) (l0 <* [1]^^R1) tape ltac:(lia)) as [R2 [S2 C2]].
    exists (R2 + R1). split; cycle 1.
    { rewrite SG_len. replace (pred j) with (j - 1) by lia. cz C1. cz C2. czg. lia. }
    rewrite SG_S. follow recT_absorb.
    replace ((P ++ zm q ++ [Dm] ++ repeat D2 j) ++ [D3]) with ((P ++ zm q) ++ [Dm] ++ U (S (j - 1)) 0)
      by (unfold U; replace (S (j - 1)) with j by lia; rewrite <- !app_assoc; reflexivity).
    follow S1. cbn [sc repeat]. replace (pred j) with (j - 1) by lia.
    replace ((P ++ zm q) ++ [D0] ++ [Dm; Dm] ++ repeat D2 (j - 1)) with (P ++ zm (S q) ++ [Dm] ++ repeat D2 (j - 1))
      by (rewrite <- zm_snoc, <- !app_assoc; reflexivity).
    follow S2. rewrite ones_sides. replace (S q + s) with (q + S s) by lia.
    replace (j - 1 - s) with (j - S s) by lia. finish.
Qed.

Lemma s3_end P q l0 tape: count3 P = O ->
  RecT l0 TLone (P ++ zm (S q) ++ [Dm] ++ repeat D2 1) D3 (SG 1 1 *> [1;1;1;1;1;1] *> [1;1;1;1;1;1] *> tape) -->*
    RecT (l0 <* [1;1;1]) TLone ((P ++ zm q ++ [D0]) ++ [Dm; Dm; D3; Dm; D3; D0]) D0 tape.
Proof.
  intros HP. rewrite SG_S. cbn [SG pred]. follow recT_absorb.
  assert (HQ: count3 (P ++ zm (S q)) = O) by (rewrite count3_app, HP, count3_zm; reflexivity).
  replace ((P ++ zm (S q) ++ [Dm] ++ repeat D2 1) ++ [D3]) with ((P ++ zm (S q)) ++ [Dm; D2; D3])
    by (cbn [repeat]; rewrite <- !app_assoc; reflexivity).
  change (2 * (4 ^ 1 - 1)) with 6.
  follow (end3 (P ++ zm (S q)) l0 ([1;1;1;1;1;1] *> [1;1;1;1;1;1] *> tape) HQ).
  follow recT_absorb. follow recT_absorb.
  replace ((((P ++ zm (S q)) ++ [Dm; D3; Dm]) ++ [D3]) ++ [D0]) with ((P ++ zm q ++ [D0]) ++ [Dm; Dm; D3; Dm; D3; D0])
    by (rewrite <- zm_snoc, <- !app_assoc; reflexivity).
  finish.
Qed.

Lemma xpat Q x B d a A z e C y k1 k2 l0 r: count3 Q = O -> tgt x -> Inv B d -> d <> Dm -> 2 <= length B ->
  Forall pos012 A -> (z = D1 \/ z = D2) -> Forall pos012 C -> y <> Dm -> 1 <= e -> 2 <= e + length C ->
  a + length A + 1 + e + length C = length B ->
  (lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (lv ((A ++ [pz z] ++ repeat D2 (e + length C)) ++ [D1]) = lv (B ++ [d]) + 3 * Z.of_nat k1 - 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (6 * Z.of_nat (length B) + 7 <= lv ((A ++ [pz z] ++ repeat D2 (e + length C)) ++ [D1]))%Z ->
  (lv ((A ++ [pz z] ++ repeat D2 (e + length C)) ++ [D1]) + 3 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (3 * Z.of_nat k2 = lv (C ++ [y]) + 5)%Z -> (6 * Z.of_nat (e + length C) + 7 <= lv (C ++ [y]))%Z ->
  Run l0 TLone (Q ++ [x] ++ B) d ([0]^^(2 * (k1 + k2)) *> r)
    (Q ++ [sc x] ++ repeat Dm a ++ A ++ [z] ++ repeat Dm e ++ C) y r (2 * (k1 + k2)).
Proof.
  intros HQ Hx HI Hd Hl HA Hz HC Hy He He2 Hlen Hv Hid Hm Ht Hk2 Hm2.
  assert (Hc0: Forall pos012 (A ++ [pz z] ++ repeat D2 (e + length C))).
  { apply Forall_app. split; [exact HA|]. apply Forall_cons; [|apply pos012_repeat2].
    unfold pos012. destruct Hz as [-> | ->]; cbn; auto. }
  assert (Lc0: length (A ++ [pz z] ++ repeat D2 (e + length C)) = length A + 1 + e + length C)
    by (rewrite !length_app, repeat_length; cbn [length]; lia).
  destruct (xstep Q x B d (A ++ [pz z] ++ repeat D2 (e + length C)) D1 k1 l0 ([0]^^(2 * k2) *> r) HQ Hx HI Hd Hl Hc0
    ltac:(discriminate) ltac:(rewrite Lc0; lia) Hv Hid Hm Ht) as [R1 [S1 C1]].
  assert (HQ2: count3 ((Q ++ [sc x]) ++ repeat Dm a ++ A) = O)
    by (rewrite !count3_app, HQ, count3_repeatm, (count3_pos012 A HA), (count3_one (sc x) (sc_ne3 x Hx)); reflexivity).
  destruct (pat_step (Q ++ [sc x]) (repeat Dm a ++ A) z e C y k2 (l0 <* [1]^^R1) r HQ2 ltac:(destruct Hz as [-> | ->]; auto)
    HC Hy He He2 Hk2 Hm2) as [R2 [S2 C2]].
  exists (R2 + R1). split; cycle 1.
  { rewrite Lc0 in C1. cz C1. cz C2. czg. lia. }
  replace (2 * (k1 + k2)) with (2 * k1 + 2 * k2) by lia. rewrite zeros_split.
  follow S1. rewrite Lc0. replace (length B - (length A + 1 + e + length C)) with a by lia.
  replace (Q ++ [sc x] ++ repeat Dm a ++ A ++ [pz z] ++ repeat D2 (e + length C))
    with ((Q ++ [sc x]) ++ (repeat Dm a ++ A) ++ [pz z] ++ repeat D2 (e + length C)) by (rewrite <- !app_assoc; reflexivity).
  follow S2. rewrite ones_sides, <- !app_assoc. finish.
Qed.

Lemma gw_first X: lv (gw (X ++ [D1]) 2) = (4 * lv (X ++ [D2]) - 3)%Z.
Proof. unfold gw. cbn [Nat.sub repeat app]. rewrite !lv_snoc. cbn [dv]. ring. Qed.

Lemma first2 e Z X l0 rest: 2 <= e -> length X = length Z -> 2 <= length Z ->
  Inv (repeat Dm (e - 1) ++ Z) D2 -> (lv (X ++ [D2]) = lv (Z ++ [D2]) - 12)%Z ->
  (6 * Z.of_nat (e - 1 + length Z) + 1 <= lv (gw (X ++ [D1]) 2))%Z ->
  (4 * lv (X ++ [D2]) + 6 * Z.of_nat (e - 1 + length Z) + 5 <= 3 * 4 ^ Z.of_nat (e - 1 + length Z - 1))%Z ->
  exists B d R, RecT l0 TLone (repeat Dm e ++ Z) D2
      ([0]^^(2 * (4 ^ S (e - 1 + length Z) - 4)) *> SG (e - 1 + length Z) 1 *> rest) -->*
    RecT (l0 <* [1]^^R) TLone (zm 2 ++ B) d rest /\
    Inv B d /\ d <> Dm /\ length B = e - 1 + length Z - 2 /\ lv (B ++ [d]) = lv (gw (X ++ [D1]) 2) /\
    R + cls ((zm 2 ++ B) ++ [d]) =
      cls ((repeat Dm e ++ Z) ++ [D2]) + (2 * (4 ^ S (e - 1 + length Z) - 4) + length (SG (e - 1 + length Z) 1)).
Proof.
  intros He HXZ HZ HI HXv Hg Hsm.
  set (N := e - 1 + length Z) in *. rewrite gw_first in Hg. set (lam := lv (X ++ [D2])) in *.
  assert (HN: 3 <= N) by (unfold N; lia).
  assert (LB0: length (repeat Dm (e - 1) ++ Z) = N) by (rewrite length_app, repeat_length; unfold N; lia).
  pose proof (pow4_ge1 N) as P0. pose proof (pow4_S N) as P1. pose proof (pow4_S (N - 1)) as P2.
  replace (S (N - 1)) with N in P2 by lia. pose proof (pow4_S (S N)) as P3.
  assert (EZ: lv ((repeat Dm (e - 1) ++ Z) ++ [D2]) = lv (Z ++ [D2])) by (rewrite <- app_assoc; apply lv_dm).
  pose proof (lv_snoc_len (repeat Dm (e - 1) ++ Z) D2) as EZ2. rewrite LB0 in EZ2.
  destruct (count_to_top (repeat Dm (e - 1) ++ Z) D2) as [kmax Hkm]; [rewrite LB0; lia|]. rewrite LB0 in Hkm.
  assert (HQm: count3 [Dm] = O) by reflexivity.
  destruct (count_maxQ TLone [Dm] dtl HQm kmax (repeat Dm (e - 1) ++ Z) D2 l0 HI ltac:(discriminate)) as [N1 [S1 C1]]; [rewrite LB0; exact Hkm|].
  rewrite LB0 in S1, C1.
  destruct (lv_mod3 (X ++ [D2])) as [q Eq]. fold lam in Eq.
  assert (Hlam: (10 <= lam)%Z) by (unfold lam; rewrite lv_snoc; pose proof (lv_ge1 X); cbn [dv]; lia).
  assert (Hq: (3 <= q)%Z) by lia.
  set (n1 := Z.to_nat (q - 3)).
  assert (En1: (3 * Z.of_nat n1 = lam - 10)%Z) by (unfold n1; rewrite Z2Nat.id by lia; lia).
  set (ks := 2 * N - 2). set (k5 := 4 ^ N - 1 - ks).
  assert (Hks: (Z.of_nat k5 = 4 ^ Z.of_nat N - 1 - Z.of_nat ks)%Z) by (unfold k5; rewrite Nat2Z.inj_sub, pow4_nat by (unfold ks; lia); unfold ks; lia).
  destruct (climb_n [] Dm (count3_zm 0) ltac:(left; reflexivity) n1 (N - 2) [Dm] D2 (l0 <* [1]^^N1 <* [1]^^9)
    ([1;1;1;1;1;1] *> [0]^^(2 * ks) *> [0]^^(2 * k5) *> rest) inv_m2 ltac:(discriminate)
    ltac:(exists Dm; split; [left; reflexivity | discriminate])) as [ws [d [R3 [S3 [C3 [Hd Hor]]]]]].
  { change (lv ([Dm] ++ [D2])) with 10%Z. cbn [length]. replace (S (S (N - 2) + 1)) with (S N) by lia. lia. }
  change (lv ([Dm] ++ [D2])) with 10%Z in Hor. cbn [length] in Hor. rewrite En1 in Hor.
  assert (Hset: exists L3 d3 R4, RecT (l0 <* [1]^^N1 <* [1]^^9 <* [1]^^R3) TLone ([] ++ ws ++ [d]) D0 ([0]^^(2 * ks) *> [0]^^(2 * k5) *> rest) -->*
      RecT (l0 <* [1]^^N1 <* [1]^^9 <* [1]^^R3 <* [1]^^R4) TLone ([] ++ [D0] ++ L3) d3 ([0]^^(2 * k5) *> rest) /\
      Inv L3 d3 /\ d3 <> Dm /\ length L3 = S N /\ lv (L3 ++ [d3]) = (4 * lam + 3 * Z.of_nat ks)%Z /\
      R4 + cls (([] ++ [D0] ++ L3) ++ [d3]) = cls (([] ++ ws ++ [d]) ++ [D0]) + 2 * ks).
  { destruct Hor as [[b' [L' [Ew [HI' [Hx' [Hl' Hv']]]]]] | [L' [Ew [HI' [Hl' Hv']]]]]; subst ws.
    - assert (HL': L' <> []) by (destruct Hx' as [e0 [Hin _]]; destruct L'; [destruct Hin | discriminate]).
      assert (Hb: 1 <= length L') by (destruct L'; [congruence | cbn; lia]).
      destruct (settle [] Dm b' (L' ++ [d]) D0 ks (l0 <* [1]^^N1 <* [1]^^9 <* [1]^^R3) ([0]^^(2 * k5) *> rest) (count3_zm 0)
        ltac:(left; reflexivity) (absorb_inv L' d HI') ltac:(discriminate)) as [L3 [d3 [R4 [S4 [HI4 [Hd4 [Hl4 [Hv4 C4]]]]]]]].
      { destruct Hx' as [e0 [Hin Hne]]. exists e0. split; [apply in_or_app; left; exact Hin | exact Hne]. }
      { unfold ks. lia. }
      { rewrite lv_zero, Hv', length_app. cbn [length]. replace (S (S b' + (length L' + 1))) with (S (S N)) by lia. lia. }
      exists L3, d3, R4. cbn [app] in S4 |- *. rewrite <- ?app_assoc. split; [exact S4|]. rewrite length_app in Hl4. cbn [length] in Hl4.
      rewrite lv_zero, Hv' in Hv4. repeat split; auto; try lia; cz C4; czg; lia.
    - assert (HQ0: count3 [D0] = O) by reflexivity.
      assert (HlL: length (L' ++ [d]) = S N) by (rewrite length_app; cbn [length]; lia).
      pose proof (lv_snoc_len (L' ++ [d]) D0) as E4. rewrite HlL in E4. rewrite lv_zero, Hv' in E4.
      destruct (incKQ TLone [D0] dtl HQ0 ks (L' ++ [d]) D0 (l0 <* [1]^^N1 <* [1]^^9 <* [1]^^R3) ([0]^^(2 * k5) *> rest)
        (absorb_inv L' d HI') ltac:(discriminate)) as [L3 [d3 [R4 [S4 [HI4 [Hd4 [Hl4 [Hw4 [C4 _]]]]]]]]].
      { rewrite HlL. unfold ks. lia. }
      exists L3, d3, R4. cbn [app] in S4 |- *. rewrite <- ?app_assoc. split; [exact S4|].
      rewrite HlL in Hl4. pose proof (lv_snoc_len L3 d3) as E5. rewrite Hl4 in E5. repeat split; auto; try lia; cz C4; czg; lia. }
  destruct Hset as [L3 [d3 [R4 [S4 [HI4 [Hd4 [Hl4 [Hv4 C4]]]]]]]].
  destruct (force_m L3 d3 HI4 ltac:(destruct L3; [cbn in Hl4; lia | discriminate])) as [B3 [-> HI5]].
  { rewrite Hv4, Hl4. unfold ks. lia. }
  cbn [length] in Hl4. assert (E5: lv ((Dm :: B3) ++ [d3]) = lv (B3 ++ [d3])) by (apply (lv_dm 1)).
  destruct (pa_step (zm 1) B3 d3 k5 (l0 <* [1]^^N1 <* [1]^^9 <* [1]^^R3 <* [1]^^R4) rest (count3_zm 1) HI5 Hd4) as [B' [d' [R5 [S5 [HI' [Hd' [Hl' [Hv' C5]]]]]]]];
    [lia | rewrite <- E5, Hv4; replace (length B3) with N by lia; unfold ks; lia
         | rewrite <- E5, Hv4; replace (length B3) with N by lia; rewrite Hks; unfold ks; lia
         | rewrite <- E5, Hv4; replace (length B3) with N by lia; rewrite Hks; unfold ks; lia |].
  assert (Eks: 4 ^ N - 1 = ks + k5) by (unfold k5, ks; lia).
  assert (Ec0: 4 ^ S N - 4 = kmax + 5 + n1).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_sub by (pose proof (Nat.pow_le_mono_r 4 1 (S N)); cbn in *; lia).
    rewrite Nat2Z.inj_pow. lia. }
  assert (Ccell: R5 + (R4 + (R3 + (9 + N1))) + cls ((zm 2 ++ B') ++ [d']) =
    cls ((repeat Dm e ++ Z) ++ [D2]) + (2 * (4 ^ S N - 4) + length (SG N 1))).
  { rewrite SG_len. cbn [SG length]. cz C1. cz C3. cz C4. cz C5. czg. lia. }
  exists B', d', (R5 + (R4 + (R3 + (9 + N1)))). split.
  - rewrite Ec0. replace (2 * (kmax + 5 + n1)) with (2 * kmax + (10 + 2 * n1)) by lia. rewrite !zeros_split.
    cbn [SG pred]. rewrite !Str_app_assoc. change ([0]^^10 *> [0]^^(2 * n1) *> ?r) with ([0]^^(10 + 2 * n1) *> r).
    assert (Ee: repeat Dm e = [Dm] ++ repeat Dm (e - 1)) by (destruct e as [|e']; [lia | replace (S e' - 1) with e' by lia; reflexivity]).
    rewrite Ee, <- app_assoc.
    follow (S1 ([0]^^(10 + 2 * n1) *> [1;1;1;1;1;1] *> [0]^^(2 * (4 ^ N - 1)) *> [] *> rest)).
    rewrite zeros_split. replace N with (S (S (N - 2))) at 1 by lia.
    follow (climb_startQ TLone [Dm] (N - 2) (l0 <* [1]^^N1) ([0]^^(2 * n1) *> [1;1;1;1;1;1] *> [0]^^(2 * (4 ^ N - 1)) *> [] *> rest) dtl HQm).
    replace (2 * (4 ^ N - 1)) with (2 * ks + 2 * k5) by (unfold k5, ks; lia). rewrite zeros_split. cbn [Str_app].
    follow S3. follow recT_absorb. follow S4. cbn [app]. change (D0 :: Dm :: B3) with (zm 1 ++ B3).
    follow S5. rewrite app_assoc, zm_snoc, !ones_sides. finish.
  - repeat split; auto; [lia | rewrite Hv', <- E5, Hv4, Hks, gw_first; fold lam; replace (length B3) with N by lia; lia].
Qed.

Lemma xstep_auto Q x B d c y l0 r: count3 Q = O -> tgt x -> Inv B d -> d <> Dm -> 2 <= length B ->
  Forall pos012 c -> y <> Dm -> length c <= length B ->
  (lv (c ++ [y]) + 3 = lv (B ++ [d]))%Z -> (lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (6 * Z.of_nat (length B) + 7 <= lv (c ++ [y]))%Z ->
  Run l0 TLone (Q ++ [x] ++ B) d ([0]^^(2 * (4 ^ S (length B) - 1)) *> r)
    (Q ++ [sc x] ++ repeat Dm (length B - length c) ++ c) y r (2 * (4 ^ S (length B) - 1)).
Proof. intros HQ Hx HI Hd Hl Hc Hy Hlc Hrel Hv Hm. apply xstep; auto; rewrite ?pow4_nat; lia. Qed.

Lemma dv_pz z: z = D0 \/ z = D1 \/ z = D2 -> dv (pz z) = (dv z - 1)%Z.
Proof. intros [-> | [-> | ->]]; reflexivity. Qed.
Lemma pat_rel A z e C y: z = D0 \/ z = D1 \/ z = D2 ->
  (lv ((A ++ [pz z] ++ repeat D2 (e + length C)) ++ [D1]) + lv (C ++ [y]) + 5 = lv (A ++ [z] ++ repeat Dm e ++ C ++ [y]))%Z.
Proof.
  intros Hz. rewrite <- !app_assoc, !(lv_app A). cbn [app length].
  rewrite !lv_cons, lv_dm, lv_2s1, (dv_pz z Hz), !length_app, !repeat_length. cbn [length].
  replace (e + length C + 1) with (S (e + length C)) by lia. replace (e + (length C + 1)) with (S (e + length C)) by lia. ring.
Qed.
Lemma xpat_auto Q x B d a A z e C y l0 r: count3 Q = O -> tgt x -> Inv B d -> d <> Dm -> 2 <= length B ->
  Forall pos012 A -> (z = D1 \/ z = D2) -> Forall pos012 C -> y <> Dm -> 1 <= e -> 2 <= e + length C ->
  a + length A + 1 + e + length C = length B ->
  (lv (A ++ [z] ++ repeat Dm e ++ C ++ [y]) + 3 = lv (B ++ [d]))%Z ->
  (lv (B ++ [d]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B)))%Z ->
  (6 * Z.of_nat (length B) + 12 + lv (C ++ [y]) <= lv (A ++ [z] ++ repeat Dm e ++ C ++ [y]))%Z ->
  (6 * Z.of_nat (e + length C) + 7 <= lv (C ++ [y]))%Z ->
  Run l0 TLone (Q ++ [x] ++ B) d ([0]^^(2 * (4 ^ S (length B) - 1)) *> r)
    (Q ++ [sc x] ++ repeat Dm a ++ A ++ [z] ++ repeat Dm e ++ C) y r (2 * (4 ^ S (length B) - 1)).
Proof.
  intros HQ Hx HI Hd Hl HA Hz HC Hy He He2 Hlen Hrel Hv Hm1 Hm2.
  pose proof (pat_rel A z e C y ltac:(destruct Hz; auto)) as PR.
  destruct (lv_mod3 (C ++ [y])) as [q2 Eq2]. pose proof (lv_ge1 (C ++ [y])) as G1.
  set (k2 := Z.to_nat (q2 + 2)).
  assert (Hk2: (3 * Z.of_nat k2 = lv (C ++ [y]) + 5)%Z) by (unfold k2; rewrite Z2Nat.id by lia; lia).
  pose proof (pow4_nat (S (length B))) as P.
  assert (Hle: k2 <= 4 ^ S (length B) - 1) by lia.
  set (k1 := 4 ^ S (length B) - 1 - k2).
  assert (Hk1: (Z.of_nat k1 = 4 ^ Z.of_nat (S (length B)) - 1 - Z.of_nat k2)%Z) by (unfold k1; lia).
  replace (4 ^ S (length B) - 1) with (k1 + k2) by (unfold k1; lia).
  apply (xpat Q x B d a A z e C y k1 k2 l0 r); auto; lia.
Qed.

Notation S3run l0 A N W1 T := (exists Rt, RecT l0 TLone A D2
    ([0]^^(2 * (4 ^ S N - 4)) *> SG N N *> [1;1;1;1;1;1] *> [1;1;1;1;1;1] *> T) -->*
  RecT (l0 <* [1]^^Rt) TLone (W1 ++ [Dm; Dm; D3; Dm; D3; D0]) D0 T /\
  Rt + cls ((W1 ++ [Dm; Dm; D3; Dm; D3; D0]) ++ [D0]) = cls (A ++ [D2]) + (2 * (4 ^ S N - 4) + length (SG N N) + 12)).

Lemma s3_skel e Z X N re c P l0 rest: 2 <= e -> length X = length Z -> 2 <= length Z -> N = e - 1 + length Z ->
  Inv (repeat Dm (e - 1) ++ Z) D2 -> (lv (X ++ [D2]) = lv (Z ++ [D2]) - 12)%Z ->
  scan false (X ++ [D1]) = Some true -> 2 <= re -> 2 * re + length X + 1 <= N + 1 ->
  (6 * Z.of_nat N + 1 <= lv (gw (X ++ [D1]) 2))%Z ->
  (4 * lv (X ++ [D2]) + 6 * Z.of_nat N + 5 <= 3 * 4 ^ Z.of_nat (N - 1))%Z ->
  2 <= c -> c <= N - re + 1 -> count3 P = O ->
  (forall B d l0' tail, Inv B d -> d <> Dm -> length B = N - re -> lv (B ++ [d]) = lv (gw (X ++ [D1]) re) ->
     exists R, RecT l0' TLone (zm re ++ B) d (SG (N - re + 1) (N - re + 1 - c) *> tail) -->*
       RecT (l0' <* [1]^^R) TLone (P ++ [Dm] ++ repeat D2 c) D3 tail /\
       R + cls ((P ++ [Dm] ++ repeat D2 c) ++ [D3]) = cls ((zm re ++ B) ++ [d]) + length (SG (N - re + 1) (N - re + 1 - c))) ->
  S3run l0 (repeat Dm e ++ Z) N (P ++ zm (c - 2) ++ [D0]) rest.
Proof.
  intros He HXZ HZ HN HI HXv HL Hre Hle Hg Hsm Hc Hc2 HP Hmid.
  assert (Etape: forall T, SG N N *> T = SG N 1 *> SG (N - 1) (re - 2) *> SG (N - re + 1) (N - re + 1 - c) *> SG c (c - 1) *> SG 1 1 *> T).
  { intros T. replace (SG N N) with (SG N (1 + ((re - 2) + ((N - re + 1 - c) + ((c - 1) + 1))))) by (f_equal; lia).
    rewrite !SG_split. replace (N - 1 - (re - 2)) with (N - re + 1) by lia.
    replace (N - re + 1 - (N - re + 1 - c)) with c by lia. replace (c - (c - 1)) with 1%nat by lia. reflexivity. }
  assert (Elen: length (SG N N) = length (SG N 1) + length (SG (N - 1) (re - 2)) + length (SG (N - re + 1) (N - re + 1 - c)) +
      length (SG c (c - 1)) + length (SG 1 1)).
  { replace (SG N N) with (SG N (1 + ((re - 2) + ((N - re + 1 - c) + ((c - 1) + 1))))) by (f_equal; lia).
    rewrite !SG_split_len. replace (N - 1 - (re - 2)) with (N - re + 1) by lia.
    replace (N - re + 1 - (N - re + 1 - c)) with c by lia. replace (c - (c - 1)) with 1%nat by lia. lia. }
  rewrite Etape.
  set (T5 := [1;1;1;1;1;1] *> [1;1;1;1;1;1] *> rest).
  destruct (first2 e Z X l0 (SG (N - 1) (re - 2) *> SG (N - re + 1) (N - re + 1 - c) *> SG c (c - 1) *> SG 1 1 *> T5)
    He HXZ HZ HI HXv ltac:(rewrite <- HN; exact Hg) ltac:(rewrite <- HN; exact Hsm)) as [B2 [d2 [R1 [S1 [HI2 [Hd2 [Hl2 [Hv2 C1]]]]]]]].
  rewrite <- HN in S1, Hl2, C1.
  destruct (phaseA (X ++ [D1]) N HL (re - 2) 2 (l0 <* [1]^^R1) B2 d2 (SG (N - re + 1) (N - re + 1 - c) *> SG c (c - 1) *> SG 1 1 *> T5)
    ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia) Hg HI2 Hd2 Hl2 Hv2) as [B3 [d3 [R2 [S2 [HI3 [Hd3 [Hl3 [Hv3 C2]]]]]]]].
  replace (N - 2 + 1) with (N - 1) in S2, C2 by lia. replace (2 + (re - 2)) with re in S2, Hl3, Hv3, C2 by lia.
  destruct (Hmid B3 d3 (l0 <* [1]^^R1 <* [1]^^R2) (SG c (c - 1) *> SG 1 1 *> T5) HI3 Hd3 Hl3 Hv3) as [R3 [S3 C3]].
  destruct (phaseB P HP (c - 1) 0 c (l0 <* [1]^^R1 <* [1]^^R2 <* [1]^^R3) (SG 1 1 *> T5) ltac:(lia)) as [R4 [S4 C4]].
  replace (c - (c - 1)) with 1%nat in S4, C4 by lia. replace (0 + (c - 1)) with (S (c - 2)) in S4, C4 by lia.
  exists (3 + (R4 + (R3 + (R2 + R1)))). split; cycle 1.
  { rewrite Elen, SG11. cz C1. cz C2. cz C3. cz C4. czg. lia. }
  follow S1. follow S2. follow S3. follow S4. unfold T5.
  follow (s3_end P (c - 2) (l0 <* [1]^^R1 <* [1]^^R2 <* [1]^^R3 <* [1]^^R4) rest HP).
  rewrite !ones_sides. change [1;1;1] with ([1]^^3). rewrite ones_sides. finish.
Qed.

Definition LrE p := [D0; D1] ++ repeat Dm p.
Definition LrO p := [D2] ++ repeat Dm p.
Lemma lv_dms p: lv (repeat Dm p) = 1%Z.
Proof. rewrite <- (app_nil_r (repeat Dm p)), lv_dm. reflexivity. Qed.
Lemma lv_LrE p: lv (LrE p) = (18 * 4 ^ Z.of_nat p + 1)%Z.
Proof. unfold LrE. rewrite lv_app, repeat_length, lv_dms. change (lv [D0; D1]) with 19%Z. ring. Qed.
Lemma lv_LrO p: lv (LrO p) = (9 * 4 ^ Z.of_nat p + 1)%Z.
Proof. unfold LrO. rewrite lv_app, repeat_length, lv_dms. change (lv [D2]) with 10%Z. ring. Qed.
Lemma shift_rel Y c: lv ((Y ++ repeat D2 c ++ [D3]) ++ [D0]) = (lv (Y ++ repeat D2 (S c) ++ [D3]) + 3)%Z.
Proof. rewrite lv_zero, !lv_X2s3, (pow4_S (S c)). ring. Qed.
Lemma lv_gw Lr r: 2 <= r -> lv (gw ((Lr ++ [D1]) ++ [D1]) r) = ((16 * lv Lr + 17) * 4 ^ Z.of_nat (r - 1) + 1)%Z.
Proof.
  intros Hr. unfold gw. rewrite lv_X2s3. replace (S (r - 2)) with (r - 1) by lia. rewrite !lv_snoc. cbn [dv]. ring.
Qed.
Lemma gw_eq Lr r: gw ((Lr ++ [D1]) ++ [D1]) r = Lr ++ [D1; D1] ++ repeat D2 (r - 2) ++ [D3].
Proof. unfold gw. rewrite <- !app_assoc. reflexivity. Qed.
Lemma inv_mid Y c: scan false Y = Some true -> Inv (Y ++ [D1; D1] ++ repeat D2 c ++ [D3]) D0.
Proof.
  intros H. unfold Inv, ok. cbn [lowc]. rewrite <- !app_assoc, scan_app, H. cbn [app scan].
  induction c as [|c IH]; cbn [repeat app scan]; [discriminate | exact IH].
Qed.
Lemma scan_dms1 p: scan true (repeat Dm p) = Some true.
Proof. induction p as [|p IH]; [reflexivity|]. cbn [repeat scan]. exact IH. Qed.
Lemma scan_dm_true s a Y: scan s (repeat Dm (S a) ++ Y) = scan true Y.
Proof. revert s; induction a as [|a IH]; intros s; [reflexivity|]. cbn [repeat app scan]. apply (IH true). Qed.

Lemma zm_pred R: 1 <= R -> zm R = zm (R - 1) ++ [D0; Dm].
Proof. intros H. rewrite zm_snoc. f_equal. lia. Qed.
Lemma conv A z p q a n B d l0 tail: (A = [D0] /\ z = D1) \/ (A = [] /\ z = D2) -> q >= p + 9 -> a <= 1 ->
  Inv B d -> d <> Dm -> length B = q + length A + p + 2 + a -> n = S (length B) ->
  lv (B ++ [d]) = lv (gw (((A ++ [z] ++ repeat Dm p) ++ [D1]) ++ [D1]) q) ->
  Run l0 TLone (zm q ++ B) d ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ n - 1)) *> tail)
    (zm q ++ [D0] ++ repeat Dm a ++ A ++ [z] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (q - 1)) D3 tail
    (6 + 2 * (4 ^ n - 1)).
Proof.
  intros HAz Hq Ha HI Hd Hl -> Hv.
  assert (Ec: (lv (A ++ [z]) = 19%Z /\ length A = 1%nat) \/ (lv (A ++ [z]) = 10%Z /\ length A = O))
    by (destruct HAz as [[-> ->] | [-> ->]]; auto).
  assert (EL: lv (A ++ [z] ++ repeat Dm p) = ((lv (A ++ [z]) - 1) * 4 ^ Z.of_nat p + 1)%Z)
    by (rewrite app_assoc, lv_app, repeat_length, lv_dms; ring).
  set (C := [D1; D1] ++ repeat D2 (q - 1)).
  assert (G: lv (A ++ [z] ++ repeat Dm p ++ C ++ [D3]) = ((16 * lv (A ++ [z] ++ repeat Dm p) + 17) * 4 ^ Z.of_nat q + 1)%Z).
  { replace (A ++ [z] ++ repeat Dm p ++ C ++ [D3]) with (((A ++ [z] ++ repeat Dm p) ++ [D1; D1]) ++ repeat D2 (q - 1) ++ [D3])
      by (unfold C; rewrite <- !app_assoc; reflexivity).
    rewrite lv_X2s3, (lv_app (A ++ [z] ++ repeat Dm p) [D1; D1]). replace (S (q - 1)) with q by lia.
    change (lv [D1; D1]) with 31%Z. change (4 ^ Z.of_nat (length [D1; D1]))%Z with 16%Z. ring. }
  assert (EC: lv (C ++ [D3]) = (33 * 4 ^ Z.of_nat q + 1)%Z).
  { unfold C. rewrite <- app_assoc, lv_X2s3. replace (S (q - 1)) with q by lia. change (lv [D1; D1]) with 31%Z. ring. }
  assert (LC: length C = q + 1) by (unfold C; rewrite length_app, repeat_length; cbn [length]; lia).
  rewrite lv_gw, EL in Hv by lia. rewrite EL in G.
  set (A4 := (4 ^ Z.of_nat p)%Z) in *. set (U := (4 ^ Z.of_nat q)%Z) in *.
  assert (EU: (4 ^ Z.of_nat (q - 1) * 4 = U)%Z) by (unfold U; replace q with (S (q - 1)) at 2 by lia; rewrite pow4_S; ring).
  assert (HA: (Z.of_nat p + 1 <= A4)%Z) by apply pow4_ge. assert (HU: (Z.of_nat q + 1 <= U)%Z) by apply pow4_ge.
  assert (E2: (4 ^ Z.of_nat (S (length B)) = 4 ^ Z.of_nat (length A + a + 3) * (A4 * U))%Z).
  { rewrite Hl. replace (S (q + length A + p + 2 + a)) with (length A + a + 3 + (p + q)) by lia. rewrite !pow4_add. unfold A4, U. ring. }
  assert (HK: (4 ^ Z.of_nat (length A + 3) <= 4 ^ Z.of_nat (length A + a + 3))%Z) by (apply pow4_mono; lia).
  set (K := (4 ^ Z.of_nat (length A + a + 3))%Z) in *.
  assert (Hv': (4 * lv (B ++ [d]) = 16 * (lv (A ++ [z]) - 1) * (A4 * U) + 33 * U + 4)%Z) by (rewrite Hv, <- EU; ring).
  set (V := (A4 * U)%Z) in *.
  assert (HV: (U <= V /\ A4 <= V)%Z) by (unfold V; split; clear -HA HU; nia).
  assert (HKV: (lv (A ++ [z]) = 19%Z /\ 256 * V <= K * V \/ lv (A ++ [z]) = 10%Z /\ 64 * V <= K * V)%Z).
  { destruct Ec as [[E1 E2'] | [E1 E2']]; [left | right]; rewrite E2' in HK; cbn in HK; split; auto; clear -HK HV HU; nia. }
  destruct (pa_conv B d HI) as [B4 [E4 [HI4 [Hl4 Hv4]]]].
  { rewrite E2. destruct HKV as [[E1 E2'] | [E1 E2']]; rewrite E1 in Hv'; lia. }
  assert (FA: Forall pos012 (A ++ [z])) by (destruct HAz as [[-> ->] | [-> ->]]; repeat apply Forall_cons; try apply Forall_nil;
    unfold pos012; auto).
  assert (FC: Forall pos012 C) by (unfold C; apply Forall_app; split; [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto
    | apply pos012_repeat2]).
  assert (X: exists Rm, RecT l0 TLone (zm q ++ [Dm] ++ B4) D0 ([0]^^(2 * (4 ^ S (length B4) - 1)) *> tail) -->*
      RecT (l0 <* [1]^^Rm) TLone (zm q ++ [sc Dm] ++ repeat Dm a ++ A ++ [z] ++ repeat Dm p ++ C) D3 tail /\
      Rm + cls ((zm q ++ [sc Dm] ++ repeat Dm a ++ A ++ [z] ++ repeat Dm p ++ C) ++ [D3]) =
        cls ((zm q ++ [Dm] ++ B4) ++ [D0]) + 2 * (4 ^ S (length B4) - 1)).
  { assert (G': (lv ((A ++ [z]) ++ repeat Dm p ++ C ++ [D3]) + 3 = lv (B4 ++ [D0]))%Z).
    { rewrite <- app_assoc, G, Hv4. destruct HKV as [[E1 _] | [E1 _]]; rewrite E1 in *; unfold V in Hv'; lia. }
    assert (Gb: (lv (B4 ++ [D0]) + 5 <= 3 * 4 ^ Z.of_nat (S (length B4)))%Z).
    { rewrite Hv4, Hl4, E2. destruct HKV as [[E1 E2'] | [E1 E2']]; rewrite E1 in Hv'; lia. }
    assert (Gm: (6 * Z.of_nat (length B4) + 12 + lv (C ++ [D3]) <= lv ((A ++ [z]) ++ repeat Dm p ++ C ++ [D3]))%Z).
    { rewrite <- app_assoc, G, EC, Hl4, Hl. destruct HKV as [[E1 _] | [E1 _]]; rewrite E1; unfold V in HV; lia. }
    rewrite <- app_assoc in G', Gm. destruct p as [|p'].
    - destruct (xstep_auto (zm q) Dm B4 D0 (A ++ [z] ++ C) D3 l0 tail (count3_zm q) ltac:(left; reflexivity) HI4 ltac:(discriminate)
        ltac:(lia) ltac:(rewrite app_assoc; apply Forall_app; auto) ltac:(discriminate)) as [Rm [Sm Cm]].
      { rewrite !length_app, LC, Hl4, Hl. cbn [length]. lia. }
      { rewrite <- !app_assoc. exact G'. }
      { exact Gb. }
      { rewrite <- !app_assoc. rewrite EC in Gm. cbn [repeat app] in Gm |- *. lia. }
      replace (length B4 - length (A ++ [z] ++ C)) with a in Sm, Cm by (rewrite !length_app, LC, Hl4, Hl; cbn [length]; lia).
      exists Rm. split; [exact Sm | exact Cm].
    - destruct (xpat_auto (zm q) Dm B4 D0 a A z (S p') C D3 l0 tail (count3_zm q) ltac:(left; reflexivity) HI4 ltac:(discriminate)
        ltac:(lia) ltac:(apply Forall_app in FA; tauto) ltac:(destruct HAz as [[_ ->] | [_ ->]]; auto) FC ltac:(discriminate)
        ltac:(lia) ltac:(lia) ltac:(lia) G' Gb Gm ltac:(rewrite EC, LC; lia)) as [Rm [Sm Cm]].
      exists Rm. split; [exact Sm | exact Cm]. }
  destruct X as [Rm [Sm Cm]].
  exists Rm. split; cycle 1.
  { assert (EC4: cls (B ++ [d]) = cls (Dm :: B4)) by (rewrite E4; reflexivity).
    rewrite Hl4 in Cm. unfold C in Cm |- *. cz Cm. cz EC4. czg. lia. }
  follow recT_absorb. rewrite <- app_assoc, E4, <- Hl4.
  follow Sm. cbn [sc]. unfold C. finish.
Qed.

Lemma eo_a t R l0 tail: R >= 2 * t + 11 ->
  Run l0 TLone (zm R ++ LrE (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 2)) D3
    ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 2 * t + 4) - 1)) *> tail)
    (zm R ++ [D1; D1] ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1)) D3 tail
    (6 + 2 * (4 ^ (R + 2 * t + 4) - 1)).
Proof.
  intros HR. set (p := 2 * t + 1) in *.
  set (B := [D1] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 2) ++ [D3]).
  assert (HB: Inv B D0) by (unfold B; rewrite app_assoc; apply inv_mid; cbn [app scan]; apply scan_dms1).
  assert (LB: length B = R + p + 2) by (unfold B; rewrite !length_app, !repeat_length; cbn [length]; lia).
  set (A4 := (4 ^ Z.of_nat p)%Z). set (U := (4 ^ Z.of_nat R)%Z).
  assert (HA: (1 <= A4)%Z) by apply pow4_ge1. assert (HU: (Z.of_nat R + 1 <= U)%Z) by apply pow4_ge.
  assert (EY: lv ([D1] ++ repeat Dm p ++ [D1; D1]) = (96 * A4 + 31)%Z).
  { rewrite app_assoc, lv_app, lv_app, repeat_length, lv_dms. cbn [length]. change (lv [D1]) with 7%Z.
    change (lv [D1; D1]) with 31%Z. unfold A4. change (4 ^ Z.of_nat 2)%Z with 16%Z. ring. }
  assert (ET: lv ([D1] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 1) ++ [D3]) = ((96 * A4 + 33) * U + 1)%Z).
  { replace ([D1] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 1) ++ [D3])
      with (([D1] ++ repeat Dm p ++ [D1; D1]) ++ repeat D2 (R - 1) ++ [D3]) by (rewrite <- !app_assoc; reflexivity).
    rewrite lv_X2s3, EY. replace (S (R - 1)) with R by lia. fold U. ring. }
  assert (EB: lv (B ++ [D0]) = ((96 * A4 + 33) * U + 4)%Z).
  { unfold B. replace ([D1] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 2) ++ [D3])
      with (([D1] ++ repeat Dm p ++ [D1; D1]) ++ repeat D2 (R - 2) ++ [D3]) by (rewrite <- !app_assoc; reflexivity).
    rewrite shift_rel. replace (S (R - 2)) with (R - 1) by lia. rewrite <- !app_assoc. cbn [app] in ET |- *. rewrite ET. ring. }
  assert (EC: lv (([D1; D1] ++ repeat D2 (R - 1)) ++ [D3]) = (33 * U + 1)%Z).
  { rewrite <- app_assoc, lv_X2s3. replace (S (R - 1)) with R by lia. change (lv [D1; D1]) with 31%Z. fold U. ring. }
  assert (E2: (4 ^ Z.of_nat (S (length B)) = 64 * A4 * U)%Z).
  { rewrite LB. replace (S (R + p + 2)) with (p + (R + 3)) by lia. rewrite !pow4_add. unfold A4, U. change (4 ^ Z.of_nat 3)%Z with 64%Z. ring. }
  assert (EW: [] ++ [D1] ++ repeat Dm p ++ ([D1; D1] ++ repeat D2 (R - 1)) ++ [D3] =
    [D1] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 1) ++ [D3]) by (rewrite <- !app_assoc; reflexivity).
  assert (AU: (U <= A4 * U)%Z) by (clear -HA HU; nia).
  destruct (xpat_auto (zm R) D0 B D0 0 [] D1 p ([D1; D1] ++ repeat D2 (R - 1)) D3 l0 tail (count3_zm R)
    ltac:(right; left; reflexivity) HB ltac:(discriminate) ltac:(lia) ltac:(constructor) ltac:(left; reflexivity)
    ltac:(apply Forall_app; split; [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto | apply pos012_repeat2])
    ltac:(discriminate) ltac:(unfold p; lia) ltac:(rewrite length_app, repeat_length; cbn [length]; lia)) as [Rm [Sm Cm]].
  { rewrite length_app, repeat_length, LB. cbn [length]. lia. }
  { rewrite EW, ET, EB. ring. }
  { rewrite EB, E2. lia. }
  { rewrite EW, LB, EC, ET. unfold p. lia. }
  { rewrite EC, length_app, repeat_length. cbn [length]. unfold p. lia. }
  exists Rm. split; cycle 1.
  { replace (S (length B)) with (R + 2 * t + 4) in Cm by (rewrite LB; unfold p; lia). unfold B in Cm. unfold LrE. cz Cm. czg. lia. }
  follow recT_absorb.
  replace ((zm R ++ LrE p ++ [D1; D1] ++ repeat D2 (R - 2)) ++ [D3]) with (zm R ++ [D0] ++ B)
    by (unfold B, LrE; rewrite <- !app_assoc; reflexivity).
  replace (R + 2 * t + 4) with (S (length B)) by (rewrite LB; unfold p; lia).
  follow Sm. cbn [sc repeat app]. finish.
Qed.

Lemma inv_restart a Lr: 1 <= a -> scan true Lr = Some true -> Inv (repeat Dm a ++ Lr ++ [D2]) D2.
Proof.
  intros Ha H. unfold Inv, ok. cbn [lowc]. destruct a as [|a]; [lia|].
  rewrite <- !app_assoc, scan_dm_true, scan_app, H. cbn. discriminate.
Qed.
Lemma scan_LrE p: scan true (LrE p) = Some true.
Proof. unfold LrE. cbn [app scan]. apply scan_dms1. Qed.
Lemma lv_restart_rel Lr: (lv ((Lr ++ [D1]) ++ [D2]) = lv ((Lr ++ [D2]) ++ [D2]) - 12)%Z.
Proof. rewrite !lv_snoc. cbn [dv]. ring. Qed.

Ltac s3t := try lia; try apply lv_restart_rel; try (rewrite !count3_app, !count3_zm; reflexivity).

Lemma s3_Eodd t R l0 rest: R >= 2 * t + 11 -> (Z.of_nat (2 * R + 2 * t + 3) <= 72 * 4 ^ Z.of_nat (2 * t + 1))%Z ->
  S3run l0 (repeat Dm (2 * R) ++ LrE (2 * t + 1) ++ [D2]) (2 * R + 2 * t + 3)
    ((zm R ++ [D1; D1] ++ zm t ++ [D0] ++ [D2; Dm; Dm]) ++ zm (R + t - 2) ++ [D0]) rest.
Proof.
  intros HR HN. set (p := 2 * t + 1) in *. set (N := 2 * R + 2 * t + 3) in *.
  assert (LZ: length (LrE p ++ [D2]) = p + 3) by (unfold LrE; rewrite !length_app, repeat_length; cbn [length]; lia).
  assert (HlX: length (LrE p ++ [D1]) = length (LrE p ++ [D2])) by (rewrite !length_app; reflexivity).
  pose proof (lv_LrE p) as EL. set (A4 := (4 ^ Z.of_nat p)%Z) in *. assert (HA: (1 <= A4)%Z) by apply pow4_ge1.
  assert (EX2: lv ((LrE p ++ [D1]) ++ [D2]) = (288 * A4 + 34)%Z) by (rewrite !lv_snoc, EL; cbn [dv]; ring).
  assert (EG2: lv (gw ((LrE p ++ [D1]) ++ [D1]) 2) = (1152 * A4 + 133)%Z) by (rewrite lv_gw, EL by lia; change (4 ^ Z.of_nat (2 - 1))%Z with 4%Z; ring).
  assert (PN: (4 ^ Z.of_nat (p + 6) <= 4 ^ Z.of_nat (N - 1))%Z) by (apply pow4_mono; unfold N, p; lia).
  rewrite pow4_add in PN. fold A4 in PN. change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  apply (s3_skel (2 * R) (LrE p ++ [D2]) (LrE p ++ [D1]) N (R - 1) (R + t) (zm R ++ [D1; D1] ++ zm t ++ [D0] ++ [D2; Dm; Dm]) l0 rest); s3t.
  - apply inv_restart; [lia | apply scan_LrE].
  - rewrite <- !app_assoc, scan_app. replace (scan false (LrE p)) with (Some true) by (unfold LrE; cbn [app scan]; symmetry; apply scan_dms1). reflexivity.
  - intros B d l0' tail HI Hd Hl Hv. unfold N in Hl. clear LZ HlX EL EX2 EG2 PN HN.
    replace (N - (R - 1) + 1) with (R + 2 * t + 5) by (unfold N; lia).
    replace (R + 2 * t + 5 - (R + t)) with (t + 5) by lia.
    assert (CL: length (SG (R + 2 * t + 5) (t + 5)) = 6 + 2 * (4 ^ (R + 2 * t + 5) - 1) + (6 + 2 * (4 ^ (R + 2 * t + 4) - 1) +
        (length (SG (2 * t + (R - 1) + 4) (S t)) + length (SG (R + t + 2) 2)))).
    { replace (t + 5) with (S (S (S t + 2))) by lia. rewrite SG_len, SG_len, SG_split_len.
      replace (pred (R + 2 * t + 5)) with (R + 2 * t + 4) by lia. replace (pred (R + 2 * t + 4)) with (2 * t + (R - 1) + 4) by lia.
      replace (2 * t + (R - 1) + 4 - S t) with (R + t + 2) by lia. lia. }
    replace (t + 5) with (S (S (t + 1 + 2))) by lia. rewrite !SG_S. cbn [pred].
    replace (R + 2 * t + 5 - 1 - 1) with (R + 2 * t + 3) by lia. rewrite SG_split.
    replace (R + 2 * t + 5 - 1) with (R + 2 * t + 4) by lia.
    destruct (conv [D0] D1 (2 * t + 1) (R - 1) 1 (R + 2 * t + 5) B d l0' ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 2 * t + 4) - 1)) *> SG (R + 2 * t + 3) (t + 1) *> SG (R + 2 * t + 3 - (t + 1)) 2 *> tail) (or_introl (conj eq_refl eq_refl))
      ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
    assert (EW: zm (R - 1) ++ [D0] ++ repeat Dm 1 ++ [D0] ++ [D1] ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1 - 1) =
      zm R ++ LrE (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 2)) by (rewrite (zm_pred R), <- app_assoc by lia;
      replace (R - 1 - 1) with (R - 2) by lia; reflexivity). rewrite EW in S1, C1.
    destruct (eo_a t R (l0' <* [1]^^R1) (SG (R + 2 * t + 3) (t + 1) *> SG (R + 2 * t + 3 - (t + 1)) 2 *> tail) HR) as [R2 [S2 C2]].
    assert (HQ0: count3 (zm R ++ [D1; D1]) = O) by (rewrite count3_app, count3_zm; reflexivity).
    destruct (tinner (zm R ++ [D1; D1]) HQ0 t 0 (R - 1) (l0' <* [1]^^R1 <* [1]^^R2) (SG (R + 2 * t + 3 - (t + 1)) 2 *> tail)) as [R3 [S3 C3]].
    { pose proof (pow4_ge (S (R - 1))). lia. }
    assert (HQ1: count3 ((zm R ++ [D1; D1]) ++ zm (0 + t) ++ [D0]) = O) by (rewrite !count3_app, count3_zm, count3_zm; reflexivity).
    destruct (ttail ((zm R ++ [D1; D1]) ++ zm (0 + t) ++ [D0]) D1 (R + t) (l0' <* [1]^^R1 <* [1]^^R2 <* [1]^^R3) tail HQ1
      ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
    exists (R4 + (R3 + (R2 + R1))). split; cycle 1.
    { replace (S (S (t + 1 + 2))) with (t + 5) by lia. rewrite CL. replace (R - 1 + S t) with (R + t) in C3 by lia.
      cz C1. cz C2. cz C3. cz C4. czg. lia. }
    follow S1. follow S2.
    replace (zm R ++ [D1; D1] ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1))
      with ((zm R ++ [D1; D1]) ++ zm 0 ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1)) by (rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 3) with (2 * t + (R - 1) + 4) at 1 by lia.
    follow S3. replace (R - 1 + S t) with (R + t) by lia.
    replace ((zm R ++ [D1; D1]) ++ zm (0 + t) ++ [D0] ++ [D1; D1] ++ repeat D2 (R + t))
      with (((zm R ++ [D1; D1]) ++ zm (0 + t) ++ [D0]) ++ [D1] ++ [D1] ++ repeat D2 (R + t)) by (rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 3 - (t + 1)) with (R + t + 2) by lia.
    follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app Nat.add]. finish.
Qed.

Lemma scan_LrO p: scan true (LrO p) = Some true.
Proof. unfold LrO. cbn [app scan]. apply scan_dms1. Qed.

Lemma s3_Oodd t R l0 rest: R >= 2 * t + 11 -> (Z.of_nat (2 * R + 2 * t + 3) <= 36 * 4 ^ Z.of_nat (2 * t + 1))%Z ->
  S3run l0 (repeat Dm (2 * R + 1) ++ LrO (2 * t + 1) ++ [D2]) (2 * R + 2 * t + 3)
    ((zm R ++ [D0; D2] ++ zm t ++ [D0] ++ [D2; Dm; Dm]) ++ zm (R + t - 2) ++ [D0]) rest.
Proof.
  intros HR HN. set (p := 2 * t + 1) in *. set (N := 2 * R + 2 * t + 3) in *.
  assert (LZ: length (LrO p ++ [D2]) = p + 2) by (unfold LrO; rewrite !length_app, repeat_length; cbn [length]; lia).
  assert (HlX: length (LrO p ++ [D1]) = length (LrO p ++ [D2])) by (rewrite !length_app; reflexivity).
  pose proof (lv_LrO p) as EL. set (A4 := (4 ^ Z.of_nat p)%Z) in *. assert (HA: (1 <= A4)%Z) by apply pow4_ge1.
  assert (EX2: lv ((LrO p ++ [D1]) ++ [D2]) = (144 * A4 + 34)%Z) by (rewrite !lv_snoc, EL; cbn [dv]; ring).
  assert (EG2: lv (gw ((LrO p ++ [D1]) ++ [D1]) 2) = (576 * A4 + 133)%Z)
    by (rewrite lv_gw, EL by lia; change (4 ^ Z.of_nat (2 - 1))%Z with 4%Z; ring).
  assert (PN: (4 ^ Z.of_nat (p + 6) <= 4 ^ Z.of_nat (N - 1))%Z) by (apply pow4_mono; unfold N, p; lia).
  rewrite pow4_add in PN. fold A4 in PN. change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  apply (s3_skel (2 * R + 1) (LrO p ++ [D2]) (LrO p ++ [D1]) N R (R + t) (zm R ++ [D0; D2] ++ zm t ++ [D0] ++ [D2; Dm; Dm]) l0 rest); s3t.
  - apply inv_restart; [lia | apply scan_LrO].
  - rewrite <- !app_assoc, scan_app. unfold LrO. cbn [app scan]. replace (scan false (repeat Dm p)) with (Some true)
      by (unfold p; replace (2 * t + 1) with (S (2 * t)) by lia; cbn [repeat scan]; symmetry; apply scan_dms1). reflexivity.
  - intros B d l0' tail HI Hd Hl Hv. unfold N in Hl. clear LZ HlX EL EX2 EG2 PN HN.
    replace (N - R + 1) with (R + 2 * t + 4) by (unfold N; lia).
    replace (R + 2 * t + 4 - (R + t)) with (t + 4) by lia.
    assert (CL: length (SG (R + 2 * t + 4) (t + 4)) = 6 + 2 * (4 ^ (R + 2 * t + 4) - 1) +
        (length (SG (2 * t + (R - 1) + 4) (S t)) + length (SG (R + t + 2) 2))).
    { replace (t + 4) with (S (S t + 2)) by lia. rewrite SG_len, SG_split_len.
      replace (pred (R + 2 * t + 4)) with (2 * t + (R - 1) + 4) by lia.
      replace (2 * t + (R - 1) + 4 - S t) with (R + t + 2) by lia. lia. }
    replace (t + 4) with (S (t + 1 + 2)) by lia. rewrite SG_S. cbn [pred].
    replace (R + 2 * t + 4 - 1) with (R + 2 * t + 3) by lia. rewrite SG_split.
    destruct (conv [] D2 (2 * t + 1) R 0 (R + 2 * t + 4) B d l0' (SG (R + 2 * t + 3) (t + 1) *> SG (R + 2 * t + 3 - (t + 1)) 2 *> tail) (or_intror (conj eq_refl eq_refl))
      ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
    change (zm R ++ [D0] ++ repeat Dm 0 ++ [] ++ [D2] ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1))
      with (zm R ++ [D0] ++ LrO (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1)) in S1, C1.
    assert (HQ0: count3 (zm R ++ [D0; D2]) = O) by (rewrite count3_app, count3_zm; reflexivity).
    destruct (tinner (zm R ++ [D0; D2]) HQ0 t 0 (R - 1) (l0' <* [1]^^R1) (SG (R + 2 * t + 3 - (t + 1)) 2 *> tail)) as [R3 [S3 C3]].
    { pose proof (pow4_ge (S (R - 1))). lia. }
    assert (HQ1: count3 ((zm R ++ [D0; D2]) ++ zm (0 + t) ++ [D0]) = O) by (rewrite !count3_app, count3_zm, count3_zm; reflexivity).
    destruct (ttail ((zm R ++ [D0; D2]) ++ zm (0 + t) ++ [D0]) D1 (R + t) (l0' <* [1]^^R1 <* [1]^^R3) tail HQ1
      ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
    exists (R4 + (R3 + R1)). split; cycle 1.
    { replace (S (t + 1 + 2)) with (t + 4) by lia. rewrite CL. replace (R - 1 + S t) with (R + t) in C3 by lia.
      unfold LrO in C1. cz C1. cz C3. cz C4. czg. lia. }
    follow S1.
    replace (zm R ++ [D0] ++ LrO (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1))
      with ((zm R ++ [D0; D2]) ++ zm 0 ++ repeat Dm (2 * t + 1) ++ [D1; D1] ++ repeat D2 (R - 1)) by (unfold LrO; rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 3) with (2 * t + (R - 1) + 4) at 1 by lia.
    follow S3. replace (R - 1 + S t) with (R + t) by lia.
    replace ((zm R ++ [D0; D2]) ++ zm (0 + t) ++ [D0] ++ [D1; D1] ++ repeat D2 (R + t))
      with (((zm R ++ [D0; D2]) ++ zm (0 + t) ++ [D0]) ++ [D1] ++ [D1] ++ repeat D2 (R + t)) by (rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 3 - (t + 1)) with (R + t + 2) by lia.
    follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app Nat.add]. finish.
Qed.

Lemma ee_b p R l0 tail: R >= p + 11 ->
  Run l0 TLone (zm R ++ [D0] ++ LrE p ++ [D1; D1] ++ repeat D2 (R - 1)) D3
    ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + p + 3) - 1)) *> tail)
    (zm R ++ [D0; D0; D2] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 R) D3 tail (6 + 2 * (4 ^ (R + p + 3) - 1)).
Proof.
  intros HR. set (B := repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 1) ++ [D3]).
  assert (LB: length B = p + R + 2) by (unfold B; rewrite !length_app, !repeat_length; cbn [length]; lia).
  set (U := (4 ^ Z.of_nat R)%Z). assert (HU: (Z.of_nat R + 1 <= U)%Z) by apply pow4_ge.
  assert (EB: lv (B ++ [D0]) = (132 * U + 4)%Z).
  { unfold B. rewrite <- app_assoc, lv_dm, shift_rel, lv_X2s3. replace (S (S (R - 1))) with (S R) by lia.
    rewrite (pow4_S R). fold U. change (lv [D1; D1]) with 31%Z. ring. }
  assert (EC: lv (([D1; D1] ++ repeat D2 R) ++ [D3]) = (132 * U + 1)%Z).
  { rewrite <- app_assoc, lv_X2s3, (pow4_S R). fold U. change (lv [D1; D1]) with 31%Z. ring. }
  assert (E2: (64 * U <= 4 ^ Z.of_nat (S (length B)))%Z).
  { rewrite LB. replace (S (p + R + 2)) with (3 + (p + R)) by lia. rewrite (pow4_add 3 (p + R)). change (4 ^ Z.of_nat 3)%Z with 64%Z.
    pose proof (pow4_mono R (p + R) ltac:(lia)). unfold U. lia. }
  assert (HQ: count3 (zm R ++ [D0; D0]) = O) by (rewrite count3_app, count3_zm; reflexivity).
  destruct (xstep_auto (zm R ++ [D0; D0]) D1 B D0 ([D1; D1] ++ repeat D2 R) D3 l0 tail HQ ltac:(right; right; reflexivity)
    ltac:(unfold B; apply inv_tail) ltac:(discriminate) ltac:(lia)) as [Rm [Sm Cm]].
  { apply Forall_app. split; [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto | apply pos012_repeat2]. }
  { discriminate. }
  { rewrite length_app, repeat_length, LB. cbn [length]. lia. }
  { rewrite EC, EB. lia. }
  { rewrite EB. lia. }
  { rewrite EC, LB. lia. }
  exists Rm. split; cycle 1.
  { rewrite LB, length_app, repeat_length in Cm. cbn [length] in Cm. replace (S (p + R + 2)) with (R + p + 3) in Cm by lia.
    unfold B in Cm. unfold LrE. cz Cm. czg. lia. }
  follow recT_absorb.
  replace ((zm R ++ [D0] ++ LrE p ++ [D1; D1] ++ repeat D2 (R - 1)) ++ [D3]) with ((zm R ++ [D0; D0]) ++ [D1] ++ B)
    by (unfold B, LrE; rewrite <- !app_assoc; reflexivity).
  replace (R + p + 3) with (S (length B)) by (rewrite LB; lia).
  follow Sm. cbn [sc]. rewrite LB, length_app, repeat_length. cbn [length]. replace (p + R + 2 - (2 + R)) with p by lia.
  rewrite <- !app_assoc. finish.
Qed.

Lemma s3_Eeven t R l0 rest: 1 <= t -> R >= 2 * t + 11 -> (Z.of_nat (2 * R + 2 * t + 3) <= 72 * 4 ^ Z.of_nat (2 * t))%Z ->
  S3run l0 (repeat Dm (2 * R + 1) ++ LrE (2 * t) ++ [D2]) (2 * R + 2 * t + 3)
    ((zm R ++ [D0; D0; D2; Dm] ++ zm (t - 1) ++ [D0] ++ [D2; Dm; Dm]) ++ zm (R + t - 2) ++ [D0]) rest.
Proof.
  intros Ht HR HN. set (p := 2 * t) in *. set (N := 2 * R + p + 3) in *.
  assert (LZ: length (LrE p ++ [D2]) = p + 3) by (unfold LrE; rewrite !length_app, repeat_length; cbn [length]; lia).
  assert (HlX: length (LrE p ++ [D1]) = length (LrE p ++ [D2])) by (rewrite !length_app; reflexivity).
  pose proof (lv_LrE p) as EL. set (A4 := (4 ^ Z.of_nat p)%Z) in *. assert (HA: (1 <= A4)%Z) by apply pow4_ge1.
  assert (EX2: lv ((LrE p ++ [D1]) ++ [D2]) = (288 * A4 + 34)%Z) by (rewrite !lv_snoc, EL; cbn [dv]; ring).
  assert (EG2: lv (gw ((LrE p ++ [D1]) ++ [D1]) 2) = (1152 * A4 + 133)%Z)
    by (rewrite lv_gw, EL by lia; change (4 ^ Z.of_nat (2 - 1))%Z with 4%Z; ring).
  assert (PN: (4 ^ Z.of_nat (p + 6) <= 4 ^ Z.of_nat (N - 1))%Z) by (apply pow4_mono; unfold N, p; lia).
  rewrite pow4_add in PN. fold A4 in PN. change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  apply (s3_skel (2 * R + 1) (LrE p ++ [D2]) (LrE p ++ [D1]) N R (R + t) (zm R ++ [D0; D0; D2; Dm] ++ zm (t - 1) ++ [D0] ++ [D2; Dm; Dm]) l0 rest); s3t.
  - apply inv_restart; [lia | apply scan_LrE].
  - rewrite <- !app_assoc, scan_app. unfold LrE. cbn [app scan]. rewrite scan_dms1. reflexivity.
  - intros B d l0' tail HI Hd Hl Hv. unfold N, p in Hl. clear LZ HlX EL EX2 EG2 PN HN.
    replace (N - R + 1) with (R + 2 * t + 4) by (unfold N, p; lia).
    replace (R + 2 * t + 4 - (R + t)) with (t + 4) by lia.
    assert (CL: length (SG (R + 2 * t + 4) (t + 4)) = 6 + 2 * (4 ^ (R + 2 * t + 4) - 1) + (6 + 2 * (4 ^ (R + 2 * t + 3) - 1) +
        (length (SG (2 * (t - 1) + R + 4) (S (t - 1))) + length (SG (R + t + 2) 2)))).
    { replace (t + 4) with (S (S (S (t - 1) + 2))) by lia. rewrite SG_len, SG_len, SG_split_len.
      replace (pred (R + 2 * t + 4)) with (R + 2 * t + 3) by lia. replace (pred (R + 2 * t + 3)) with (2 * (t - 1) + R + 4) by lia.
      replace (2 * (t - 1) + R + 4 - S (t - 1)) with (R + t + 2) by lia. lia. }
    replace (t + 4) with (S (S (t + 2))) by lia. rewrite !SG_S. cbn [pred].
    replace (R + 2 * t + 4 - 1 - 1) with (R + 2 * t + 2) by lia. replace (R + 2 * t + 4 - 1) with (R + 2 * t + 3) by lia.
    rewrite SG_split.
    destruct (conv [D0] D1 (2 * t) R 0 (R + 2 * t + 4) B d l0' ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 2 * t + 3) - 1)) *> SG (R + 2 * t + 2) t *>
      SG (R + 2 * t + 2 - t) 2 *> tail) (or_introl (conj eq_refl eq_refl))
      ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
    change (zm R ++ [D0] ++ repeat Dm 0 ++ [D0] ++ [D1] ++ repeat Dm (2 * t) ++ [D1; D1] ++ repeat D2 (R - 1))
      with (zm R ++ [D0] ++ LrE (2 * t) ++ [D1; D1] ++ repeat D2 (R - 1)) in S1, C1.
    destruct (ee_b (2 * t) R (l0' <* [1]^^R1) (SG (R + 2 * t + 2) t *> SG (R + 2 * t + 2 - t) 2 *> tail) ltac:(lia)) as [R2 [S2 C2]].
    assert (HQ0: count3 (zm R ++ [D0; D0; D2; Dm]) = O) by (rewrite count3_app, count3_zm; reflexivity).
    destruct (tinner (zm R ++ [D0; D0; D2; Dm]) HQ0 (t - 1) 0 R (l0' <* [1]^^R1 <* [1]^^R2) (SG (R + 2 * t + 2 - t) 2 *> tail)) as [R3 [S3 C3]].
    { pose proof (pow4_ge (S R)). lia. }
    assert (HQ1: count3 ((zm R ++ [D0; D0; D2; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) = O) by (rewrite !count3_app, !count3_zm; reflexivity).
    destruct (ttail ((zm R ++ [D0; D0; D2; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) D1 (R + t) (l0' <* [1]^^R1 <* [1]^^R2 <* [1]^^R3) tail HQ1
      ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
    exists (R4 + (R3 + (R2 + R1))). split; cycle 1.
    { replace (S (S (t + 2))) with (t + 4) by lia. rewrite CL. unfold LrE in C1, C2. cz C1. cz C2. cz C3. cz C4. czg. lia. }
    follow S1. follow S2.
    replace (zm R ++ [D0; D0; D2] ++ repeat Dm (2 * t) ++ [D1; D1] ++ repeat D2 R)
      with ((zm R ++ [D0; D0; D2; Dm]) ++ zm 0 ++ repeat Dm (2 * (t - 1) + 1) ++ [D1; D1] ++ repeat D2 R)
      by (replace (2 * t) with (S (2 * (t - 1) + 1)) by lia; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
    replace (S (t - 1)) with t in S3 by lia. replace (2 * (t - 1) + R + 4) with (R + 2 * t + 2) in S3 by lia.
    follow S3. replace (R + S (t - 1)) with (R + t) by lia.
    replace ((zm R ++ [D0; D0; D2; Dm]) ++ zm (0 + (t - 1)) ++ [D0] ++ [D1; D1] ++ repeat D2 (R + t))
      with (((zm R ++ [D0; D0; D2; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) ++ [D1] ++ [D1] ++ repeat D2 (R + t)) by (rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 2 - t) with (R + t + 2) by lia.
    follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app Nat.add]. finish.
Qed.
Lemma s3_Eeven0 R l0 rest: R >= 11 -> R <= 105 ->
  S3run l0 (repeat Dm (2 * R + 1) ++ LrE 0 ++ [D2]) (2 * R + 3)
    ((zm R ++ [D0; D0; D2; D2; Dm; Dm]) ++ zm (R - 2) ++ [D0]) rest.
Proof.
  intros HR HR2. set (Nn := 2 * R + 3) in *.
  assert (PN: (4 ^ Z.of_nat 6 <= 4 ^ Z.of_nat (Nn - 1))%Z) by (apply pow4_mono; unfold Nn; lia).
  change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  apply (s3_skel (2 * R + 1) (LrE 0 ++ [D2]) (LrE 0 ++ [D1]) Nn R R (zm R ++ [D0; D0; D2; D2; Dm; Dm]) l0 rest).
  11: change (lv ((LrE 0 ++ [D1]) ++ [D2])) with 322%Z; assert (Nn <= 213) by (unfold Nn; lia); lia.
  10: change (lv (gw ((LrE 0 ++ [D1]) ++ [D1]) 2)) with 1285%Z; unfold Nn; lia.
  5: apply inv_restart; [lia | reflexivity].
  1-11: s3t; first [reflexivity | cbn; lia | unfold Nn; lia | cbn; unfold Nn; lia].
  intros B d l0' tail HI Hd Hl Hv. unfold Nn in Hl. replace (Nn - R + 1) with (R + 4) by (unfold Nn; lia). replace (R + 4 - R) with 4 by lia.
  assert (CL: length (SG (R + 4) 4) = 6 + 2 * (4 ^ (R + 4) - 1) + (6 + 2 * (4 ^ (R + 0 + 3) - 1) + length (SG (R + 2) 2))).
  { rewrite SG_len, SG_len. replace (pred (R + 4)) with (R + 0 + 3) by lia. replace (pred (R + 0 + 3)) with (R + 2) by lia. lia. } rewrite SG_S, SG_S. cbn [pred]. replace (R + 4 - 1 - 1) with (R + 2) by lia. replace (R + 4 - 1) with (R + 3) by lia.
  destruct (conv [D0] D1 0 R 0 (R + 4) B d l0' ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 3) - 1)) *> SG (R + 2) 2 *> tail) (or_introl (conj eq_refl eq_refl))
    ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
  change (zm R ++ [D0] ++ repeat Dm 0 ++ [D0] ++ [D1] ++ repeat Dm 0 ++ [D1; D1] ++ repeat D2 (R - 1))
    with (zm R ++ [D0] ++ LrE 0 ++ [D1; D1] ++ repeat D2 (R - 1)) in S1, C1.
  destruct (ee_b 0 R (l0' <* [1]^^R1) (SG (R + 2) 2 *> tail) ltac:(lia)) as [R2 [S2 C2]].
  assert (HQ: count3 (zm R ++ [D0; D0; D2]) = O) by (rewrite count3_app, count3_zm; reflexivity).
  destruct (ttail (zm R ++ [D0; D0; D2]) D1 R (l0' <* [1]^^R1 <* [1]^^R2) tail HQ ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
  exists (R4 + (R2 + R1)). split; cycle 1.
  { rewrite CL. unfold LrE in C1, C2. cz C1. cz C2. cz C4. czg. lia. }
  follow S1. replace (R + 3) with (R + 0 + 3) by lia. follow S2.
  replace (zm R ++ [D0; D0; D2] ++ repeat Dm 0 ++ [D1; D1] ++ repeat D2 R) with ((zm R ++ [D0; D0; D2]) ++ [D1] ++ [D1] ++ repeat D2 R)
    by (cbn [repeat]; rewrite <- !app_assoc; reflexivity).
  follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app]. finish.
Qed.

Lemma inv_O p c: Inv ([D2] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 c ++ [D3]) D0.
Proof. pose proof (inv_tail p c) as H. unfold Inv, ok in *. cbn [app scan] in *. exact H. Qed.
Lemma oe_a p R l0 tail: R >= p + 11 ->
  Run l0 TLone (zm R ++ LrO p ++ [D1; D1] ++ repeat D2 (R - 2)) D3
    ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + p + 2) - 1)) *> tail)
    (zm (R - 1) ++ [D0; D0] ++ repeat Dm (S p) ++ [D1; D1] ++ repeat D2 (R - 1)) D3 tail
    (6 + 2 * (4 ^ (R + p + 2) - 1)).
Proof.
  intros HR. set (B := [D2] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 2) ++ [D3]).
  assert (LB: length B = R + p + 2) by (unfold B; rewrite !length_app, !repeat_length; cbn [length]; lia).
  set (A4 := (4 ^ Z.of_nat p)%Z). set (W := (4 ^ Z.of_nat R)%Z).
  assert (HA: (1 <= A4)%Z) by apply pow4_ge1. assert (HW: (Z.of_nat R + 1 <= W)%Z) by apply pow4_ge.
  assert (EB: lv (B ++ [D0]) = ((144 * A4 + 33) * W + 4)%Z).
  { unfold B. rewrite lv_zero. replace ([D2] ++ repeat Dm p ++ [D1; D1] ++ repeat D2 (R - 2) ++ [D3])
      with (gw ((LrO p ++ [D1]) ++ [D1]) R) by (rewrite gw_eq; unfold LrO; rewrite <- !app_assoc; reflexivity).
    rewrite lv_gw, lv_LrO by lia.
    assert (E: (4 * 4 ^ Z.of_nat (R - 1) = W)%Z) by (unfold W; replace R with (S (R - 1)) at 2 by lia; rewrite pow4_S; ring).
    fold A4. rewrite <- E. ring. }
  assert (EC: lv (([D1; D1] ++ repeat D2 (R - 1)) ++ [D3]) = (33 * W + 1)%Z).
  { rewrite <- app_assoc, lv_X2s3. replace (S (R - 1)) with R by lia. fold W. change (lv [D1; D1]) with 31%Z. ring. }
  assert (E2: (4 ^ Z.of_nat (S (length B)) = 64 * A4 * W)%Z).
  { rewrite LB. replace (S (R + p + 2)) with (p + (R + 3)) by lia. rewrite !pow4_add. unfold A4, W. change (4 ^ Z.of_nat 3)%Z with 64%Z. ring. }
  assert (E2': (4 ^ Z.of_nat (R + p + 2) = 16 * A4 * W)%Z).
  { replace (R + p + 2) with (p + (R + 2)) by lia. rewrite !pow4_add. unfold A4, W. change (4 ^ Z.of_nat 2)%Z with 16%Z. ring. }
  assert (HQ: count3 (zm (R - 1) ++ [D0]) = O) by (rewrite count3_app, count3_zm; reflexivity).
  destruct (xstep (zm (R - 1) ++ [D0]) Dm B D0 ([D1; D1] ++ repeat D2 (R - 1)) D3 (4 ^ (R + p + 2) - 1) l0 tail HQ
    ltac:(left; reflexivity) ltac:(unfold B; apply inv_O) ltac:(discriminate) ltac:(lia)) as [Rm [Sm Cm]].
  { apply Forall_app. split; [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto | apply pos012_repeat2]. }
  { discriminate. }
  { rewrite length_app, repeat_length, LB. cbn [length]. lia. }
  { rewrite EB, E2. assert (AW: (W <= A4 * W)%Z) by (clear -HA HW; nia). lia. }
  { rewrite EC, EB, E2, pow4_nat, E2'. ring. }
  { rewrite EC, LB. lia. }
  { rewrite EC, E2. assert (AW: (W <= A4 * W)%Z) by (clear -HA HW; nia). lia. }
  exists Rm. split; cycle 1.
  { rewrite LB, length_app, repeat_length in Cm. cbn [length] in Cm. unfold B in Cm. unfold LrO.
    cz Cm. czg. lia. }
  follow recT_absorb.
  replace ((zm R ++ LrO p ++ [D1; D1] ++ repeat D2 (R - 2)) ++ [D3]) with ((zm (R - 1) ++ [D0]) ++ [Dm] ++ B)
    by (unfold B, LrO; replace (zm R) with (zm (R - 1) ++ [D0; Dm]) by (rewrite zm_snoc; f_equal; lia); rewrite <- !app_assoc; reflexivity).
  follow Sm. cbn [sc]. rewrite LB, length_app, repeat_length. cbn [length]. replace (R + p + 2 - (2 + (R - 1))) with (S p) by lia.
  rewrite <- !app_assoc. finish.
Qed.

Lemma s3_Oeven t R l0 rest: 1 <= t -> R >= 2 * t + 11 -> (Z.of_nat (2 * R + 2 * t + 1) <= 36 * 4 ^ Z.of_nat (2 * t))%Z ->
  S3run l0 (repeat Dm (2 * R) ++ LrO (2 * t) ++ [D2]) (2 * R + 2 * t + 1)
    ((zm (R - 1) ++ [D0; D0; Dm; Dm] ++ zm (t - 1) ++ [D0] ++ [D2; Dm; Dm]) ++ zm (R + t - 3) ++ [D0]) rest.
Proof.
  intros Ht HR HN. set (p := 2 * t) in *. set (N := 2 * R + p + 1) in *.
  assert (LZ: length (LrO p ++ [D2]) = p + 2) by (unfold LrO; rewrite !length_app, repeat_length; cbn [length]; lia).
  assert (HlX: length (LrO p ++ [D1]) = length (LrO p ++ [D2])) by (rewrite !length_app; reflexivity).
  pose proof (lv_LrO p) as EL. set (A4 := (4 ^ Z.of_nat p)%Z) in *. assert (HA: (1 <= A4)%Z) by apply pow4_ge1.
  assert (EX2: lv ((LrO p ++ [D1]) ++ [D2]) = (144 * A4 + 34)%Z) by (rewrite !lv_snoc, EL; cbn [dv]; ring).
  assert (EG2: lv (gw ((LrO p ++ [D1]) ++ [D1]) 2) = (576 * A4 + 133)%Z)
    by (rewrite lv_gw, EL by lia; change (4 ^ Z.of_nat (2 - 1))%Z with 4%Z; ring).
  assert (PN: (4 ^ Z.of_nat (p + 6) <= 4 ^ Z.of_nat (N - 1))%Z) by (apply pow4_mono; unfold N, p; lia).
  rewrite pow4_add in PN. fold A4 in PN. change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  replace (R + t - 3) with (R + t - 1 - 2) by lia.
  apply (s3_skel (2 * R) (LrO p ++ [D2]) (LrO p ++ [D1]) N (R - 1) (R + t - 1) (zm (R - 1) ++ [D0; D0; Dm; Dm] ++ zm (t - 1) ++ [D0] ++ [D2; Dm; Dm]) l0 rest); s3t.
  - apply inv_restart; [lia | apply scan_LrO].
  - rewrite <- !app_assoc, scan_app. unfold LrO. cbn [app scan]. replace (scan false (repeat Dm p)) with (Some true)
      by (unfold p; replace (2 * t) with (S (2 * t - 1)) by lia; cbn [repeat scan]; symmetry; apply scan_dms1). reflexivity.
  - intros B d l0' tail HI Hd Hl Hv. unfold N, p in Hl. clear LZ HlX EL EX2 EG2 PN HN.
    replace (N - (R - 1) + 1) with (R + 2 * t + 3) by (unfold N, p; lia).
    replace (R + 2 * t + 3 - (R + t - 1)) with (t + 4) by lia.
    assert (CL: length (SG (R + 2 * t + 3) (t + 4)) = 6 + 2 * (4 ^ (R + 2 * t + 3) - 1) + (6 + 2 * (4 ^ (R + 2 * t + 2) - 1) +
        (length (SG (2 * (t - 1) + (R - 1) + 4) (S (t - 1))) + length (SG (R + t - 1 + 2) 2)))).
    { replace (t + 4) with (S (S (S (t - 1) + 2))) by lia. rewrite SG_len, SG_len, SG_split_len.
      replace (pred (R + 2 * t + 3)) with (R + 2 * t + 2) by lia. replace (pred (R + 2 * t + 2)) with (2 * (t - 1) + (R - 1) + 4) by lia.
      replace (2 * (t - 1) + (R - 1) + 4 - S (t - 1)) with (R + t - 1 + 2) by lia. lia. }
    replace (t + 4) with (S (S (t + 2))) by lia. rewrite !SG_S. cbn [pred].
    replace (R + 2 * t + 3 - 1 - 1) with (R + 2 * t + 1) by lia. replace (R + 2 * t + 3 - 1) with (R + 2 * t + 2) by lia.
    rewrite SG_split.
    destruct (conv [] D2 (2 * t) (R - 1) 1 (R + 2 * t + 3) B d l0' ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 2 * t + 2) - 1)) *> SG (R + 2 * t + 1) t *>
      SG (R + 2 * t + 1 - t) 2 *> tail) (or_intror (conj eq_refl eq_refl))
      ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
    assert (EW: zm (R - 1) ++ [D0] ++ repeat Dm 1 ++ [] ++ [D2] ++ repeat Dm (2 * t) ++ [D1; D1] ++ repeat D2 (R - 1 - 1) =
      zm R ++ LrO (2 * t) ++ [D1; D1] ++ repeat D2 (R - 2)) by (rewrite (zm_pred R), <- app_assoc by lia;
      replace (R - 1 - 1) with (R - 2) by lia; reflexivity). rewrite EW in S1, C1.
    destruct (oe_a (2 * t) R (l0' <* [1]^^R1) (SG (R + 2 * t + 1) t *> SG (R + 2 * t + 1 - t) 2 *> tail) ltac:(lia)) as [R2 [S2 C2]].
    assert (HQ0: count3 (zm (R - 1) ++ [D0; D0; Dm; Dm]) = O) by (rewrite count3_app, count3_zm; reflexivity).
    destruct (tinner (zm (R - 1) ++ [D0; D0; Dm; Dm]) HQ0 (t - 1) 0 (R - 1) (l0' <* [1]^^R1 <* [1]^^R2) (SG (R + 2 * t + 1 - t) 2 *> tail)) as [R3 [S3 C3]].
    { pose proof (pow4_ge (S (R - 1))). lia. }
    assert (HQ1: count3 ((zm (R - 1) ++ [D0; D0; Dm; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) = O) by (rewrite !count3_app, !count3_zm; reflexivity).
    destruct (ttail ((zm (R - 1) ++ [D0; D0; Dm; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) D1 (R + t - 1) (l0' <* [1]^^R1 <* [1]^^R2 <* [1]^^R3) tail HQ1
      ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
    exists (R4 + (R3 + (R2 + R1))). split; cycle 1.
    { replace (S (S (t + 2))) with (t + 4) by lia. rewrite CL. cz C1. cz C2. cz C3. cz C4. czg. lia. }
    follow S1. follow S2.
    replace (zm (R - 1) ++ [D0; D0] ++ repeat Dm (S (2 * t)) ++ [D1; D1] ++ repeat D2 (R - 1))
      with ((zm (R - 1) ++ [D0; D0; Dm; Dm]) ++ zm 0 ++ repeat Dm (2 * (t - 1) + 1) ++ [D1; D1] ++ repeat D2 (R - 1))
      by (replace (S (2 * t)) with (S (S (2 * (t - 1) + 1))) by lia; cbn [repeat]; rewrite <- !app_assoc; reflexivity).
    replace (S (t - 1)) with t in S3 by lia. replace (2 * (t - 1) + (R - 1) + 4) with (R + 2 * t + 1) in S3 by lia.
    follow S3. replace (R - 1 + t) with (R + t - 1) by lia.
    replace ((zm (R - 1) ++ [D0; D0; Dm; Dm]) ++ zm (0 + (t - 1)) ++ [D0] ++ [D1; D1] ++ repeat D2 (R + t - 1))
      with (((zm (R - 1) ++ [D0; D0; Dm; Dm]) ++ zm (0 + (t - 1)) ++ [D0]) ++ [D1] ++ [D1] ++ repeat D2 (R + t - 1)) by (rewrite <- !app_assoc; reflexivity).
    replace (R + 2 * t + 1 - t) with (R + t - 1 + 2) by lia.
    follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app Nat.add]. finish.
Qed.
Lemma s3_Oeven0 R l0 rest: R >= 11 -> R <= 58 ->
  S3run l0 (repeat Dm (2 * R) ++ LrO 0 ++ [D2]) (2 * R + 1)
    ((zm (R - 1) ++ [D0; D0; Dm; D2; Dm; Dm]) ++ zm (R - 3) ++ [D0]) rest.
Proof.
  intros HR HR2. set (Nn := 2 * R + 1) in *.
  assert (PN: (4 ^ Z.of_nat 6 <= 4 ^ Z.of_nat (Nn - 1))%Z) by (apply pow4_mono; unfold Nn; lia).
  change (4 ^ Z.of_nat 6)%Z with 4096%Z in PN.
  replace (R - 3) with (R - 1 - 2) by lia.
  apply (s3_skel (2 * R) (LrO 0 ++ [D2]) (LrO 0 ++ [D1]) Nn (R - 1) (R - 1) (zm (R - 1) ++ [D0; D0; Dm; D2; Dm; Dm]) l0 rest).
  11: change (lv ((LrO 0 ++ [D1]) ++ [D2])) with 178%Z; assert (Nn <= 117) by (unfold Nn; lia); lia.
  10: change (lv (gw ((LrO 0 ++ [D1]) ++ [D1]) 2)) with 709%Z; unfold Nn; lia.
  5: apply inv_restart; [lia | reflexivity].
  1-11: s3t; first [reflexivity | cbn; lia | unfold Nn; lia | cbn; unfold Nn; lia].
  intros B d l0' tail HI Hd Hl Hv. unfold Nn in Hl. replace (Nn - (R - 1) + 1) with (R + 3) by (unfold Nn; lia). replace (R + 3 - (R - 1)) with 4 by lia.
  assert (CL: length (SG (R + 3) 4) = 6 + 2 * (4 ^ (R + 3) - 1) + (6 + 2 * (4 ^ (R + 0 + 2) - 1) + length (SG (R - 1 + 2) 2))).
  { rewrite SG_len, SG_len. replace (pred (R + 3)) with (R + 0 + 2) by lia. replace (pred (R + 0 + 2)) with (R - 1 + 2) by lia. lia. } rewrite SG_S, SG_S. cbn [pred]. replace (R + 3 - 1 - 1) with (R - 1 + 2) by lia. replace (R + 3 - 1) with (R + 0 + 2) by lia.
  destruct (conv [] D2 0 (R - 1) 1 (R + 3) B d l0' ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ (R + 0 + 2) - 1)) *> SG (R - 1 + 2) 2 *> tail) (or_intror (conj eq_refl eq_refl))
    ltac:(lia) ltac:(lia) HI Hd ltac:(cbn [length]; lia) ltac:(lia) Hv) as [R1 [S1 C1]].
  assert (EW: zm (R - 1) ++ [D0] ++ repeat Dm 1 ++ [] ++ [D2] ++ repeat Dm 0 ++ [D1; D1] ++ repeat D2 (R - 1 - 1) =
    zm R ++ LrO 0 ++ [D1; D1] ++ repeat D2 (R - 2)) by (rewrite (zm_pred R), <- app_assoc by lia;
    replace (R - 1 - 1) with (R - 2) by lia; reflexivity). rewrite EW in S1, C1.
  destruct (oe_a 0 R (l0' <* [1]^^R1) (SG (R - 1 + 2) 2 *> tail) ltac:(lia)) as [R2 [S2 C2]].
  assert (HQ: count3 (zm (R - 1) ++ [D0; D0; Dm]) = O) by (rewrite count3_app, count3_zm; reflexivity).
  destruct (ttail (zm (R - 1) ++ [D0; D0; Dm]) D1 (R - 1) (l0' <* [1]^^R1 <* [1]^^R2) tail HQ ltac:(right; right; reflexivity) ltac:(lia)) as [R4 [S4 C4]].
  exists (R4 + (R2 + R1)). split; cycle 1.
  { rewrite CL. cz C1. cz C2. cz C4. czg. lia. }
  follow S1. follow S2.
  replace (zm (R - 1) ++ [D0; D0] ++ repeat Dm 1 ++ [D1; D1] ++ repeat D2 (R - 1)) with ((zm (R - 1) ++ [D0; D0; Dm]) ++ [D1] ++ [D1] ++ repeat D2 (R - 1))
    by (cbn [repeat]; rewrite <- !app_assoc; reflexivity).
  follow S4. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app]. finish.
Qed.

Lemma s3_17 l0 rest:
  S3run l0 (repeat Dm 14 ++ [D1; D0]) 15 ((zm 7 ++ [D2; D0; Dm; Dm]) ++ zm 4 ++ [D0]) rest.
Proof.
  replace (zm 4) with (zm (6 - 2)) by reflexivity.
  apply (s3_skel 14 [D1; D0] [D1; Dm] 15 6 6 (zm 7 ++ [D2; D0; Dm; Dm]) l0 rest).
  1-14: s3t; first [reflexivity | cbn; lia | vm_compute; reflexivity | vm_compute; discriminate].
  intros B d l0' tail HI Hd Hl Hv. cbn [Nat.sub] in Hl. change (SG (15 - 6 + 1) (15 - 6 + 1 - 6)) with (SG 10 4).
  change (lv (gw ([D1; Dm] ++ [D1]) 6)) with 107521%Z in Hv.
  destruct (pa_conv B d HI) as [B4 [E4 [HI4 [Hl4 Hv4]]]]; [rewrite Hv, Hl; vm_compute; discriminate|].
  rewrite Hv in Hv4.
  destruct (xpat_auto (zm 6) Dm B4 D0 1 [] D1 1 ([D1] ++ repeat D2 5) D3 l0'
    ([1;1;1;1;1;1] *> [0]^^(2 * (4 ^ 9 - 1)) *> SG 8 2 *> tail) (count3_zm 6)
    ltac:(left; reflexivity) HI4 ltac:(discriminate) ltac:(lia) ltac:(constructor) ltac:(left; reflexivity)
    ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto) ltac:(discriminate) ltac:(lia) ltac:(cbn; lia)) as [R1 [S1 C1]];
    [rewrite Hl4, Hl; reflexivity | rewrite Hv4; reflexivity | rewrite Hv4, Hl4, Hl; vm_compute; discriminate
    | rewrite Hl4, Hl; vm_compute; discriminate | vm_compute; discriminate |].
  set (B5 := [Dm; D1] ++ repeat D2 5 ++ [D3]).
  destruct (xstep_auto (zm 7) D1 B5 D0 ([D1] ++ repeat D2 6) D3 (l0' <* [1]^^R1) (SG 8 2 *> tail) (count3_zm 7)
    ltac:(right; right; reflexivity) ltac:(unfold B5; vm_compute; discriminate) ltac:(discriminate) ltac:(cbn; lia)) as [R2 [S2 C2]];
    [repeat apply Forall_cons; try apply Forall_nil; unfold pos012; auto | discriminate | cbn; lia | reflexivity | vm_compute; discriminate
    | vm_compute; discriminate |].
  assert (HQ: count3 (zm 7 ++ [D2]) = O) by reflexivity.
  destruct (ttail (zm 7 ++ [D2]) Dm 6 (l0' <* [1]^^R1 <* [1]^^R2) tail HQ ltac:(left; reflexivity) ltac:(lia)) as [R3 [S3 C3]].
  exists (R3 + (R2 + R1)). split; cycle 1.
  { assert (EC4: cls (B ++ [d]) = cls (Dm :: B4)) by (rewrite E4; reflexivity).
    assert (CL: length (SG 10 4) = 6 + 2 * (4 ^ 10 - 1) + (6 + 2 * (4 ^ 9 - 1) + length (SG 8 2))) by (rewrite SG_len, SG_len; reflexivity).
    rewrite CL. replace (length B4) with 9 in C1 by (rewrite Hl4, Hl; reflexivity). unfold B5 in C2. cbn [length app repeat] in C2.
    change (6 + 2) with 8 in C3. cz C1. cz C2. cz C3. cz EC4. czg. clear - C1 C2 C3 EC4. lia. } rewrite SG_S. cbn [pred]. rewrite SG_S. cbn [pred].
  follow recT_absorb. rewrite <- app_assoc, E4. rewrite Hl4, Hl in S1.
  follow S1. cbn [sc]. follow recT_absorb.
  replace ((zm 6 ++ [D0] ++ repeat Dm 1 ++ [] ++ [D1] ++ repeat Dm 1 ++ [D1] ++ repeat D2 5) ++ [D3]) with (zm 7 ++ [D1] ++ B5)
    by (unfold B5; change (zm 7) with (zm 6 ++ [D0; Dm]); rewrite <- !app_assoc; reflexivity).
  follow S2. cbn [sc]. replace (length B5 - length ([D1] ++ repeat D2 6)) with 1%nat by reflexivity.
  replace (zm 7 ++ [D2] ++ repeat Dm 1 ++ [D1] ++ repeat D2 6) with ((zm 7 ++ [D2]) ++ [Dm] ++ [D1] ++ repeat D2 6)
    by (rewrite <- !app_assoc; reflexivity).
  follow S3. cbn [sc]. rewrite !ones_sides. rewrite <- !app_assoc. cbn [app]. finish.
Qed.

Notation Glued K l0 ws N x W1 T := (exists Rt, lstack (D2 :: rev ws) (base (TDig D2) l0) <* [0;0] <* [0;1;1;1]
    <{{SA}} [0;0;0] *> S3B (K N x) *> [0;0;0;0;0;0] *> [1;1;1;1;1;1] *> [1;1;1;1;1;1] *> T -->*
  RecT (l0 <* [1]^^Rt) TLone (W1 ++ [Dm;Dm;D3;Dm;D3;D0]) D0 T /\
  Rt + cls ((W1 ++ [Dm;Dm;D3;Dm;D3;D0]) ++ [D0]) = cls (ws ++ [D2]) + length (S3B (K N x)) + 28).

Section Glue.
Variable K : nat -> nat -> list nat.
Hypothesis K1 : forall x, K 1%nat x = [x + 12].
Hypothesis KS : forall N x, 1 <= N -> K (S N) x = K N (2 * 4 ^ S N - 3 * S N - 8) ++ [x + 3 * S N + 9].

Lemma S3B_app l1 l2: S3B (l1 ++ l2) = S3B l2 ++ S3B l1.
Proof. induction l1 as [|k l1 IH]; cbn [app S3B]; [rewrite app_nil_r; reflexivity | rewrite IH, <- app_assoc; reflexivity]. Qed.
Lemma S3B_len N x: 1 <= N -> length (S3B (K N x)) + 6 = x + 3 * N + 9 + length (SG N N).
Proof.
  revert x. induction N as [|N IH]; intros x HN; [lia|].
  destruct N as [|N].
  - rewrite K1. cbn [S3B app]. rewrite length_app, lz_len. cbn [length]. rewrite SG11. lia.
  - rewrite KS by lia. rewrite S3B_app, length_app. cbn [S3B app]. rewrite length_app, lz_len. cbn [length].
    rewrite (SG_len (S (S N)) (S N)). cbn [pred].
    specialize (IH (2 * 4 ^ S (S N) - 3 * S (S N) - 8) ltac:(lia)).
    assert (4 * S N + 8 <= 4 ^ S (S N)) by (clear; induction N; cbn in *; lia). lia.
Qed.

Lemma glue ws W' N x W1 l0 T: toks (W' ++ [Dm]) = 2 :: toks ws ++ [3] -> count3 W' = O -> 1 <= N ->
  x + 3 * N + 3 = 2 * (4 ^ S N - 4) ->
  S3run (l0 <* [1]^^9) (W' ++ [D2]) N W1 T ->
  Glued K l0 ws N x W1 T.
Proof.
  intros Ht H3 HN Hx [Rt [S3 C3]]. pose proof (S3B_len N x HN) as LS. pose proof (cls_lone _ _ Ht) as EC.
  exists (Rt + 9). split.
  - change ([0;0;0;0;0;0] *> ?R) with ([0]^^6 *> R). rewrite (S3B_SG K K1 KS N x _ HN).
    replace (x + 3 * N + 9) with (6 + (x + 3 * N + 3)) by lia. rewrite zeros_split, Hx, (lone_reading ws (W' ++ [Dm]) l0 Ht).
    change (?X <* [0;1;1;1] <{{SA}} [0;0;0] *> [0]^^6 *> ?R) with (X <* [1;1;1] {{SA}}> [0]^^10 *> R).
    follow (fun R => restart W' l0 R H3). follow S3. rewrite ones_sides. finish.
  - rewrite !cls_app in *. cbn [cls cl] in *. lia.
Qed.

Lemma glue_17 l0 x T: x + 3 * 15 + 3 = 2 * (4 ^ S 15 - 4) ->
  Glued K l0 (repeat D2 14 ++ [Dm] ++ repeat D2 0) 15 x ((zm 7 ++ [D2; D0; Dm; Dm]) ++ zm 4 ++ [D0]) T.
Proof.
  intros Hx. destruct (s3_17 (l0 <* [1]^^9) T) as [Rt [S3 C3]].
  pose proof (S3B_len (15) x ltac:(lia)) as LS.
  exists (Rt + 9). split; cycle 1.
  { try unfold LrE in C3; try unfold LrO in C3. cz C3. czg. set (P := 4 ^ S 15) in *. clearbody P. lia. }
  change ([0;0;0;0;0;0] *> ?R) with ([0]^^6 *> R). rewrite (S3B_SG K K1 KS 15 x _ ltac:(lia)).
  replace (x + 3 * 15 + 9) with (6 + (x + 3 * 15 + 3)) by lia. rewrite zeros_split, Hx.
  rewrite (lone_reading (repeat D2 14 ++ [Dm] ++ repeat D2 0) (repeat Dm 14 ++ [D0; D1]) l0 (lr_even 14 0)).
  change (?X <* [0;1;1;1] <{{SA}} [0;0;0] *> [0]^^6 *> ?R) with (X <* [1;1;1] {{SA}}> [0]^^10 *> R).
  follow (fun R => restart17 (repeat Dm 14) l0 R (count3_repeatm 14)). follow S3. rewrite ones_sides. finish.
Qed.
End Glue.

Lemma ones4 (l : side) a b c d: l <* [1]^^a <* [1]^^b <* [1]^^c <* [1]^^d = l <* [1]^^(a + b + c + d).
Proof. rewrite !ones_join. f_equal. f_equal. lia. Qed.
Lemma KS1 x: KS 1 x = [x + 12].
Proof. reflexivity. Qed.
Lemma KSs N x: 1 <= N -> KS (S N) x = KS N (2 * 4 ^ S N - 3 * S N - 8) ++ [x + 3 * S N + 9].
Proof. intros H. destruct N as [|N]; [lia | reflexivity]. Qed.
Lemma KS_nn N x: 1 <= N -> KS N x <> [].
Proof. intros H. destruct N as [|[|N]]; [lia | discriminate | cbn [KS]; apply app_cons_nn]. Qed.
Lemma SG_Z2 N: 1 <= N -> length (SG N N) + 4 = Z2 N + 4 * N.
Proof.
  induction N as [|N IH]; intros HN; [lia|]. destruct N as [|N]; [rewrite SG11; reflexivity|].
  rewrite SG_len. cbn [pred]. specialize (IH ltac:(lia)). change (Z2 (S (S N))) with (2 * 4 ^ S (S N) + Z2 (S N)).
  pose proof (pow4_pos (S (S N))). lia.
Qed.

Definition LevD (m E : nat) (W : list dg) (d : dg) (N R : nat) : Prop :=
  Inv W d /\ d <> Dm /\ sv false (W ++ [d]) = true /\ length W = m - 2 /\
  (3 * wv (W ++ [d]) <= 4 ^ Z.of_nat (m - 1))%Z /\ R + 10 + cls (W ++ [d]) = N + E /\
  forall r, 0inf {{A}}> [0]^^N *> r -->* RecT (0inf <* [1]^^R) (TDig D2) W d r.

Notation Next m E W d N R := (exists W' N' R', LevD m E W' ML N' R' /\
  forall r, RecT (0inf <* [1]^^R) (TDig D2) W d ([0]^^(N' - N) *> r) -[tm]->+ RecT (0inf <* [1]^^R') (TDig D2) W' ML r).

Section Step.
Variables (m E q I c ex k2 : nat) (REM : list Sym) (D WX W1 : list dg) (dl : dg).
Hypothesis Hm3: 3 * E = 8 * m + 5.
Hypothesis Hq: 3 * q + 1 = 2 * m.
Hypothesis Hm: 17 <= m.
Hypothesis Hc: c = 3 * m - 1.
Hypothesis HF: forall l n r, RecT (l <* [1]^^n) (TDig D2) (repeat D2 (m - 2)) D1 ([0]^^(2 * I) *> r) -->*
  l <{{SA}} [0]^^(n + c) *> OVT *> REM *> r.
Hypothesis HS1: forall l0 r, RecT l0 (TDig D2) WX D2 ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> REM *> r) -->*
  RecT (S2L l0 (TDig D2) WX D2 <* [1]^^ex) TLone D dl r.
Hypothesis HWXv: (3 * wv (WX ++ [D2]) = 2 * 4 ^ Z.of_nat (m - 1) - 2 * Z.of_nat m - 4)%Z.
Hypothesis HC: forall W d k l0 r, Inv W d -> d <> Dm -> sv false (W ++ [d]) = true -> length W = m - 2 ->
  (wv (W ++ [d]) + Z.of_nat k = wv (WX ++ [D2]))%Z ->
  exists NX, RecT l0 (TDig D2) W d ([0]^^(2 * k) *> r) -->* RecT (l0 <* [1]^^NX) (TDig D2) WX D2 r /\
    NX + cls (WX ++ [D2]) = cls (W ++ [d]) + 2 * k.
Hypothesis HDl: length D = m - 2.
Hypothesis HDI: Inv D dl.
Hypothesis Hdl: dl <> Dm.
Hypothesis Hk2: (3 * (wv (D ++ [dl]) + Z.of_nat k2) = 2 * 4 ^ Z.of_nat (S (m - 2)) - 5)%Z.
Hypothesis HP: cls (D ++ [dl]) + ex = 2 * I + 4 * m - 11.
Hypothesis HxZ: (3 * (Z.of_nat (cls (D ++ [dl])) + Z.of_nat ex) - 6 * wv (D ++ [dl]) =
  2 * 4 ^ Z.of_nat (S (m - 2)) + 12 * Z.of_nat (m - 2) + 1)%Z.
Hypothesis HG: forall l0 x T, x + 3 * (m - 2) + 3 = 2 * (4 ^ S (m - 2) - 4) ->
  Glued KS l0 WX (m - 2) x W1 T.
Hypothesis HW1: count3 W1 = O.
Hypothesis HW1h: exists W1', W1 = D0 :: Dm :: W1'.
Hypothesis HW1l: length W1 = 2 * m - 7.

Lemma step W d N R: LevD m E W d N R -> Next (2 * m + 1) (2 * E + 1) W d N R.
Proof.
  intros [HI [Hd [Hsv [Hl [Hv [HE Hrun]]]]]]. pose proof MF as [merge_cells [MT_3free [ML_ne [MT_len [MT_inv SA_C]]]]].
  assert (Hdt: dtop (TDig D2)) by (left; reflexivity). assert (Hdl': dtop TLone) by (right; reflexivity).
  assert (P1: (6 * Z.of_nat (m - 3) + 13 <= 4 ^ Z.of_nat (S (S (m - 3))))%Z) by apply pow4_lin.
  replace (S (S (m - 3))) with (m - 1) in P1 by lia.
  destruct (count_to_top W d) as [k1 Hk1]; [rewrite Hl; replace (S (m - 2)) with (m - 1) by lia; lia|].
  rewrite Hl in Hk1. replace (S (m - 2)) with (m - 1) in Hk1 by lia.
  assert (Hk1q: q + 2 <= k1) by lia.
  assert (Hx: cls (D ++ [dl]) + 2 * k2 + ex = 2 * (4 ^ S (m - 2) - 4) + 4 * (m - 2) + 5).
  { assert (PZ: Z.of_nat (4 ^ S (m - 2)) = (4 ^ Z.of_nat (S (m - 2)))%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
    assert (P4: (4 <= 4 ^ Z.of_nat (S (m - 2)))%Z) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; pose proof (pow4_ge1 (m - 2)); lia).
    lia. }
  set (kX := k1 - q).
  assert (HkX: 2 * kX + 1 + 4 * m = E + 2 * k1) by (unfold kX; lia).
  assert (HvX: (wv (W ++ [d]) + Z.of_nat kX = wv (WX ++ [D2]))%Z) by (unfold kX; lia).
  assert (Hk1': (3 * (wv (W ++ [d]) + Z.of_nat k1) = 2 * 4 ^ Z.of_nat (S (length W)) - 5)%Z)
    by (rewrite Hl; replace (S (m - 2)) with (m - 1) by lia; exact Hk1).
  assert (Hk2': (3 * (wv (D ++ [dl]) + Z.of_nat k2) = 2 * 4 ^ Z.of_nat (S (length D)) - 5)%Z) by (rewrite HDl; exact Hk2).
  destruct (count_maxQ (TDig D2) [] Hdt eq_refl k1 W d 0inf HI Hd Hk1') as [Nc [_ C1]].
  destruct (HC W d kX 0inf 0inf HI Hd Hsv Hl HvX) as [NX [_ CX]].
  destruct (count_maxQ TLone [] Hdl' eq_refl k2 D dl 0inf HDI Hdl Hk2') as [Nc2 [_ C2]].
  rewrite Hl, (cls_app (repeat D2 (m - 2)) [D1]), cls_rep2 in C1. rewrite HDl, (cls_app (repeat D2 (m - 2)) [D1]), cls_rep2 in C2.
  cbn [cls cl] in C1, C2.
  set (x := Nc2 + ex).
  assert (Hxx: x + 3 * (m - 2) + 3 = 2 * (4 ^ S (m - 2) - 4)) by (unfold x; lia).
  destruct (HG 0inf x 0inf Hxx) as [Rt [_ CG]].
  pose proof (S3B_len KS KS1 KSs (m - 2) x ltac:(lia)) as LS. pose proof (SG_Z2 (m - 2) ltac:(lia)) as LZ.
  destruct HW1h as [W1' EW1].
  set (REP := REPof W1).
  destruct (REP_ok D0 (Dm :: W1')) as [Htok [Hne H3]]; [rewrite <- EW1; exact HW1 | reflexivity |].
  rewrite <- EW1 in Htok, Hne, H3. fold REP in Htok, Hne, H3.
  destruct (cls_rep REP W1 Htok) as [ER LR].
  set (Mz := 2 * k1 + 2 * I + 2 * k2 + Z2 (m - 2) + 7 + MZ).
  assert (Hrec: forall r, RecT (0inf <* [1]^^R) (TDig D2) W d ([0]^^Mz *> r) -[tm]->+
      RecT (0inf <* [1]^^(R + NX + Rt + MR)) (TDig D2) (REP ++ MT) ML r).
  { intros r. unfold Mz. rewrite !zeros_split.
    set (r1 := [0]^^(2 * k2) *> [0]^^(Z2 (m - 2)) *> [0]^^7 *> [0]^^MZ *> r).
    destruct (count_maxQ (TDig D2) [] Hdt eq_refl k1 W d (0inf <* [1]^^R) HI Hd Hk1') as [Nc' [S1 C1']].
    rewrite Hl, (cls_app (repeat D2 (m - 2)) [D1]), cls_rep2 in C1'. cbn [cls cl] in C1'. assert (Nc' = Nc) by lia. subst Nc'.
    rewrite Hl in S1.
    assert (Ho: RecT (0inf <* [1]^^R) (TDig D2) W d ([0]^^(2 * k1) *> [0]^^(2 * I) *> r1) -[tm]->+
        0inf <{{SA}} [0]^^(Nc + R + c) *> OVT *> REM *> r1).
    { apply ev_prog; [|unfold RecT; cbn; intros E0; apply SA_C; symmetry; exact E0].
      follow S1. rewrite ones_sides. apply HF. }
    apply (progress_evstep_trans _ _ _ _ Ho). clear Ho.
    replace (Nc + R + c) with (S (Nc + R + c - 1)) by lia.
    follow (replay (fun r => RecT (0inf <* [1]^^R) (TDig D2) W d r) N Hrun (Nc + R + c - 1) (OVT *> REM *> r1) ltac:(lia)). cbv beta.
    change (OVT *> REM *> r1) with ([0;0;0;0] *> [1;1;1;1;1;1;1;0;1;1;1] *> REM *> r1).
    rewrite (zeros_shift (S (S (Nc + R + c - 1)) - N) (2 * kX)) by lia.
    destruct (HC W d kX (0inf <* [1]^^R) ([0] *> [1;1;1;1;1;1;1;0;1;1;1] *> REM *> r1) HI Hd Hsv Hl HvX) as [NX' [SX CX']].
    assert (NX' = NX) by lia. subst NX'. follow SX.
    follow (HS1 (0inf <* [1]^^R <* [1]^^NX) r1). unfold r1.
    destruct (count_maxQ TLone [] Hdl' eq_refl k2 D dl (S2L (0inf <* [1]^^R <* [1]^^NX) (TDig D2) WX D2 <* [1]^^ex)
      HDI Hdl Hk2') as [Nc2' [S2 C2']].
    rewrite HDl, (cls_app (repeat D2 (m - 2)) [D1]), cls_rep2 in C2'. cbn [cls cl] in C2'. assert (Nc2' = Nc2) by lia. subst Nc2'.
    follow S2. rewrite HDl. unfold S2L. rewrite ones_sides.
    set (l0X := 0inf <* [1]^^R <* [1]^^NX).
    set (lS := lstack (D2 :: rev WX) (base (TDig D2) l0X) <* [0;0] <* [0;1;1;1]).
    change (lstack (D2 :: rev WX) (base (TDig D2) l0X) <* [0;0] <* [1;1;0;1;1;1]) with (lS <* [1;1]).
    follow (s2_run (m - 2) ltac:(lia) lS (Nc2 + ex) ([0]^^7 *> [0]^^MZ *> r)). fold x.
    destruct (KS (m - 2) x) as [|k ks] eqn:EK; [exfalso; exact (KS_nn (m - 2) x ltac:(lia) EK)|].
    change ([0]^^7 *> [0]^^MZ *> r) with ([0;0;0;0;0;0;0] *> [0]^^MZ *> r).
    follow (s2end k ks lS ([0]^^MZ *> r)).
    rewrite Str_app_assoc. change ([1;1;1;1;1;1;1;1;1;1;1;1] *> ?X) with ([1;1;1;1;1;1] *> [1;1;1;1;1;1] *> X).
    destruct (HG l0X x (EXT1 *> [0]^^MZ *> r) Hxx) as [Rt' [SG' CG']].
    assert (Rt' = Rt) by (clear - CG CG' EK; rewrite ?EK in CG; rewrite ?EK in CG'; lia). subst Rt'.
    rewrite EK in SG'. follow SG'.
    follow (merge REP W1 (l0X <* [1]^^Rt) r Hne H3 Htok).
    unfold l0X. rewrite ones4. finish. }
  assert (Ex: x = Nc2 + ex) by reflexivity. assert (EMz: Mz = 2 * k1 + 2 * I + 2 * k2 + Z2 (m - 2) + 7 + MZ) by reflexivity.
  assert (ER0: REP = D0 :: repair 3 W1') by (unfold REP; rewrite EW1; reflexivity).
  exists (REP ++ MT), (N + Mz), (R + NX + Rt + MR). split.
  - repeat split.
    + unfold Inv. destruct (scan_3free false REP H3) as [s' Es]. rewrite <- app_assoc. apply (ok_app_r _ _ _ _ Es). apply MT_inv.
    + exact ML_ne.
    + apply sv_3free. rewrite <- app_assoc, count3_app, H3, MT_3free. reflexivity.
    + rewrite length_app, MT_len, LR, HW1l. lia.
    + assert (Lr: length ((repair 3 W1' ++ MT) ++ [ML]) = 2 * m - 1).
      { assert (L0: length REP = S (length (repair 3 W1'))) by (rewrite ER0; reflexivity).
        rewrite !length_app, MT_len. cbn [length]. lia. }
      rewrite ER0. change ((D0 :: repair 3 W1') ++ MT) with (D0 :: (repair 3 W1' ++ MT)). cbn [app]. rewrite wv_cons. cbn [dv].
      pose proof (wv_le3 ((repair 3 W1' ++ MT) ++ [ML])) as U. rewrite Lr in U.
      replace (2 * m + 1 - 1) with (S (2 * m - 1)) by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
    + rewrite (cls_app (REP ++ MT) [ML]), (cls_app REP MT). cbn [cls].
      rewrite (cls_app (W1 ++ [Dm;Dm;D3;Dm;D3;D0]) [D0]), (cls_app W1 [Dm;Dm;D3;Dm;D3;D0]) in CG. cbn [cls cl] in CG.
      pose proof merge_cells as MC. lia.
    + intros r. rewrite zeros_split. eapply evstep_trans; [apply (Hrun ([0]^^Mz *> r))|]. apply progress_evstep. apply Hrec.
  - intros r. replace (N + Mz - N) with Mz by lia. apply Hrec.
Qed.
End Step.

Lemma HC_E a J W d k l0 r: Inv W d -> d <> Dm -> sv false (W ++ [d]) = true -> length W = a + S J ->
  (wv (W ++ [d]) + Z.of_nat k = wv ((repeat D2 a ++ [Dm] ++ repeat D2 J) ++ [D2]))%Z ->
  (3 * wv ((repeat D2 a ++ [Dm] ++ repeat D2 J) ++ [D2]) < 2 * (4 ^ Z.of_nat (S (length W)) - 1))%Z ->
  Run l0 (TDig D2) W d ([0]^^(2 * k) *> r) (repeat D2 a ++ [Dm] ++ repeat D2 J) D2 r (2 * k).
Proof.
  intros HI Hd Hs Hl Hv Hb.
  destruct (incKQ (TDig D2) [] (or_introl eq_refl) eq_refl k W d l0 r HI Hd ltac:(lia))
    as [ws' [d0' [N [S1 [HI' [Hd' [Hl' [Hw [Hc Hs']]]]]]]]].
  assert (EW: (repeat D2 a ++ [Dm] ++ repeat D2 J) ++ [D2] = repeat D2 a ++ Dm :: repeat D2 (S J))
    by (rewrite <- !app_assoc; cbn [app]; rewrite repeat_app1; reflexivity).
  assert (E: ws' ++ [d0'] = (repeat D2 a ++ [Dm] ++ repeat D2 J) ++ [D2]).
  { rewrite EW. apply (unique_m2 a J); [exact (Hs' Hs) | rewrite length_app, Hl', Hl; cbn [length]; lia | rewrite Hw, <- EW; lia]. }
  apply app_inj_tail in E. destruct E as [-> ->]. exists N. split; [exact S1 | exact Hc].
Qed.
Lemma HC_O WX W d k l0 r: Inv W d -> d <> Dm -> Forall pos012 (WX ++ [D2]) -> length WX = length W ->
  (wv (W ++ [d]) + Z.of_nat k = wv (WX ++ [D2]))%Z -> (3 * wv (WX ++ [D2]) < 2 * (4 ^ Z.of_nat (S (length W)) - 1))%Z ->
  Run l0 (TDig D2) W d ([0]^^(2 * k) *> r) WX D2 r (2 * k).
Proof.
  intros HI Hd Hp Hl Hv Hb.
  destruct (incKQ (TDig D2) [] (or_introl eq_refl) eq_refl k W d l0 r HI Hd) as [w1 [e1 [N [Hs [HI' [Hd' [Hl1 [Hw [Hcl _]]]]]]]]]; [lia|].
  assert (E: w1 ++ [e1] = WX ++ [D2]).
  { apply (inv_unique _ _ false); [rewrite !length_app, Hl1, Hl; reflexivity | apply Inv_word; exact HI' | exact Hp | lia]. }
  apply app_inj_tail in E. destruct E as [-> ->]. exists N. split; [exact Hs | exact Hcl].
Qed.

Definition p012b (d : dg) : bool := match d with D0 | D1 | D2 => true | _ => false end.
Lemma pos012_dec l: forallb p012b l = true -> Forall pos012 l.
Proof.
  induction l as [|d l IH]; intros H; [constructor|]. cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  constructor; [destruct d; cbn in H1; try discriminate; unfold pos012; auto | apply IH; exact H2].
Qed.

Definition REM17 : list Sym := Ercat ([D0;D0] ++ repeat Dm 13) ++ Zl D3.
Definition D17 : list dg := repeat Dm 13 ++ [D0; D1].
Definition WX17 : list dg := repeat D2 14 ++ [Dm] ++ repeat D2 0.
Definition W117 : list dg := (zm 7 ++ [D2; D0; Dm; Dm]) ++ zm 4 ++ [D0].
Ltac sv := first [reflexivity | lia | discriminate | assumption | eexists; reflexivity
  | lazymatch goal with |- Inv _ _ => unfold Inv, ok; vm_compute; discriminate | |- _ = _ => vm_compute; reflexivity end
  | repeat match goal with x := _ |- _ => subst x end; lia].
Lemma step17 W d N R: LevD 17 47 W d N R -> Next 35 95 W d N R.
Proof.
  intros HL.
  destruct (count_to_top D17 D0) as [k2 Hk2]; [vm_compute; discriminate|].
  eapply (step 17 47 11 27 50 0 k2 REM17 D17 WX17 W117 D0); try solve [sv].
  - intros l n r. replace ([0]^^(2 * 27) *> r) with ([0]^^(2 * 26) *> [0;0] *> r) by reflexivity.
    unfold REM17. rewrite (Str_app_assoc (Ercat ([D0; D0] ++ repeat Dm 13)) (Zl D3) r). apply fire17.
  - intros l0 r. unfold REM17. rewrite (Str_app_assoc (Ercat ([D0; D0] ++ repeat Dm 13)) (Zl D3) r).
    change (S2L l0 (TDig D2) WX17 D2 <* [1]^^0) with (S2L l0 (TDig D2) WX17 D2).
    replace D17 with (rev (D0 :: repeat Dm 13) ++ [sc D0]) by reflexivity.
    apply s1_z3; [left; reflexivity | reflexivity].
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. unfold WX17 in *. apply HC_E; auto; rewrite Hl; vm_compute; reflexivity.
  - intros l0 x T Hx. exact (glue_17 KS KS1 KSs l0 x T Hx).
Qed.
Definition REM35 : list Sym := Ercat ([Dm;D2] ++ repeat Dm 31) ++ Zl D3.
Definition D35 : list dg := repeat Dm 31 ++ [D2; D0].
Definition WX35 : list dg := repeat D2 31 ++ [D1; D0] ++ repeat D2 0.
Definition W135 : list dg := (zm 15 ++ [D0; D0; Dm; D2; Dm; Dm]) ++ zm 13 ++ [D0].
Lemma step35 W d N R: LevD 35 95 W d N R -> Next 71 191 W d N R.
Proof.
  intros HL.
  destruct (count_to_top D35 D0) as [k2 Hk2]; [vm_compute; discriminate|].
  eapply (step 35 95 23 55 104 3 k2 REM35 D35 WX35 W135 D0); try solve [sv].
  - intros l n r. replace ([0]^^(2 * 55) *> r) with ([0]^^(2 * 54) *> [0;0] *> r) by reflexivity.
    unfold REM35. rewrite (Str_app_assoc (Ercat ([Dm; D2] ++ repeat Dm 31)) (Zl D3) r). apply fire35.
  - intros l0 r. unfold REM35. rewrite (Str_app_assoc (Ercat ([Dm; D2] ++ repeat Dm 31)) (Zl D3) r).
    change (S2L l0 (TDig D2) WX35 D2 <* [1]^^3) with (S2L l0 (TDig D2) WX35 D2 <* [1;1;1]).
    replace D35 with (rev (D2 :: repeat Dm 31) ++ [D0]) by reflexivity.
    apply s1_z3t; [left; split; reflexivity | reflexivity].
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. apply HC_O; auto; try (apply pos012_dec; reflexivity); rewrite ?Hl; vm_compute; reflexivity.
  - intros l0 x T Hx. apply (glue KS KS1 KSs _ (repeat Dm 32 ++ LrO 0)); [reflexivity | reflexivity | lia | exact Hx |].
    pose proof (s3_Oeven0 16 (l0 <* [1]^^9) T ltac:(lia) ltac:(lia)) as Hs. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
Qed.

Definition REM71 : list Sym := Ercat ([D1;D1;D0] ++ repeat Dm 66) ++ Zl D1.
Definition D71 : list dg := repeat Dm 66 ++ [D0; D1; D1].
Definition WX71 : list dg := repeat D2 67 ++ [Dm] ++ repeat D2 1.
Definition W171 : list dg := (zm 33 ++ [D0; D0; D2; D2; Dm; Dm]) ++ zm 31 ++ [D0].
Lemma step71 W d N R: LevD 71 191 W d N R -> Next 143 383 W d N R.
Proof.
  intros HL.
  destruct (count_to_top D71 D2) as [k2 Hk2]; [vm_compute; discriminate|].
  eapply (step 71 191 47 109 212 0 k2 REM71 D71 WX71 W171 D2); try solve [sv].
  - intros l n r. replace ([0]^^(2 * 109) *> r) with ([0]^^(2 * 108) *> [0;0] *> r) by reflexivity.
    unfold REM71. rewrite (Str_app_assoc (Ercat ([D1; D1; D0] ++ repeat Dm 66)) (Zl D1) r). apply fire71.
  - intros l0 r. unfold REM71. rewrite (Str_app_assoc (Ercat ([D1; D1; D0] ++ repeat Dm 66)) (Zl D1) r).
    change (S2L l0 (TDig D2) WX71 D2 <* [1]^^0) with (S2L l0 (TDig D2) WX71 D2).
    replace ([D1; D1; D0] ++ repeat Dm 66) with (rev D71) by reflexivity.
    apply s1_low1; [discriminate | reflexivity].
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. unfold WX71 in *. apply HC_E; auto; rewrite Hl; vm_compute; reflexivity.
  - intros l0 x T Hx. apply (glue KS KS1 KSs _ (repeat Dm 67 ++ LrE 0)); [reflexivity | reflexivity | lia | exact Hx |].
    pose proof (s3_Eeven0 33 (l0 <* [1]^^9) T ltac:(lia) ltac:(lia)) as Hs. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
Qed.

Definition REM143 : list Sym := Ercat ([D0;D2] ++ repeat Dm 138) ++ Er' D0 ++ [1;1;1;1;1;1;1].
Definition D143 : list dg := repeat Dm 138 ++ [D2; D0; D0].
Definition WX143 : list dg := repeat D2 138 ++ [D1; D0] ++ repeat D2 1.
Definition W1143 : list dg := (zm 69 ++ [D0; D2] ++ zm 0 ++ [D0] ++ [D2; Dm; Dm]) ++ zm (69 + 0 - 2) ++ [D0].
Lemma step143 W d N R: LevD 143 383 W d N R -> Next 287 767 W d N R.
Proof.
  intros HL.
  destruct (count_to_top D143 D0) as [k2 Hk2]; [vm_compute; discriminate|].
  eapply (step 143 383 95 215 428 0 k2 REM143 D143 WX143 W1143 D0); try solve [sv].
  - intros l n r. replace ([0]^^(2 * 215) *> r) with ([0]^^(2 * 214) *> [0;0] *> r) by reflexivity.
    unfold REM143. rewrite (Str_app_assoc (Ercat ([D0; D2] ++ repeat Dm 138)) (Er' D0 ++ [1;1;1;1;1;1;1]) r).
    rewrite (Str_app_assoc (Er' D0) [1;1;1;1;1;1;1] r). apply fire143.
  - intros l0 r. unfold REM143. rewrite (app_assoc (Ercat ([D0; D2] ++ repeat Dm 138)) (Er' D0) [1;1;1;1;1;1;1]).
    rewrite (Str_app_assoc (Ercat ([D0; D2] ++ repeat Dm 138) ++ Er' D0) [1;1;1;1;1;1;1] r).
    change (S2L l0 (TDig D2) WX143 D2 <* [1]^^0) with (S2L l0 (TDig D2) WX143 D2).
    replace (Ercat ([D0; D2] ++ repeat Dm 138) ++ Er' D0) with (Ercat (rev D143)) by reflexivity.
    apply s1_m1; [discriminate | reflexivity].
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. apply HC_O; auto; try (apply pos012_dec; reflexivity); rewrite ?Hl; vm_compute; reflexivity.
  - intros l0 x T Hx. apply (glue KS KS1 KSs _ (repeat Dm 139 ++ LrO 1)); [reflexivity | reflexivity | lia | exact Hx |].
    pose proof (s3_Oodd 0 69 (l0 <* [1]^^9) T ltac:(lia) ltac:(vm_compute; discriminate)) as Hs. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
Qed.

Definition REMe j : list Sym := Ercat (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j)) ++ Zl D1.
Definition De j : list dg := repeat Dm (288 * 4 ^ j - 7 - j) ++ [D0; D1; D1] ++ repeat D2 (S j).
Definition WXe j : list dg := repeat D2 (288 * 4 ^ j - j - 6) ++ [Dm] ++ repeat D2 (j + 2).

Lemma stepE j W1
  (HG: forall l0 x T, x + 3 * (288 * 4 ^ j - 1 - 2) + 3 = 2 * (4 ^ S (288 * 4 ^ j - 1 - 2) - 4) ->
    Glued KS l0 (WXe j) (288 * 4 ^ j - 1 - 2) x W1 T)
  (HW1: count3 W1 = O) (HW1h: exists W1', W1 = D0 :: Dm :: W1') (HW1l: length W1 = 2 * (288 * 4 ^ j - 1) - 7)
  W d N R: LevD (288 * 4 ^ j - 1) (768 * 4 ^ j - 1) W d N R -> Next (576 * 4 ^ j - 1) (1536 * 4 ^ j - 1) W d N R.
Proof.
  intros HL. pose proof (pow4_pos j) as HP0. pose proof (p4nat_ge j) as HPj.
  assert (EZ: Z.of_nat (4 ^ j) = (4 ^ Z.of_nat j)%Z) by apply p4nat.
  set (m := 288 * 4 ^ j - 1) in *.
  assert (Lm1: length (De j ++ [D2]) = m - 1).
  { unfold De, m. rewrite !length_app, !repeat_length. cbn [length]. lia. }
  assert (LvD: lv (De j ++ [D2]) = (81 * (16 * 4 ^ Z.of_nat j) - 2)%Z).
  { unfold De. rewrite <- !app_assoc, lv_dm. cbn [app]. rewrite repeat_app1.
    change (D0 :: D1 :: D1 :: repeat D2 (S (S j))) with ([D0; D1; D1] ++ repeat D2 (S (S j))).
    rewrite lv_y2. change (lv [D0; D1; D1]) with 79%Z. rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia. lia. }
  assert (WvD: (3 * wv (De j ++ [D2]) = 81 * (16 * 4 ^ Z.of_nat j) - 2 - 4 ^ Z.of_nat (m - 1))%Z)
    by (rewrite wv_from_lv, LvD, Lm1; reflexivity).
  assert (ClsD: cls (De j ++ [D2]) = 2016 * 4 ^ j - 13).
  { unfold De. rewrite !cls_app, cls_dm, cls_rep2. cbn [cls cl]. lia. }
  destruct (count_to_top (De j) D2) as [k2 Hk2].
  { assert (Hn: (wv (De j ++ [D2]) <= -1)%Z).
    { unfold De. replace (288 * 4 ^ j - 7 - j) with (S (288 * 4 ^ j - 8 - j)) by lia. cbn [repeat app]. apply wv_dm_neg. }
    pose proof (pow4_ge1 (S (length (De j)))). lia. }
  assert (Lm2: length (De j) = m - 2) by (rewrite length_app in Lm1; cbn [length] in Lm1; lia).
  rewrite Lm2 in Hk2.
  assert (HWX: (3 * wv (WXe j ++ [D2]) = 2 * 4 ^ Z.of_nat (m - 1) - 2 * Z.of_nat m - 4)%Z).
  { unfold WXe. replace ((repeat D2 (288 * 4 ^ j - j - 6) ++ [Dm] ++ repeat D2 (j + 2)) ++ [D2])
      with (repeat D2 (288 * 4 ^ j - j - 6) ++ [Dm] ++ repeat D2 (j + 3))
      by (rewrite <- !app_assoc; cbn [app]; rewrite repeat_app1; do 3 f_equal; lia).
    rewrite wv_m_in. replace (288 * 4 ^ j - j - 6 + 1 + (j + 3)) with (m - 1) by (unfold m; lia).
    pose proof (all2_wv (m - 1)) as A2.
    rewrite (pow4_add j 3). change (4 ^ Z.of_nat 3)%Z with 64%Z.
    assert (Zm: Z.of_nat m = (288 * 4 ^ Z.of_nat j - 1)%Z) by (unfold m; rewrite Nat2Z.inj_sub, Nat2Z.inj_mul, EZ by lia; reflexivity).
    rewrite Zm. lia. }
  replace (576 * 4 ^ j - 1) with (2 * m + 1) by (unfold m; lia).
  replace (1536 * 4 ^ j - 1) with (2 * (768 * 4 ^ j - 1) + 1) by lia.
  eapply (step m (768 * 4 ^ j - 1) (192 * 4 ^ j - 1) (432 * 4 ^ j + 1) (864 * 4 ^ j - 4) 0 k2 (REMe j) (De j) (WXe j) W1 D2); try lia; try discriminate; try assumption.
  - intros l n r. unfold m. replace (288 * 4 ^ j - 1 - 2) with (S (S (288 * 4 ^ j - 5))) by lia.
    replace (n + (864 * 4 ^ j - 4)) with (9 + n + 3 * (288 * 4 ^ j - 6) + 5) by lia.
    replace (2 * (432 * 4 ^ j + 1)) with (10 + (2 * (432 * 4 ^ j - 5) + 2)) by lia.
    rewrite (zeros_split 10 (2 * (432 * 4 ^ j - 5) + 2)), (zeros_split (2 * (432 * 4 ^ j - 5)) 2).
    change ([0]^^2 *> r) with ([0;0] *> r).
    follow (climb_startQ (TDig D2) [] (288 * 4 ^ j - 5) (l <* [1]^^n) ([0]^^(2 * (432 * 4 ^ j - 5)) *> [0;0] *> r) (or_introl eq_refl) eq_refl).
    rewrite ones_sides. unfold REMe.
    rewrite (Str_app_assoc (Ercat (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j))) (Zl D1) r).
    apply fire_even.
  - intros l0 r. unfold REMe.
    rewrite (Str_app_assoc (Ercat (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j))) (Zl D1) r).
    change (S2L l0 (TDig D2) (WXe j) D2 <* [1]^^0) with (S2L l0 (TDig D2) (WXe j) D2).
    replace (repeat D2 (S j) ++ [D1;D1;D0] ++ repeat Dm (288 * 4 ^ j - 7 - j)) with (rev (De j))
      by (unfold De; rewrite !rev_app_distr, !rev_repeat; cbn [rev app]; rewrite <- !app_assoc; reflexivity).
    apply s1_low1; [unfold De; destruct (288 * 4 ^ j - 7 - j); discriminate|].
    unfold De. rewrite !count3_app, count3_repeatm, count3_repeat2. reflexivity.
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. unfold WXe in *. apply HC_E; auto.
    + rewrite Hl. unfold m. lia.
    + rewrite Hl. replace (S (m - 2)) with (m - 1) by (unfold m; lia). lia.
  - unfold Inv, ok. cbn [lowc]. unfold De. rewrite <- !app_assoc. cbn [app]. rewrite scan_dm0. cbn [app scan].
    rewrite scan_2s. cbn [scan]. discriminate.
  - assert (Zc: Z.of_nat (cls (De j ++ [D2])) = (2016 * 4 ^ Z.of_nat j - 13)%Z)
      by (rewrite ClsD, Nat2Z.inj_sub, Nat2Z.inj_mul, EZ by lia; reflexivity).
    assert (Zm2: Z.of_nat (m - 2) = (288 * 4 ^ Z.of_nat j - 3)%Z) by (unfold m; lia).
    replace (S (m - 2)) with (m - 1) by (unfold m; lia). rewrite Zc, Zm2. cbn [Z.of_nat]. lia.
Qed.
Definition REMo j : list Sym := Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j)) ++ Er' D2 ++ [1;1;1;1;1;1;1].
Definition Do j : list dg := repeat Dm (576 * 4 ^ j - 7 - j) ++ [D2; D0; D0] ++ repeat D2 (S j).
Definition WXo j : list dg := repeat D2 (576 * 4 ^ j - j - 7) ++ [D1; D0] ++ repeat D2 (j + 2).

Lemma stepO j W1
  (HG: forall l0 x T, x + 3 * (576 * 4 ^ j - 1 - 2) + 3 = 2 * (4 ^ S (576 * 4 ^ j - 1 - 2) - 4) ->
    Glued KS l0 (WXo j) (576 * 4 ^ j - 1 - 2) x W1 T)
  (HW1: count3 W1 = O) (HW1h: exists W1', W1 = D0 :: Dm :: W1') (HW1l: length W1 = 2 * (576 * 4 ^ j - 1) - 7)
  W d N R: LevD (576 * 4 ^ j - 1) (1536 * 4 ^ j - 1) W d N R -> Next (288 * 4 ^ S j - 1) (768 * 4 ^ S j - 1) W d N R.
Proof.
  intros HL. pose proof (pow4_pos j) as HP0. pose proof (p4nat_ge j) as HPj.
  assert (EZ: Z.of_nat (4 ^ j) = (4 ^ Z.of_nat j)%Z) by apply p4nat.
  set (m := 576 * 4 ^ j - 1) in *.
  assert (Lm1: length (Do j ++ [D0]) = m - 1).
  { unfold Do, m. rewrite !length_app, !repeat_length. cbn [length]. lia. }
  assert (LvD: lv (Do j ++ [D0]) = (2592 * 4 ^ Z.of_nat j - 8)%Z).
  { unfold Do. rewrite <- !app_assoc, lv_dm, app_assoc, lv_snoc.
    change ([D2; D0; D0] ++ repeat D2 (S j)) with ([D2; D0; D0] ++ repeat D2 (S j)).
    rewrite lv_y2. change (lv [D2; D0; D0]) with 160%Z. cbn [dv]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
  assert (WvD: (3 * wv (Do j ++ [D0]) = 2592 * 4 ^ Z.of_nat j - 8 - 4 ^ Z.of_nat (m - 1))%Z)
    by (rewrite wv_from_lv, LvD, Lm1; reflexivity).
  assert (ClsD: cls (Do j ++ [D0]) = 4032 * 4 ^ j - 17).
  { unfold Do. rewrite !cls_app, cls_dm, cls_rep2. cbn [cls cl]. lia. }
  destruct (count_to_top (Do j) D0) as [k2 Hk2].
  { assert (Hn: (wv (Do j ++ [D0]) <= -1)%Z).
    { unfold Do. replace (576 * 4 ^ j - 7 - j) with (S (576 * 4 ^ j - 8 - j)) by lia. cbn [repeat app]. apply wv_dm_neg. }
    pose proof (pow4_ge1 (S (length (Do j)))). lia. }
  assert (Lm2: length (Do j) = m - 2) by (rewrite length_app in Lm1; cbn [length] in Lm1; lia).
  rewrite Lm2 in Hk2.
  assert (HWX: (3 * wv (WXo j ++ [D2]) = 2 * 4 ^ Z.of_nat (m - 1) - 2 * Z.of_nat m - 4)%Z).
  { unfold WXo. replace ((repeat D2 (576 * 4 ^ j - j - 7) ++ [D1; D0] ++ repeat D2 (j + 2)) ++ [D2])
      with (repeat D2 (576 * 4 ^ j - j - 7) ++ [D1; D0] ++ repeat D2 (j + 3))
      by (rewrite <- !app_assoc; cbn [app]; rewrite repeat_app1; do 4 f_equal; lia).
    rewrite wv_10_in. replace (576 * 4 ^ j - j - 7 + 2 + (j + 3)) with (m - 1) by (unfold m; lia).
    pose proof (all2_wv (m - 1)) as A2.
    rewrite (pow4_add j 3). change (4 ^ Z.of_nat 3)%Z with 64%Z.
    assert (Zm: Z.of_nat m = (576 * 4 ^ Z.of_nat j - 1)%Z) by (unfold m; lia).
    rewrite Zm. lia. }
  replace (288 * 4 ^ S j - 1) with (2 * m + 1) by (unfold m; rewrite Nat.pow_succ_r'; lia).
  replace (768 * 4 ^ S j - 1) with (2 * (1536 * 4 ^ j - 1) + 1) by (rewrite Nat.pow_succ_r'; lia).
  eapply (step m (1536 * 4 ^ j - 1) (384 * 4 ^ j - 1) (864 * 4 ^ j - 1) (1728 * 4 ^ j - 4) 0 k2 (REMo j) (Do j) (WXo j) W1 D0); try lia; try discriminate; try assumption.
  - intros l n r. unfold m. replace (576 * 4 ^ j - 1 - 2) with (S (S (576 * 4 ^ j - 5))) by lia.
    replace (n + (1728 * 4 ^ j - 4)) with (9 + n + 3 * (576 * 4 ^ j - 5) + 2) by lia.
    replace (2 * (864 * 4 ^ j - 1)) with (10 + (2 * (864 * 4 ^ j - 7) + 2)) by lia.
    rewrite (zeros_split 10 (2 * (864 * 4 ^ j - 7) + 2)), (zeros_split (2 * (864 * 4 ^ j - 7)) 2).
    change ([0]^^2 *> r) with ([0;0] *> r).
    follow (climb_startQ (TDig D2) [] (576 * 4 ^ j - 5) (l <* [1]^^n) ([0]^^(2 * (864 * 4 ^ j - 7)) *> [0;0] *> r) (or_introl eq_refl) eq_refl).
    rewrite ones_sides. unfold REMo.
    rewrite (Str_app_assoc (Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j))) (Er' D2 ++ [1;1;1;1;1;1;1]) r).
    rewrite (Str_app_assoc (Er' D2) [1;1;1;1;1;1;1] r).
    apply fire_odd.
  - intros l0 r. unfold REMo.
    rewrite (app_assoc (Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j))) (Er' D2) [1;1;1;1;1;1;1]).
    rewrite (Str_app_assoc (Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j)) ++ Er' D2) [1;1;1;1;1;1;1] r).
    change (S2L l0 (TDig D2) (WXo j) D2 <* [1]^^0) with (S2L l0 (TDig D2) (WXo j) D2).
    replace (Ercat (repeat D2 j ++ [D0;D0;D2] ++ repeat Dm (576 * 4 ^ j - 7 - j)) ++ Er' D2) with (Ercat (rev (Do j)))
      by (unfold Do; rewrite !rev_app_distr, !rev_repeat; cbn [rev app]; rewrite <- !app_assoc; reflexivity).
    apply s1_m1; [unfold Do; destruct (576 * 4 ^ j - 7 - j); discriminate|].
    unfold Do. rewrite !count3_app, count3_repeatm, count3_repeat2. reflexivity.
  - intros W0 d0 k l0 r HI Hd Hs Hl Hv. apply HC_O; auto.
    + unfold WXo. rewrite <- !app_assoc. apply Forall_app. split; [apply pos012_repeat2|].
      apply Forall_cons; [unfold pos012; auto|]. apply Forall_cons; [unfold pos012; auto|].
      apply Forall_app. split; [apply pos012_repeat2|]. apply Forall_cons; [unfold pos012; auto | constructor].
    + rewrite Hl. unfold WXo, m. rewrite !length_app, !repeat_length. cbn [length]. lia.
    + rewrite Hl. replace (S (m - 2)) with (m - 1) by (unfold m; lia). lia.
  - unfold Inv. cbn [lowc]. destruct (scan_3free false (Do j ++ [D0])) as [s' Es].
    + unfold Do. rewrite !count3_app, count3_repeatm, count3_repeat2. reflexivity.
    + unfold ok. rewrite Es. discriminate.
  - assert (Zc: Z.of_nat (cls (Do j ++ [D0])) = (4032 * 4 ^ Z.of_nat j - 17)%Z) by (rewrite ClsD; lia).
    assert (Zm2: Z.of_nat (m - 2) = (576 * 4 ^ Z.of_nat j - 3)%Z) by (unfold m; lia).
    replace (S (m - 2)) with (m - 1) by (unfold m; lia). rewrite Zc, Zm2. cbn [Z.of_nat]. lia.
Qed.
Lemma zm_cons r: 1 <= r -> zm r = D0 :: Dm :: zm (r - 1).
Proof. intros H. destruct r as [|r]; [lia|]. cbn [zm app]. replace (S r - 1) with r by lia. reflexivity. Qed.

Ltac wfacts := first [rewrite !count3_app, !count3_zm; reflexivity | rewrite (zm_cons _) by lia; eexists; reflexivity
  | rewrite !length_app, !zm_length; cbn [length]; lia].

Lemma stepE_all j W d N R: LevD (288 * 4 ^ j - 1) (768 * 4 ^ j - 1) W d N R ->
  Next (576 * 4 ^ j - 1) (1536 * 4 ^ j - 1) W d N R.
Proof.
  intros HL. destruct (Nat.Even_or_Odd j) as [[t ->] | [t ->]].
  - pose proof (p4nat_ge (2 * t)) as P1. pose proof (p4nat (2 * t)) as PZ.
    remember (144 * 4 ^ (2 * t) - t - 3) as Rr eqn:ERr.
    assert (EN: 288 * 4 ^ (2 * t) - 1 - 2 = 2 * Rr + 2 * t + 3) by lia.
    assert (EA: 288 * 4 ^ (2 * t) - 2 * t - 6 = 2 * Rr) by lia.
    apply (stepE (2 * t) ((zm Rr ++ [D1; D1] ++ zm t ++ [D0] ++ [D2; Dm; Dm]) ++ zm (Rr + t - 2) ++ [D0])); [| wfacts | wfacts | wfacts | exact HL].
    + intros l0 x T Hx. unfold WXe. rewrite EN in Hx |- *. rewrite EA.
      apply (glue KS KS1 KSs _ (repeat Dm (2 * Rr) ++ LrE (2 * t + 1))); [| unfold LrE; apply count3_W; reflexivity | lia | exact Hx |].
      { unfold LrE. rewrite <- lone_E. replace (2 * t + 2) with (S (2 * t + 1)) by lia. apply lr_even. }
      pose proof (s3_Eodd t Rr (l0 <* [1]^^9) T ltac:(lia)
        ltac:(rewrite (pow4_add (2 * t) 1); change (4 ^ Z.of_nat 1)%Z with 4%Z; lia)) as Hs. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
  - pose proof (p4nat_ge (2 * t + 1)) as P1. pose proof (p4nat (2 * t + 1)) as PZ.
    remember (144 * 4 ^ (2 * t + 1) - t - 4) as Rr eqn:ERr.
    assert (EN: 288 * 4 ^ (2 * t + 1) - 1 - 2 = 2 * Rr + 2 * (t + 1) + 3) by lia.
    assert (EA: 288 * 4 ^ (2 * t + 1) - (2 * t + 1) - 6 = 2 * Rr + 1) by lia.
    apply (stepE (2 * t + 1) ((zm Rr ++ [D0; D0; D2; Dm] ++ zm (t + 1 - 1) ++ [D0] ++ [D2; Dm; Dm]) ++ zm (Rr + (t + 1) - 2) ++ [D0]));
      [| wfacts | wfacts | wfacts | exact HL].
    + intros l0 x T Hx. unfold WXe. rewrite EN in Hx |- *. rewrite EA.
      replace (2 * t + 1 + 2) with (2 * (t + 1) + 1) by lia.
      apply (glue KS KS1 KSs _ (repeat Dm (2 * Rr + 1) ++ LrE (2 * (t + 1)))); [| unfold LrE; apply count3_W; reflexivity | lia | exact Hx |].
      { unfold LrE. rewrite <- lone_E. replace (2 * (t + 1) + 1) with (S (2 * (t + 1))) by lia. apply lr_even. }
      pose proof (s3_Eeven (t + 1) Rr (l0 <* [1]^^9) T ltac:(lia) ltac:(lia) ltac:(replace (2 * (t + 1)) with (2 * t + 1 + 1) by lia;
        rewrite (pow4_add (2 * t + 1) 1); change (4 ^ Z.of_nat 1)%Z with 4%Z; lia)) as Hs. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
Qed.

Lemma stepO_all j W d N R: LevD (576 * 4 ^ j - 1) (1536 * 4 ^ j - 1) W d N R ->
  Next (288 * 4 ^ S j - 1) (768 * 4 ^ S j - 1) W d N R.
Proof.
  intros HL. destruct (Nat.Even_or_Odd j) as [[t ->] | [t ->]].
  - pose proof (p4nat_ge (2 * t)) as P1. pose proof (p4nat (2 * t)) as PZ.
    remember (288 * 4 ^ (2 * t) - t - 3) as Rr eqn:ERr.
    assert (EN: 576 * 4 ^ (2 * t) - 1 - 2 = 2 * Rr + 2 * (t + 1) + 1) by lia.
    assert (EA: 576 * 4 ^ (2 * t) - 2 * t - 7 = 2 * Rr - 1) by lia.
    apply (stepO (2 * t) ((zm (Rr - 1) ++ [D0; D0; Dm; Dm] ++ zm (t + 1 - 1) ++ [D0] ++ [D2; Dm; Dm]) ++ zm (Rr + (t + 1) - 3) ++ [D0]));
      [| wfacts | wfacts | wfacts | exact HL].
    + intros l0 x T Hx. unfold WXo. rewrite EN in Hx |- *. rewrite EA.
      replace (2 * t + 2) with (2 * (t + 1)) by lia.
      apply (glue KS KS1 KSs _ (repeat Dm (S (2 * Rr - 1)) ++ LrO (2 * (t + 1))));
        [unfold LrO; rewrite <- lone_O; apply lr_odd | unfold LrO; apply count3_W; reflexivity | lia | exact Hx |].
      pose proof (s3_Oeven (t + 1) Rr (l0 <* [1]^^9) T ltac:(lia) ltac:(lia) ltac:(replace (2 * (t + 1)) with (2 * t + 2) by lia;
        rewrite (pow4_add (2 * t) 2); change (4 ^ Z.of_nat 2)%Z with 16%Z; lia)) as Hs.
      replace (S (2 * Rr - 1)) with (2 * Rr) by lia. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
  - pose proof (p4nat_ge (2 * t + 1)) as P1. pose proof (p4nat (2 * t + 1)) as PZ.
    remember (288 * 4 ^ (2 * t + 1) - t - 4) as Rr eqn:ERr.
    assert (EN: 576 * 4 ^ (2 * t + 1) - 1 - 2 = 2 * Rr + 2 * (t + 1) + 3) by lia.
    assert (EA: 576 * 4 ^ (2 * t + 1) - (2 * t + 1) - 7 = 2 * Rr) by lia.
    apply (stepO (2 * t + 1) ((zm Rr ++ [D0; D2] ++ zm (t + 1) ++ [D0] ++ [D2; Dm; Dm]) ++ zm (Rr + (t + 1) - 2) ++ [D0]));
      [| wfacts | wfacts | wfacts | exact HL].
    + intros l0 x T Hx. unfold WXo. rewrite EN in Hx |- *. rewrite EA.
      replace (2 * t + 1 + 2) with (2 * (t + 1) + 1) by lia.
      apply (glue KS KS1 KSs _ (repeat Dm (S (2 * Rr)) ++ LrO (2 * (t + 1) + 1)));
        [unfold LrO; rewrite <- lone_O; apply lr_odd | unfold LrO; apply count3_W; reflexivity | lia | exact Hx |].
      pose proof (s3_Oodd (t + 1) Rr (l0 <* [1]^^9) T ltac:(lia) ltac:(replace (2 * (t + 1) + 1) with (2 * t + 1 + 2) by lia;
        rewrite (pow4_add (2 * t + 1) 2); change (4 ^ Z.of_nat 2)%Z with 16%Z; lia)) as Hs.
      replace (S (2 * Rr)) with (2 * Rr + 1) by lia. rewrite <- !app_assoc in Hs. rewrite <- !app_assoc. exact Hs.
Qed.

Definition Lvl (m E : nat) : Prop :=
  (m = 17 /\ E = 47) \/ (m = 35 /\ E = 95) \/ (m = 71 /\ E = 191) \/ (m = 143 /\ E = 383) \/
  (exists j, m = 288 * 4 ^ j - 1 /\ E = 768 * 4 ^ j - 1) \/ (exists j, m = 576 * 4 ^ j - 1 /\ E = 1536 * 4 ^ j - 1).
Definition Pc (c : Q * tape) : Prop :=
  exists m E W d N R, Lvl m E /\ LevD m E W d N R /\ c = RecT (0inf <* [1]^^R) (TDig D2) W d 0inf.

Lemma progress_step c: Pc c -> exists c', Pc c' /\ c -[tm]->+ c'.
Proof.
  intros [m [E [W [d [N [R [Hl [HL ->]]]]]]]].
  assert (Gen: forall m' E', Lvl m' E' -> Next m' E' W d N R ->
    exists c', Pc c' /\ RecT (0inf <* [1]^^R) (TDig D2) W d 0inf -[tm]->+ c').
  { intros m' E' Hl' [W' [N' [R' [HL' Hr]]]]. exists (RecT (0inf <* [1]^^R') (TDig D2) W' ML 0inf). split.
    - exists m', E', W', ML, N', R'. auto.
    - specialize (Hr 0inf). rewrite zeros_inf in Hr. exact Hr. }
  destruct Hl as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[j [-> ->]] | [j [-> ->]]]]]]].
  - apply (Gen 35 95); [unfold Lvl; auto | apply step17; exact HL].
  - apply (Gen 71 191); [unfold Lvl; auto 6 | apply step35; exact HL].
  - apply (Gen 143 383); [unfold Lvl; auto 7 | apply step71; exact HL].
  - apply (Gen (288 * 4 ^ O - 1) (768 * 4 ^ O - 1)); [unfold Lvl; right; right; right; right; left; exists O; auto | apply step143; exact HL].
  - apply (Gen (576 * 4 ^ j - 1) (1536 * 4 ^ j - 1));
      [unfold Lvl; right; right; right; right; right; exists j; auto | apply stepE_all; exact HL].
  - apply (Gen (288 * 4 ^ S j - 1) (768 * 4 ^ S j - 1));
      [unfold Lvl; right; right; right; right; left; exists (S j); auto | apply stepO_all; exact HL].
Qed.

Theorem nonhalt_of_base W d N R: LevD 17 47 W d N R -> ~ halts tm c0.
Proof.
  intros HL.
  assert (Hrun: c0 -[tm]->* RecT (0inf <* [1]^^R) (TDig D2) W d 0inf).
  { pose proof HL as [_ [_ [_ [_ [_ [_ Hr]]]]]]. specialize (Hr 0inf). rewrite zeros_inf in Hr. exact Hr. }
  apply (multistep_nonhalt _ _ _ Hrun).
  apply (progress_nonhalt tm Pc); [exact progress_step|].
  exists 17, 47, W, d, N, R. split; [left; auto | split; [exact HL | reflexivity]].
Qed.
End Gen.

Ltac rule := unfold bt, dec, Rl, Er, Er', EXT, OVT, MLONE; let l := fresh "l" in let r := fresh "r" in
  lazymatch goal with
  | |- forall d : dg, _ => intros [] l r; intros; try congruence; es' & l r
  | |- forall _, _ -[_]->* _ => intros r; first [solve [finish] | es' & r]
  | |- _ => intros l r; es' & l r end.
Ltac fact := first [reflexivity | discriminate | intros; reflexivity | intros []; unfold ok; cbn; discriminate
  | lazymatch goal with |- mfacts _ _ _ _ _ =>
      unfold mfacts; repeat split; first [reflexivity | discriminate | intros []; unfold ok; cbn; discriminate] end].
Ltac base n := unfold LevD; split; [unfold Inv, ok; vm_compute; discriminate|];
  split; [discriminate|]; split; [vm_compute; reflexivity|]; split; [reflexivity|];
  split; [vm_compute; discriminate|]; split; [apply Nat.eqb_eq; vm_compute; reflexivity|];
  intros r; apply (base_of_check _ n 47); vm_cast_no_check (eq_refl true).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC---_0LD1RD_1RA0RE_0RF1RC_1LF0LA").
Notation Y0 := [0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;0;0;0;1;1;1;1;1;1;1].
Notation Y1 := [0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;0;0;0;1;1;1;1;1;1;1].
Notation Y2 := [0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;0;0;0;1;1;1;1;1;1;1].
Notation Y3 := [0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1].
Notation YR := [1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1].
Theorem nonhalt: ~halts tm c0.
Proof.
  apply (nonhalt_of_base tm A [0;1;1;1] 6 [D2;D0;D2;D0;D2;D2] D0 Y0 YR [Y1;Y2;Y3])
    with (W := [D0;D2;D0;D2;D0;Dm;D1;D0;D0;D2;D0;D2;D0;D2;D2]) (d := D0) (N := 108059) (R := 107991).
  all: try solve [fact | rule].
  - cbn [mchain]. repeat split; intros; es' & l r.
  - base 20274513%N.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_0LA1RA_0RE1RC_1LE0LF_0RC0LF").
Notation Y0 := [0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1].
Notation Y1 := [0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;0;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1].
Notation Y2 := [0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1].
Notation YR := [1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1;1;0;1;1;0;1;1;0;1;1;1;0;1].
Theorem nonhalt: ~halts tm c0.
Proof.
  apply (nonhalt_of_base tm F [1;1;1;0] 3 [D2;D0;D2;D0;D2;D0] D2 Y0 YR [Y1;Y2])
    with (W := [D0;D2;D0;D2;D0;Dm;D1;D0;D0;D2;D0;D2;D0;D2;D0]) (d := D2) (N := 108062) (R := 107994).
  all: try solve [fact | rule].
  - cbn [mchain]. repeat split; intros; es' & l r.
  - base 24009260%N.
Qed.
End TM2.
