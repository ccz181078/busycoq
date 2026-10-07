(* Adapted from the October 2026 nonhalting proof archive supplied by the user.
   The finite graph is constructed by a small generator, not a literal table. *)
From BusyCoq Require Import Individual62 FastRev.
From Coq Require Import Lia List String PeanoNat Bool.
Import ListNotations.

Module TM1.
(* Machine *)
Import ListNotations.
Open Scope list_scope.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0LF_---0LD_0LE1LD_0RF0LB_1RA1RE").
Definition config := (Q * tape)%type.
Notation "c -->* d" := (c -[tm]->* d) (at level 40).
Notation "c -->+ d" := (c -[tm]->+ d) (at level 40).

(* Words are written from left to right.  The official left stream is
   written in the opposite order, beginning next to the head. *)
Definition put (l : side) (w : list Sym) : side := rev w *> l.
Definition FR (l r : side) : config := l {{F}}> r.
Definition DL (l r : side) : config := l <{{D}} r.
Definition FL (l r : side) : config := l <{{F}} r.
Definition BL (l r : side) : config := l <{{B}} r.
Definition CE (r : side) : config := const 0 {{E}}> [0;0] *> r.

Definition wL : list Sym := [1;1;0].
Definition wX : list Sym := [1;1;0;1;1;0].
Definition wY : list Sym := [1;1;1;1].
Definition wa : list Sym := [1;1;1;0;1;0].
Definition wb : list Sym := [1;0;1;0].

Lemma put_app l u v : put l (u ++ v) = put (put l u) v.
Proof. unfold put. rewrite rev_app_distr, Str_app_assoc. reflexivity. Qed.

Lemma right_000 l r : FR l ([0;0;0] *> r) -->+ DL l ([1;0;1] *> r).
Proof. unfold FR, DL. execute. Qed.
Lemma right_001 l r : FR l ([0;0;1] *> r) -->+ FR (put l wL) r.
Proof. unfold FR, put, wL. execute. Qed.
Lemma right_01 l r : FR l ([0;1] *> r) -->+ FR (put l [1;1]) r.
Proof. unfold FR, put. execute. Qed.
Lemma right_10 l r : FR l ([1;0] *> r) -->+ FR (put l [1;0]) r.
Proof. unfold FR, put. execute. Qed.
Lemma right_11 l r : FR l ([1;1] *> r) -->+ FL l ([0;0] *> r).
Proof. unfold FR, FL. execute. Qed.

Lemma left_D1 l r : DL (put l [1]) r -->+ DL l ([1] *> r).
Proof. unfold DL, put. execute. Qed.
Lemma left_D10 l r : DL (put l [1;0]) r -->+ BL l ([0;0] *> r).
Proof. unfold DL, BL, put. execute. Qed.
Lemma left_B1 l r : BL (put l [1]) ([0;0] *> r) -->+ FL l ([0;0;0] *> r).
Proof. unfold BL, FL, put. execute. Qed.
Lemma left_B10 l r : BL (put l [1;0]) ([0;0] *> r) -->+ DL l ([0;1;0;0] *> r).
Proof. unfold BL, DL, put. execute. Qed.
Lemma left_F1 l r : FL (put l [1]) ([0;0] *> r) -->+ FR (put l [1;0]) ([0] *> r).
Proof. unfold FL, FR, put. execute. Qed.
Lemma left_F10 l r : FL (put l [1;0]) ([0;0] *> r) -->+ DL (put l [1]) ([1;0;1] *> r).
Proof. unfold FL, DL, put. execute. Qed.

(* A finite computation supplies evidence in the official step relation. *)

(* Flows *)
Definition leads (c : config) (P : config -> Prop) : Prop :=
  forall n, halts_in tm c n ->
  exists m d, m <= n /\ P d /\ halts_in tm d m.
Definition advances (c : config) (P : config -> Prop) : Prop :=
  forall n, halts_in tm c n ->
  exists m d, m < n /\ P d /\ halts_in tm d m.

Lemma reduce_evstep c d n : c -->* d -> halts_in tm c n ->
  exists m, m <= n /\ halts_in tm d m.
Proof.
  intros Hr Hh. destruct (with_counter Hr) as [k Hk].
  assert (Hkn : k <= n) by (eapply within_halt; eauto).
  exists (n-k). split; [lia|]. eapply preceeds_halt; eauto.
Qed.
Lemma reduce_progress c d n : c -->+ d -> halts_in tm c n ->
  exists m, m < n /\ halts_in tm d m.
Proof.
  intros Hr Hh. destruct (progress_multistep _ _ _ Hr) as [k Hk].
  assert (Hkn : S k <= n) by (eapply within_halt; eauto).
  exists (n-S k). split; [lia|]. eapply preceeds_halt; eauto.
Qed.

Lemma leads_here c P : P c -> leads c P.
Proof. intros HP n Hh. exists n,c. auto. Qed.
Lemma leads_native c d P : c -->* d -> P d -> leads c P.
Proof.
  intros Hr HP n Hh. destruct (reduce_evstep _ _ _ Hr Hh) as [m [Hmn Hm]].
  exists m,d. auto.
Qed.
Lemma leads_trans c P Q : leads c P ->
  (forall d, P d -> leads d Q) -> leads c Q.
Proof.
  intros H1 H2 n Hh. destruct (H1 n Hh) as [m [d [Hmn [HP Hm]]]].
  destruct (H2 d HP m Hm) as [k [e [Hkm [HQ Hk]]]].
  exists k,e. repeat split; auto; lia.
Qed.
Lemma leads_mono c P Q : leads c P -> (forall d, P d -> Q d) -> leads c Q.
Proof. intros H Hinc. eapply leads_trans; [exact H|]. intros. apply leads_here. auto. Qed.
Lemma advances_leads c P : advances c P -> leads c P.
Proof.
  intros H n Hh. destruct (H n Hh) as [m [d [Hmn Hrest]]].
  exists m,d. split; [lia|exact Hrest].
Qed.
Lemma advances_then c d P : c -->+ d -> leads d P -> advances c P.
Proof.
  intros Hr H n Hh. destruct (reduce_progress _ _ _ Hr Hh) as [m [Hmn Hm]].
  destruct (H m Hm) as [k [e [Hkm Hrest]]].
  exists k,e. split; [lia|exact Hrest].
Qed.
Lemma leads_follow c d P : c -->+ d -> leads d P -> leads c P.
Proof. intros. apply advances_leads. eapply advances_then; eauto. Qed.
Lemma advances_trans c P Q : advances c P ->
  (forall d, P d -> leads d Q) -> advances c Q.
Proof.
  intros H1 H2 n Hh. destruct (H1 n Hh) as [m [d [Hmn [HP Hm]]]].
  destruct (H2 d HP m Hm) as [k [e [Hkm Hrest]]].
  exists k,e. split; [lia|exact Hrest].
Qed.

Lemma decreasing_halt_budget P :
  (forall c, P c -> advances c P) -> forall c, P c -> ~halts tm c.
Proof.
  intros H c HP [n Hn]. revert c HP Hn.
  induction n using strong_induction. intros c HP Hn.
  destruct (H c HP n Hn) as [m [d [Hmn [Hd Hm]]]].
  eapply H0; eauto.
Qed.

(* Return *)
Inductive entry := GoRight | FromD | FromF | FromB.
(* false encodes 1, true encodes 10; the first item is nearest the head. *)
Definition chunk (b : bool) : list Sym := if b then [1;0] else [1].
Fixpoint stack_side (l : side) (s : list bool) : side :=
  match s with [] => l | b::s => put (stack_side l s) (chunk b) end.
Definition stack_config l s e r : config :=
  match e with
  | GoRight => FR (stack_side l s) r
  | FromD => DL (stack_side l s) r
  | FromF => FL (stack_side l s) ([0;0] *> r)
  | FromB => BL (stack_side l s) ([0;0] *> r)
  end.
Inductive contact (l : side) : config -> Prop :=
| contact_D r : contact l (DL l r)
| contact_F r : contact l (FL l ([0;0] *> r))
| contact_B r : contact l (BL l ([0;0] *> r)).

Lemma lift_contact c d P n : c -->+ d ->
  (forall m, m < n -> halts_in tm d m ->
   exists k e, k <= m /\ P e /\ halts_in tm e k) ->
  halts_in tm c n -> exists k e, k <= n /\ P e /\ halts_in tm e k.
Proof.
  intros Hr IH Hh. destruct (reduce_progress _ _ _ Hr Hh) as [m [Hmn Hm]].
  destruct (IH m Hmn Hm) as [k [e [Hkm Hrest]]].
  exists k,e. split; [lia|exact Hrest].
Qed.

Lemma stack_contact : forall n l s e r,
  halts_in tm (stack_config l s e r) n ->
  exists k c, k <= n /\ contact l c /\ halts_in tm c k.
Proof.
  induction n using strong_induction.
  intros l s e r Hhalt. destruct e.
  - destruct r as [b r]. destruct b.
    + destruct r as [b r]. destruct b.
      * destruct r as [b r]. destruct b.
        -- eapply lift_contact; [apply right_000| |exact Hhalt].
           intros m Hmn Hm. eapply H with (s:=s) (e:=FromD); eauto.
        -- eapply lift_contact; [apply right_001| |exact Hhalt].
           intros m Hmn Hm. eapply H with (s:=true::false::s) (e:=GoRight); eauto.
      * eapply lift_contact; [apply right_01| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=false::false::s) (e:=GoRight); eauto.
    + destruct r as [b r]. destruct b.
      * eapply lift_contact; [apply right_10| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=true::s) (e:=GoRight); eauto.
      * eapply lift_contact; [apply right_11| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=s) (e:=FromF); eauto.
  - destruct s as [|b s].
    + exists n,(DL l r). repeat split; auto. constructor.
    + destruct b.
      * eapply lift_contact; [apply left_D10| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=s) (e:=FromB); eauto.
      * eapply lift_contact; [apply left_D1| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=s) (e:=FromD); eauto.
  - destruct s as [|b s].
    + exists n,(FL l ([0;0] *> r)). repeat split; auto. constructor.
    + destruct b.
      * eapply lift_contact; [apply left_F10| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=false::s) (e:=FromD); eauto.
      * eapply lift_contact; [apply left_F1| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=true::s) (e:=GoRight); eauto.
  - destruct s as [|b s].
    + exists n,(BL l ([0;0] *> r)). repeat split; auto. constructor.
    + destruct b.
      * eapply lift_contact; [apply left_B10| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=s) (e:=FromD); eauto.
      * eapply lift_contact; [apply left_B1| |exact Hhalt].
        intros m Hmn Hm. eapply H with (s:=s) (e:=FromF) (r:=([0] *> r)); eauto.
Qed.

Lemma right_contacts l r : leads (FR l r) (contact l).
Proof. intros n Hn. exact (stack_contact n l [] GoRight r Hn). Qed.

Lemma stack_contacts l s e r : leads (stack_config l s e r) (contact l).
Proof. intros n Hn. exact (stack_contact n l s e r Hn). Qed.
Lemma right_contacts_advances l r : advances (FR l r) (contact l).
Proof.
  destruct r as [b r]. destruct b.
  - destruct r as [b r]. destruct b.
    + destruct r as [b r]. destruct b.
      * eapply advances_then; [apply right_000|]. apply leads_here. constructor.
      * eapply advances_then; [apply right_001|].
        apply (stack_contacts l [true;false] GoRight r).
    + eapply advances_then; [apply right_01|].
      apply (stack_contacts l [false;false] GoRight r).
  - destruct r as [b r]. destruct b.
    + eapply advances_then; [apply right_10|].
      apply (stack_contacts l [true] GoRight r).
    + eapply advances_then; [apply right_11|]. apply leads_here. constructor.
Qed.

(* Guards *)
Inductive weak_endpoint (l : side) : config -> Prop :=
| weak_D r : weak_endpoint l (DL l r)
| weak_F r : weak_endpoint l (FL l ([0;0;0] *> r)).
Inductive strong_endpoint (l : side) : config -> Prop :=
| strong_D r : strong_endpoint l (DL l (wa *> r))
| strong_F r : strong_endpoint l (FL l ([0;0;0] *> wa *> r)).

Lemma D_L l r : DL (put l wL) r -->+ FL l ([0;0;0] *> r).
Proof. unfold DL,FL,put,wL. execute. Qed.
Lemma F_L l r : FL (put l wL) ([0;0] *> r) -->+ DL l ([1;1;1;0;1] *> r).
Proof. unfold DL,FL,put,wL. execute. Qed.
Lemma B_L l r : BL (put l wL) ([0;0] *> r) -->+ DL l ([1;0;1;0;0] *> r).
Proof. unfold DL,BL,put,wL. execute. Qed.
Lemma D_11 l r : DL (put l [1;1]) r -->+ DL l ([1;1] *> r).
Proof. unfold DL,put. execute. Qed.
Lemma F_11 l r : FL (put l [1;1]) ([0;0] *> r) -->+ FR (put l wL) ([0] *> r).
Proof. unfold FL,FR,put,wL. execute. Qed.
Lemma B_11 l r : BL (put l [1;1]) ([0;0] *> r) -->+ FR (put l [1;0]) ([0;0] *> r).
Proof. unfold BL,FR,put. execute. Qed.
Lemma D_X l r : DL (put l wX) r -->+ DL l (wa *> r).
Proof. unfold DL,put,wX,wa. execute. Qed.
Lemma F_X000 l r : FL (put l wX) ([0;0;0] *> r) -->+ FL l ([0;0;0] *> wa *> r).
Proof. unfold FL,put,wX,wa. execute. Qed.

Lemma L_contact l c : contact (put l wL) c -> leads c (weak_endpoint l).
Proof.
  intros H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_L|constructor].
  - eapply leads_native; [apply progress_evstep; apply F_L|constructor].
  - eapply leads_native; [apply progress_evstep; apply B_L|constructor].
Qed.
Lemma L_right l r : leads (FR (put l wL) r) (weak_endpoint l).
Proof. eapply leads_trans; [apply right_contacts|]. intros c Hc. apply L_contact. exact Hc. Qed.

Definition transports (w : list Sym) : Prop :=
  forall l c, weak_endpoint (put l w) c -> leads c (weak_endpoint l).
Lemma transport_L : transports wL.
Proof.
  intros l c H. inversion H; subst; apply L_contact; constructor.
Qed.
Lemma transport_11 : transports [1;1].
Proof.
  intros l c H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_11|constructor].
  - eapply leads_follow; [apply F_11|]. apply L_right.
Qed.
Lemma transport_app u v : transports u -> transports v -> transports (u++v).
Proof.
  intros Hu Hv l c Hc. rewrite put_app in Hc.
  eapply leads_trans; [apply Hv; exact Hc|]. intros d Hd. apply Hu. exact Hd.
Qed.
Inductive middle_piece := PL | P11.
Definition piece_word p := match p with PL => wL | P11 => [1;1] end.
Fixpoint middle_word (ps : list middle_piece) : list Sym :=
  match ps with [] => [] | p::ps => piece_word p ++ middle_word ps end.
Lemma transport_middle ps : transports (middle_word ps).
Proof.
  induction ps as [|p ps IH].
  - intros l c H. cbn [middle_word put] in H. apply leads_here. exact H.
  - cbn [middle_word]. apply transport_app; [destruct p; apply transport_L || apply transport_11|exact IH].
Qed.
Lemma X_bridge l c : weak_endpoint (put l wX) c -> leads c (strong_endpoint l).
Proof.
  intros H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_X|constructor].
  - eapply leads_native; [apply progress_evstep; apply F_X000|constructor].
Qed.
Definition guard_word ps := (wX ++ middle_word ps) ++ wL.
Lemma guard_contact ps l c : contact (put l (guard_word ps)) c -> leads c (strong_endpoint l).
Proof.
  intros H. unfold guard_word in H. rewrite !put_app in H.
  eapply leads_trans; [apply L_contact; exact H|]. intros d Hd.
  eapply leads_trans; [exact (transport_middle ps (put l wX) d Hd)|]. intros e He.
  apply X_bridge. exact He.
Qed.
Lemma guard_right ps l r : leads (FR (put l (guard_word ps)) r) (strong_endpoint l).
Proof. eapply leads_trans; [apply right_contacts|]. intros c Hc. apply (guard_contact ps). exact Hc. Qed.

(* This sharper statement supplies the two B families used by the graph. *)
Inductive phase_contact (l : side) : config -> Prop :=
| phase_D r : phase_contact l (DL l r)
| phase_F r : phase_contact l (FL l ([0;0;0] *> r))
| phase_B101 r : phase_contact l (BL l ([0;0;1;0;1] *> r))
| phase_B11101 r : phase_contact l (BL l ([0;0;1;1;1;0;1] *> r)).
Lemma weak_phase l c : weak_endpoint l c -> phase_contact l c.
Proof. intros H. inversion H; subst; constructor. Qed.

Lemma D_10L l r : DL (put l ([1;0]++wL)) r -->+ DL l ([1;1;0;1;0] *> r).
Proof. unfold DL,put,wL. execute. Qed.
Lemma F_10L l r : FL (put l ([1;0]++wL)) ([0;0] *> r) -->+ BL l ([0;0;1;1;1;0;1] *> r).
Proof. unfold FL,BL,put,wL. execute. Qed.
Lemma B_10L l r : BL (put l ([1;0]++wL)) ([0;0] *> r) -->+ BL l ([0;0;1;0;1;0;0] *> r).
Proof. unfold BL,put,wL. execute. Qed.
Lemma right_10L l r : leads (FR (put l ([1;0]++wL)) r) (phase_contact l).
Proof.
  eapply leads_trans; [apply right_contacts|]. intros c H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_10L|constructor].
  - eapply leads_native; [apply progress_evstep; apply F_10L|constructor].
  - eapply leads_native; [apply progress_evstep; apply B_10L|].
    change (phase_contact l (BL l ([0;0;1;0;1] *> [0;0] *> r0))). constructor.
Qed.
Lemma right_10_000 l r : FR (put l [1;0]) ([0;0;0] *> r) -->+ BL l ([0;0;1;0;1] *> r).
Proof. unfold FR,BL,put. execute. Qed.
Lemma right_10_001 l r : FR (put l [1;0]) ([0;0;1] *> r) -->+ FR (put l ([1;0]++wL)) r.
Proof. unfold FR,put,wL. execute. Qed.
Lemma right_10_00 l r : leads (FR (put l [1;0]) ([0;0] *> r)) (phase_contact l).
Proof.
  destruct r as [b r]. destruct b.
  - eapply leads_native; [apply progress_evstep; apply right_10_000|constructor].
  - eapply leads_follow; [apply right_10_001|apply right_10L].
Qed.
Lemma right_11_phase l r : leads (FR (put l [1;1]) r) (phase_contact l).
Proof.
  eapply leads_trans; [apply right_contacts|]. intros c H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_11|constructor].
  - eapply leads_follow; [apply F_11|]. eapply leads_mono; [apply L_right|apply weak_phase].
  - eapply leads_follow; [apply B_11|apply right_10_00].
Qed.
Lemma right_zero_contacts l r : leads (FR l ([0] *> r)) (phase_contact l).
Proof.
  destruct r as [b r]. destruct b.
  - destruct r as [b r]. destruct b.
    + eapply leads_native; [apply progress_evstep; apply right_000|constructor].
    + eapply leads_follow; [apply right_001|]. eapply leads_mono; [apply L_right|apply weak_phase].
  - eapply leads_follow; [apply right_01|apply right_11_phase].
Qed.

(* Units *)
Inductive unit := UA | UT.
Inductive coding := CD | CF.
Definition HD1 u := match u with UA => wa | UT => wY ++ wa end.
Definition HF1 u := match u with UA => wa | UT => wa ++ wb end.
Definition G1 u := match u with UA => wX | UT => wX ++ wY end.
Fixpoint HD (us : list unit) : list Sym :=
  match us with [] => [] | u::us => HD1 u ++ HD us end.
Fixpoint HF (us : list unit) : list Sym :=
  match us with [] => [] | u::us => HF1 u ++ HF us end.
Fixpoint G (us : list unit) : list Sym :=
  match us with [] => [] | u::us => G1 u ++ G us end.
Definition marker d := match d with CD => [] | CF => wY end.
Definition body d us := match d with CD => HD us | CF => wb ++ HF us end.
Definition coded d us r := CE (body d us *> r).
Definition safe (c : config) :=
  exists d us r, 3 <= List.length us /\ c = coded d us r.
Definition formed d us := put (const 0) ([0] ++ marker d ++ G us).

Lemma HD_app us vs : HD (us++vs) = HD us ++ HD vs.
Proof. induction us; cbn; [reflexivity|rewrite IHus, app_assoc; reflexivity]. Qed.
Lemma HF_app us vs : HF (us++vs) = HF us ++ HF vs.
Proof. induction us; cbn; [reflexivity|rewrite IHus, app_assoc; reflexivity]. Qed.
Lemma G_app us vs : G (us++vs) = G us ++ G vs.
Proof. induction us; cbn; [reflexivity|rewrite IHus, app_assoc; reflexivity]. Qed.

Lemma pass_HD1 u l r :
  FR l ([0] *> HD1 u *> r) -->+ FR (put l (G1 u)) ([0] *> r).
Proof. destruct u; unfold HD1,G1,wa,wX,wY,FR,put; execute. Qed.
Lemma pass_HF1 u l r :
  FR l ([0] *> HF1 u *> r) -->+ FR (put l (G1 u)) ([0] *> r).
Proof. destruct u; unfold HF1,G1,wa,wb,wX,wY,FR,put; execute. Qed.
Lemma pass_b l r :
  FR l ([0] *> wb *> r) -->+ FR (put l wY) ([0] *> r).
Proof. unfold wb,wY,FR,put. execute. Qed.
Lemma pass_HD us l r :
  FR l ([0] *> HD us *> r) -->* FR (put l (G us)) ([0] *> r).
Proof.
  revert l r. induction us as [|u us IH]; intros l r.
  - cbn [HD G put]. apply evstep_refl.
  - cbn [HD G]. rewrite Str_app_assoc, put_app.
    apply progress_evstep. eapply progress_evstep_trans; [apply pass_HD1|apply IH].
Qed.
Lemma pass_HF us l r :
  FR l ([0] *> HF us *> r) -->* FR (put l (G us)) ([0] *> r).
Proof.
  revert l r. induction us as [|u us IH]; intros l r.
  - cbn [HF G put]. apply evstep_refl.
  - cbn [HF G]. rewrite Str_app_assoc, put_app.
    apply progress_evstep. eapply progress_evstep_trans; [apply pass_HF1|apply IH].
Qed.
Lemma leave_C r : CE r -->+ FR (put (const 0) [0]) ([0] *> r).
Proof. unfold CE,FR,put. execute. Qed.
Lemma pass_coded d us r : coded d us r -->+ FR (formed d us) ([0] *> r).
Proof.
  unfold coded. eapply progress_evstep_trans; [apply leave_C|].
  destruct d.
  - unfold body,formed,marker. rewrite put_app. apply pass_HD.
  - unfold body,formed,marker. rewrite Str_app_assoc, !put_app.
    apply progress_evstep. eapply progress_evstep_trans; [apply pass_b|apply pass_HF].
Qed.

Lemma D_G1 u l r :
  DL (put l (G1 u)) (wa *> r) -->+ DL l (wa *> HD1 u *> r).
Proof. destruct u; unfold DL,put,G1,HD1,wa,wX,wY; execute. Qed.
Lemma F_G1 u l r :
  FL (put l (G1 u)) ([0;0;0] *> wa *> r) -->+
  FL l ([0;0;0] *> wa *> HF1 u *> r).
Proof. destruct u; unfold FL,put,G1,HF1,wa,wb,wX,wY; execute. Qed.
Lemma D_G us l r :
  DL (put l (G us)) (wa *> r) -->* DL l (wa *> HD us *> r).
Proof.
  revert l r. induction us as [|u us IH]; intros l r.
  - cbn [G HD put]. apply evstep_refl.
  - cbn [G HD]. rewrite put_app, Str_app_assoc.
    eapply evstep_trans; [apply IH|apply progress_evstep; apply D_G1].
Qed.
Lemma F_G us l r :
  FL (put l (G us)) ([0;0;0] *> wa *> r) -->*
  FL l ([0;0;0] *> wa *> HF us *> r).
Proof.
  revert l r. induction us as [|u us IH]; intros l r.
  - cbn [G HF put]. apply evstep_refl.
  - cbn [G HF]. rewrite put_app, Str_app_assoc.
    eapply evstep_trans; [apply IH|apply progress_evstep; apply F_G1].
Qed.
Lemma D_Y l r : DL (put l wY) (wa *> r) -->+ DL l (wY *> wa *> r).
Proof. unfold DL,put,wY,wa. execute. Qed.
Lemma F_Y l r : FL (put l wY) ([0;0;0] *> wa *> r) -->+
  FL l ([0;0;0] *> wa *> wb *> r).
Proof. unfold FL,put,wY,wa,wb. execute. Qed.
Lemma D_empty r : DL (put (const 0) [0]) r -->+ CE r.
Proof.
  unfold DL,put,CE. cbn [rev Str_app]. apply progress_base.
  apply (@step_left tm D E 0 0 (const 0) r). reflexivity.
Qed.
Lemma F_empty r : FL (put (const 0) [0]) ([0;0;0] *> wa *> r) -->+
  CE (wb *> wa *> r).
Proof. unfold FL,put,CE,wa,wb. do 5 step. finish. Qed.

Definition prepend_label d := match d with CD => UA | CF => UT end.
Lemma finish_D d us r :
  DL (formed d us) (wa *> r) -->+ coded CD (prepend_label d::us) r.
Proof.
  unfold formed. rewrite !put_app.
  eapply evstep_progress_trans; [apply D_G|]. destruct d.
  - unfold marker,prepend_label,coded,body,HD,HD1. cbn [put]. apply D_empty.
  - unfold marker. eapply progress_trans; [apply D_Y|].
    unfold prepend_label,coded,body,HD,HD1.
    rewrite Str_app_assoc. apply D_empty.
Qed.
Lemma finish_F d us r :
  FL (formed d us) ([0;0;0] *> wa *> r) -->+
  coded CF (prepend_label d::us) r.
Proof.
  unfold formed. rewrite !put_app.
  eapply evstep_progress_trans; [apply F_G|]. destruct d.
  - unfold marker,prepend_label,coded,body,HF,HF1. cbn [put].
    rewrite Str_app_assoc. apply F_empty.
  - unfold marker. eapply progress_trans; [apply F_Y|].
    unfold prepend_label,coded,body,HF,HF1.
    rewrite !Str_app_assoc. apply F_empty.
Qed.
Definition restored d us (c : config) :=
  exists d' r, c = coded d' (prepend_label d::us) r.
Lemma strong_restores d us c : strong_endpoint (formed d us) c ->
  leads c (restored d us).
Proof.
  intros H; inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply finish_D|].
    exists CD,r. reflexivity.
  - eapply leads_native; [apply progress_evstep; apply finish_F|].
    exists CF,r. reflexivity.
Qed.
Lemma restored_safe d us c : 2 <= List.length us -> restored d us c -> safe c.
Proof. intros H [d' [r ->]]. exists d',(prepend_label d::us),r. split; [cbn; lia|reflexivity]. Qed.

(* Gains *)
Definition nine : list Sym := [1;1;1;1;1;1;1;1;1].
Definition six010 : list Sym := [1;1;1;1;1;1;0;1;0].
Lemma gain_nine l r : FR l ([0] *> nine *> r) -->+
  FR (put l (guard_word [])) ([0] *> r).
Proof. unfold FR,put,nine,guard_word,middle_word,wX,wL. execute. Qed.
Lemma gain_six l r : FR l ([0] *> six010 *> r) -->+
  FR (put l (guard_word [])) ([0] *> r).
Proof. unfold FR,put,six010,guard_word,middle_word,wX,wL. execute. Qed.
Lemma gain_tail d us r t : 2 <= List.length us ->
  (forall l r, FR l ([0] *> t *> r) -->+ FR (put l (guard_word [])) ([0] *> r)) ->
  leads (coded d us (t *> r)) safe.
Proof.
  intros Hlen Ht. eapply leads_follow; [apply pass_coded|].
  eapply leads_follow; [apply Ht|].
  eapply leads_trans; [apply guard_right|]. intros c Hc.
  eapply leads_trans; [apply strong_restores; exact Hc|].
  intros e He. apply leads_here. eapply restored_safe; eauto.
Qed.
Lemma gain_nine_safe d us r : 2 <= List.length us ->
  leads (coded d us (nine *> r)) safe.
Proof. intros. eapply gain_tail; [eassumption|apply gain_nine]. Qed.
Lemma gain_six_safe d us r : 2 <= List.length us ->
  leads (coded d us (six010 *> r)) safe.
Proof. intros. eapply gain_tail; [eassumption|apply gain_six]. Qed.
Lemma gain_Yaa_native r :
  coded CF [UA;UT] ((wY ++ wa ++ wa) *> r) -->+
  FR (put (formed CF [UA;UT]) (guard_word [P11;P11])) ([0;0;1;0] *> r).
Proof.
  unfold coded,body,HF,HF1,CE,formed,marker,G,G1,wa,wb,wY,wX,
    FR,put,guard_word,middle_word,piece_word,wL. execute.
Qed.
Lemma gain_Yaa_safe r : leads (coded CF [UA;UT] ((wY++wa++wa) *> r)) safe.
Proof.
  eapply leads_follow; [apply gain_Yaa_native|].
  eapply leads_trans; [apply guard_right|]. intros c Hc.
  eapply leads_trans; [apply strong_restores; exact Hc|].
  intros e He. apply leads_here. eapply (restored_safe CF [UA;UT] e); [cbn; lia|exact He].
Qed.

(* Finite *)
(* Both lists begin next to the head.  The unspecified right stream is
   retained by every checked transition.  Empty left content is blank. *)
Record finite := Fin { past : list Sym; front : list Sym; state : Q }.
Definition meaning (x : finite) (r : side) : config :=
  state x ;; (past x *> const 0) {{Streams.hd (front x *> r)}} Streams.tl (front x *> r).
Definition finite_step (x : finite) : option finite :=
  match front x with
  | [] => None
  | b::bs =>
    match tm (state x,b) with
    | None => None
    | Some (v,R,s) => Some (Fin (v::past x) bs s)
    | Some (v,L,s) =>
      match past x with
      | [] => Some (Fin [] (0::v::bs) s)
      | a::ls => Some (Fin ls (a::v::bs) s)
      end
    end
  end.
Fixpoint run (n : nat) (x : finite) : option finite :=
  match n with
  | O => Some x
  | S n => match finite_step x with None => None | Some y => run n y end
  end.

Local Opaque tm.
Lemma finite_step_sound x y : finite_step x = Some y ->
  forall r, meaning x r -[tm]-> meaning y r.
Proof.
  destruct x as [ls fs s]. destruct fs as [|b bs].
  { intros He. cbn [finite_step] in He. discriminate He. }
  unfold finite_step,front,past,state.
  destruct (tm (s,b)) as [[[v d] s']|] eqn:H; [|discriminate].
  destruct d.
  - destruct ls as [|a ls]; intros He r; inversion He; subst; cbn [meaning].
    + exact (@step_left tm s s' b v (const 0) (bs *> r) H).
    + exact (@step_left tm s s' b v (a >> (ls *> const 0)) (bs *> r) H).
  - intros He r. inversion He; subst. cbn [meaning].
    exact (@step_right tm s s' b v (ls *> const 0) (bs *> r) H).
Qed.
Local Transparent tm.
Lemma run_sound n x y : run n x = Some y ->
  forall r, multistep tm n (meaning x r) (meaning y r).
Proof.
  revert x y. induction n as [|n IH]; intros x y Hr r.
  - cbn in Hr. inversion Hr; subst. constructor.
  - cbn in Hr. destruct (finite_step x) as [z|] eqn:Hs; [|discriminate].
    econstructor; [apply finite_step_sound; exact Hs|apply IH; exact Hr].
Qed.
Lemma run_progress n x y : run (S n) x = Some y ->
  forall r, meaning x r -->+ meaning y r.
Proof.
  intros Hr r. eapply multistep_progress. apply run_sound. exact Hr.
Qed.


Fixpoint clean (ls : list Sym) : list Sym :=
  match ls with
  | [] => []
  | b::ls => match b, clean ls with 0,[] => [] | _,ys => b::ys end
  end.
Lemma clean_sound ls : clean ls *> const 0 = ls *> const 0.
Proof.
  induction ls as [|b ls IH]; [reflexivity|]. cbn [clean Str_app].
  rewrite <-IH. destruct b; destruct (clean ls); cbn;
    repeat rewrite <-const_unfold; reflexivity.
Qed.
Definition finite_equal x y : bool :=
  if list_eq_dec BB62.eqb_sym (clean (past x)) (clean (past y)) then
  if list_eq_dec BB62.eqb_sym (front x) (front y) then
  if BB62.eqb_q (state x) (state y) then true else false else false else false.
Lemma finite_equal_sound x y : finite_equal x y = true ->
  forall r, meaning x r = meaning y r.
Proof.
  unfold finite_equal.
  destruct (list_eq_dec BB62.eqb_sym (clean (past x)) (clean (past y))); [|discriminate].
  destruct (list_eq_dec BB62.eqb_sym (front x) (front y)); [|discriminate].
  destruct (BB62.eqb_q (state x) (state y)); [|discriminate].
  intros _ r. unfold meaning. rewrite e0,e1.
  rewrite <- (clean_sound (past x)), <- (clean_sound (past y)),e. reflexivity.
Qed.
Definition native_check n x y : bool :=
  match run n x with Some z => finite_equal z y | None => false end.
Lemma native_check_sound n x y : native_check (S n) x y = true ->
  forall r, meaning x r -->+ meaning y r.
Proof.
  unfold native_check. destruct (run (S n) x) as [z|] eqn:Hr; [|discriminate].
  intros He r. rewrite <- (finite_equal_sound _ _ He r).
  apply (run_progress n x z). exact Hr.
Qed.

(* Summaries *)
Inductive return_state := RD | RF | RB.
Definition return_config e l r :=
  match e with RD => DL l r | RF => FL l r | RB => BL l r end.
Definition exits_all : list (return_state * list Sym) :=
  [(RD,[]);(RF,[0;0]);(RB,[0;0])].
Definition exits_00 : list (return_state * list Sym) :=
  [(RD,[1;0;1]);(RD,[1;1;1;0;1]);(RD,[1;0;1;0;0]);(RF,[0;0;0])].
Definition exits_1 : list (return_state * list Sym) :=
  [(RD,[1;1;0;1]);(RD,[0;1;0;0]);(RF,[0;0]);(RB,[0;0])].
Definition returned l es c :=
  exists e p r, In (e,p) es /\ c = return_config e l (p *> r).

Lemma contact_returned l c : contact l c -> returned l exits_all c.
Proof.
  intros H. inversion H; subst; unfold returned,exits_all.
  - exists RD,([]:list Sym),r. split; [cbn; auto|reflexivity].
  - exists RF,[0;0],r. split; [cbn; auto|reflexivity].
  - exists RB,[0;0],r. split; [cbn; auto|reflexivity].
Qed.
Lemma summary_all l r : advances (FR l r) (returned l exits_all).
Proof. eapply advances_trans; [apply right_contacts_advances|].
  intros c H. apply leads_here. apply contact_returned. exact H. Qed.
Lemma L_refined l c : contact (put l wL) c -> leads c (returned l exits_00).
Proof.
  intros H; inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply D_L|].
    exists RF,[0;0;0],r. split; [cbn; auto|reflexivity].
  - eapply leads_native; [apply progress_evstep; apply F_L|].
    exists RD,[1;1;1;0;1],r. split; [cbn; auto|reflexivity].
  - eapply leads_native; [apply progress_evstep; apply B_L|].
    exists RD,[1;0;1;0;0],r. split; [cbn; auto|reflexivity].
Qed.
Lemma summary_00 l r : advances (FR l ([0;0] *> r)) (returned l exits_00).
Proof.
  destruct r as [b r]; destruct b.
  - eapply advances_then; [apply right_000|]. apply leads_here.
    exists RD,[1;0;1],r. split; [cbn; auto|reflexivity].
  - eapply advances_then; [apply right_001|].
    eapply leads_trans; [apply right_contacts|]. intros c H. apply L_refined. exact H.
Qed.
Lemma ten_refined l c : contact (put l [1;0]) c -> leads c (returned l exits_1).
Proof.
  intros H; inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply left_D10|].
    exists RB,[0;0],r. split; [cbn; auto|reflexivity].
  - eapply leads_follow; [apply left_F10|].
    eapply leads_follow; [apply left_D1|]. apply leads_here.
    exists RD,[1;1;0;1],r. split; [cbn; auto|reflexivity].
  - eapply leads_native; [apply progress_evstep; apply left_B10|].
    exists RD,[0;1;0;0],r. split; [cbn; auto|reflexivity].
Qed.
Lemma summary_1 l r : advances (FR l ([1] *> r)) (returned l exits_1).
Proof.
  destruct r as [b r]; destruct b.
  - eapply advances_then; [apply right_10|].
    eapply leads_trans; [apply right_contacts|]. intros c H. apply ten_refined. exact H.
  - eapply advances_then; [apply right_11|]. apply leads_here.
    exists RF,[0;0],r. split; [cbn; auto|reflexivity].
Qed.

Definition exits_DF : list (return_state * list Sym) := [(RD,[]);(RF,[0;0])].
Definition exits_DB : list (return_state * list Sym) := [(RD,[]);(RB,[0;0])].
Definition exits_F : list (return_state * list Sym) := [(RF,[0;0])].
Lemma returned_00_DF l c : returned l exits_00 c -> returned l exits_DF c.
Proof.
  intros [e [p [r [Hin ->]]]]. cbn in Hin.
  destruct Hin as [He|[He|[He|[He|Hfalse]]]]; [inversion He; subst|inversion He; subst|inversion He; subst|inversion He; subst|contradiction].
  - exists RD,([]:list Sym),([1;0;1] *> r). split; [cbn; auto|reflexivity].
  - exists RD,([]:list Sym),([1;1;1;0;1] *> r). split; [cbn; auto|reflexivity].
  - exists RD,([]:list Sym),([1;0;1;0;0] *> r). split; [cbn; auto|reflexivity].
  - exists RF,[0;0],([0] *> r). split; [cbn; auto|reflexivity].
Qed.
Lemma summary_coarse00 l r : advances (FR l ([0;0] *> r)) (returned l exits_DF).
Proof. eapply advances_trans; [apply summary_00|]. intros c H. apply leads_here. apply returned_00_DF. exact H. Qed.
Lemma summary_coarse10 l r : advances (FR l ([1;0] *> r)) (returned l exits_DB).
Proof.
  eapply advances_then; [apply right_10|].
  eapply leads_trans; [apply right_contacts|]. intros c H. inversion H; subst.
  - eapply leads_native; [apply progress_evstep; apply left_D10|].
    exists RB,[0;0],r0. split; [cbn; auto|reflexivity].
  - eapply leads_follow; [apply left_F10|].
    eapply leads_native; [apply progress_evstep; apply left_D1|].
    exists RD,([]:list Sym),([1;1;0;1] *> r0). split; [cbn; auto|reflexivity].
  - eapply leads_native; [apply progress_evstep; apply left_B10|].
    exists RD,([]:list Sym),([0;1;0;0] *> r0). split; [cbn; auto|reflexivity].
Qed.
Lemma summary_coarse11 l r : advances (FR l ([1;1] *> r)) (returned l exits_F).
Proof. eapply advances_then; [apply right_11|]. apply leads_here.
  exists RF,[0;0],r. split; [cbn; auto|reflexivity]. Qed.

(* Closure *)
Definition pair_guard u :=
  match u with UA => [PL] | UT => [P11;P11;PL] end.
Lemma pair_core u : G1 u ++ wX = guard_word (pair_guard u).
Proof. destruct u; reflexivity. Qed.
Lemma pair_contact u v l c : contact (put l (G [u;v])) c ->
  leads c (strong_endpoint l).
Proof.
  destruct v.
  - change (contact (put l (G1 u ++ wX)) c -> leads c (strong_endpoint l)).
    rewrite pair_core. apply (guard_contact (pair_guard u)).
  - change (contact (put l (G1 u ++ (wX ++ wY))) c -> leads c (strong_endpoint l)).
    rewrite app_assoc.
    rewrite pair_core,put_app. intros H. inversion H; subst.
    + eapply leads_trans;
        [apply (stack_contacts (put l (guard_word (pair_guard u)))
          [false;false;false;false] FromD)|].
      intros d Hd. apply (guard_contact (pair_guard u)). exact Hd.
    + eapply leads_trans;
        [apply (stack_contacts (put l (guard_word (pair_guard u)))
          [false;false;false;false] FromF)|].
      intros d Hd. apply (guard_contact (pair_guard u)). exact Hd.
    + eapply leads_trans;
        [apply (stack_contacts (put l (guard_word (pair_guard u)))
          [false;false;false;false] FromB)|].
      intros d Hd. apply (guard_contact (pair_guard u)). exact Hd.
Qed.
Lemma formed_app d us vs : formed d (us++vs) = put (formed d us) (G vs).
Proof. unfold formed. rewrite G_app, !app_assoc, put_app. reflexivity. Qed.
Lemma formed_snoc d us u : formed d (us++[u]) = put (formed d us) (G1 u).
Proof. rewrite formed_app. cbn [G]. rewrite app_nil_r. reflexivity. Qed.
Lemma four_units d a b c e r : advances (coded d [a;b;c;e] r) safe.
Proof.
  eapply advances_then; [apply pass_coded|].
  change (leads (FR (formed d ([a;b]++[c;e])) ([0] *> r)) safe).
  rewrite formed_app.
  eapply leads_trans; [apply right_contacts|]. intros x Hx.
  eapply leads_trans; [exact (pair_contact c e (formed d [a;b]) x Hx)|]. intros y Hy.
  eapply leads_trans; [apply strong_restores; exact Hy|]. intros z Hz.
  apply leads_here. eapply (restored_safe d [a;b] z); [cbn; lia|exact Hz].
Qed.

Lemma D_last u l r : DL (put l (G1 u)) r -->+ DL l (wa *> (match u with UA => [] | UT => wY end) *> r).
Proof. destruct u; unfold DL,put,G1,wX,wY,wa; execute. Qed.
Lemma F_last_A l r : FL (put l (G1 UA)) ([0;0;0] *> r) -->+
  FL l ([0;0;0] *> wa *> r).
Proof. apply F_X000. Qed.
Lemma F_last_T l r : FL (put l (G1 UT)) ([0;0;0] *> r) -->+
  FR (put l (guard_word [P11])) ([0;0] *> r).
Proof. unfold FL,FR,put,G1,guard_word,middle_word,piece_word,wX,wY,wL. execute. Qed.
Lemma single_phase d us u c : phase_contact (put (formed d us) (G1 u)) c ->
  (forall r, leads (BL (put (formed d us) (G1 u)) ([0;0;1;0;1] *> r)) safe) ->
  (forall r, leads (BL (put (formed d us) (G1 u)) ([0;0;1;1;1;0;1] *> r)) safe) ->
  2 <= List.length us -> leads c safe.
Proof.
  intros H H1 H2 Hlen. inversion H; subst.
  - eapply leads_follow; [apply D_last|].
    eapply leads_trans; [apply strong_restores; constructor|].
    intros e He. apply leads_here. eapply restored_safe; eauto.
  - destruct u.
    + eapply leads_follow; [apply F_last_A|].
      eapply leads_trans; [apply strong_restores; constructor|].
      intros e He. apply leads_here. eapply restored_safe; eauto.
    + eapply leads_follow; [apply F_last_T|].
      eapply leads_trans; [apply guard_right|]. intros e He.
      eapply leads_trans; [apply strong_restores; exact He|].
      intros f Hf. apply leads_here. eapply restored_safe; eauto.
  - apply H1.
  - apply H2.
Qed.

Definition B_entries := forall d a b c r,
  leads (BL (formed d [a;b;c]) ([0;0;1;0;1] *> r)) safe /\
  leads (BL (formed d [a;b;c]) ([0;0;1;1;1;0;1] *> r)) safe.
Lemma three_units : B_entries -> forall d a b c r,
  advances (coded d [a;b;c] r) safe.
Proof.
  intros HB d a b c r. eapply advances_then; [apply pass_coded|].
  eapply leads_trans; [apply right_zero_contacts|]. intros x Hx.
  change (phase_contact (formed d ([a;b]++[c])) x) in Hx.
  rewrite formed_snoc in Hx.
  eapply single_phase; [exact Hx| | |cbn; lia].
  - intros r'. rewrite <-(formed_snoc d [a;b] c). exact (proj1 (HB d a b c r')).
  - intros r'. rewrite <-(formed_snoc d [a;b] c). exact (proj2 (HB d a b c r')).
Qed.
Lemma body_prefix d us vs r : coded d (us++vs) r =
  coded d us ((match d with CD => HD vs | CF => HF vs end) *> r).
Proof. destruct d; unfold coded,body; rewrite HD_app || rewrite HF_app;
  rewrite !Str_app_assoc; reflexivity. Qed.
Lemma safe_advances : B_entries -> forall c, safe c -> advances c safe.
Proof.
  intros HB c [d [us [r [Hlen ->]]]].
  destruct us as [|a [|b [|e [|f us]]]]; cbn in Hlen; try lia.
  - apply three_units. exact HB.
  - change (advances (coded d ([a;b;e;f]++us) r) safe).
    rewrite body_prefix. apply four_units.
Qed.
Lemma safe_nonhalt : B_entries -> forall c, safe c -> ~halts tm c.
Proof. intros HB. apply decreasing_halt_budget. apply safe_advances. exact HB. Qed.

(* Certificates *)
Definition right_finite q w := Fin (rev q) w F.
Definition left_finite q s w :=
  match rev q with
  | [] => Fin [] (0::w) s
  | a::ls => Fin ls (a::w) s
  end.
Definition C_finite w := Fin [] ([0;0]++w) E.
Lemma right_meaning q w r : meaning (right_finite q w) r = FR (put (const 0) q) (w *> r).
Proof. reflexivity. Qed.
Lemma left_meaning q s w r : meaning (left_finite q s w) r =
  s ;; Streams.tl (put (const 0) q) {{Streams.hd (put (const 0) q)}} (w *> r).
Proof. unfold left_finite,put. destruct (rev q); reflexivity. Qed.
Lemma C_meaning w r : meaning (C_finite w) r = CE (w *> r).
Proof. reflexivity. Qed.

Inductive terminal :=
| Recovered (d:coding) (us:list unit) (tail:list Sym)
| NineGain (d:coding) (us:list unit) (tail:list Sym)
| SixGain (d:coding) (us:list unit) (tail:list Sym)
| YaaGain (tail:list Sym).
Definition terminal_word t :=
  match t with
  | Recovered d us tail => body d us ++ tail
  | NineGain d us tail => body d us ++ nine ++ tail
  | SixGain d us tail => body d us ++ six010 ++ tail
  | YaaGain tail => body CF [UA;UT] ++ wY ++ wa ++ wa ++ tail
  end.
Definition terminal_finite t := C_finite (terminal_word t).
Definition terminal_valid t :=
  match t with
  | Recovered _ us _ => Nat.leb 3 (List.length us)
  | NineGain _ us _ | SixGain _ us _ => Nat.leb 2 (List.length us)
  | YaaGain _ => true
  end.
Lemma terminal_sound t : terminal_valid t = true ->
  forall r, leads (meaning (terminal_finite t) r) safe.
Proof.
  destruct t; cbn [terminal_valid]; intros H r; unfold terminal_finite;
    rewrite C_meaning; cbn [terminal_word].
  - apply Nat.leb_le in H. rewrite Str_app_assoc.
    apply leads_here. exists d,us,(tail *> r). split; [exact H|reflexivity].
  - apply Nat.leb_le in H. rewrite !Str_app_assoc. apply gain_nine_safe. exact H.
  - apply Nat.leb_le in H. rewrite !Str_app_assoc. apply gain_six_safe. exact H.
  - rewrite !Str_app_assoc. apply gain_Yaa_safe.
Qed.

Fixpoint stack_word (s:list bool) : list Sym :=
  match s with [] => [] | b::s => stack_word s ++ chunk b end.
Lemma stack_word_side l s : stack_side l s = put l (stack_word s).
Proof.
  induction s as [|b s IH]; [reflexivity|]. cbn [stack_side stack_word].
  rewrite IH,put_app. reflexivity.
Qed.
Lemma protected_right base ps s r :
  leads (FR (put (const 0) ((base++guard_word ps)++stack_word s)) r)
    (strong_endpoint (put (const 0) base)).
Proof.
  rewrite !put_app, <-stack_word_side.
  eapply leads_trans; [apply (stack_contacts _ s GoRight r)|].
  intros c Hc. apply (guard_contact ps). exact Hc.
Qed.

Record guard_certificate := GuardCert {
  guard_base : list Sym;
  guard_pieces : list middle_piece;
  guard_stack : list bool;
  guard_D_steps : nat;
  guard_D_terminal : terminal;
  guard_F_steps : nat;
  guard_F_terminal : terminal
}.
Definition guard_full g :=
  (guard_base g ++ guard_word (guard_pieces g)) ++ stack_word (guard_stack g).
Definition guard_valid g : Prop :=
  terminal_valid (guard_D_terminal g) = true /\
  terminal_valid (guard_F_terminal g) = true /\
  native_check (S (guard_D_steps g))
    (left_finite (guard_base g) D wa) (terminal_finite (guard_D_terminal g)) = true /\
  native_check (S (guard_F_steps g))
    (left_finite (guard_base g) F ([0;0;0]++wa))
    (terminal_finite (guard_F_terminal g)) = true.
Lemma guard_sound g : guard_valid g -> forall r,
  leads (FR (put (const 0) (guard_full g)) r) safe.
Proof.
  intros [HD [HF [ND NF]]] r. unfold guard_full.
  eapply leads_trans; [apply protected_right|]. intros c Hc. inversion Hc; subst.
  - eapply leads_follow.
    + pose proof (native_check_sound (guard_D_steps g) _ _ ND r0) as Hnative.
      rewrite left_meaning in Hnative. exact Hnative.
    + apply terminal_sound. exact HD.
  - eapply leads_follow.
    + pose proof (native_check_sound (guard_F_steps g) _ _ NF r0) as Hnative.
      rewrite left_meaning in Hnative. exact Hnative.
    + apply terminal_sound. exact HF.
Qed.

(* Graph *)
Open Scope bool_scope.

Inductive summary := AllCases | Cases00 | Cases1 | Coarse00 | Coarse10 | Coarse11.
Definition summary_exits s :=
  match s with
  | AllCases => exits_all | Cases00 => exits_00 | Cases1 => exits_1
  | Coarse00 => exits_DF | Coarse10 => exits_DB | Coarse11 => exits_F
  end.
Definition sym_list_equal u v := if list_eq_dec BB62.eqb_sym u v then true else false.
Definition summary_valid s w :=
  match s with
  | AllCases => true
  | Cases00 => sym_list_equal w [0;0]
  | Cases1 => sym_list_equal w [1]
  | Coarse00 => sym_list_equal (firstn 2 w) [0;0]
  | Coarse10 => sym_list_equal (firstn 2 w) [1;0]
  | Coarse11 => sym_list_equal (firstn 2 w) [1;1]
  end.
Lemma sym_list_equal_sound u v : sym_list_equal u v = true -> u=v.
Proof. unfold sym_list_equal. destruct (list_eq_dec BB62.eqb_sym u v); congruence. Qed.
Lemma summary_sound s w : summary_valid s w = true -> forall l r,
  advances (FR l (w *> r)) (returned l (summary_exits s)).
Proof.
  destruct s; cbn [summary_valid summary_exits]; intros H l r.
  - apply summary_all.
  - apply sym_list_equal_sound in H. subst. apply summary_00.
  - apply sym_list_equal_sound in H. subst. apply summary_1.
  - apply sym_list_equal_sound in H.
    destruct w as [|a [|b w]]; cbn in H; try discriminate.
    inversion H; subst. apply summary_coarse00.
  - apply sym_list_equal_sound in H.
    destruct w as [|a [|b w]]; cbn in H; try discriminate.
    inversion H; subst. apply summary_coarse10.
  - apply sym_list_equal_sound in H.
    destruct w as [|a [|b w]]; cbn in H; try discriminate.
    inversion H; subst. apply summary_coarse11.
Qed.
Definition ret_Q s := match s with RD => D | RF => F | RB => B end.
Definition return_state_equal a b :=
  match a,b with RD,RD | RF,RF | RB,RB => true | _,_ => false end.
Lemma return_state_equal_sound a b : return_state_equal a b = true -> a=b.
Proof. destruct a,b; cbn; congruence. Qed.
Record branch := Branch {
  branch_state : return_state;
  branch_prefix : list Sym;
  branch_steps : nat;
  branch_target : nat
}.
Definition branch_matches (e:return_state*list Sym) b :=
  andb (return_state_equal (fst e) (branch_state b))
       (sym_list_equal (snd e) (branch_prefix b)).
Definition covers s bs :=
  forallb (fun e => existsb (branch_matches e) bs) (summary_exits s).
Inductive action :=
| ActNative (steps:nat) (target:nat)
| ActInclude (target:nat) (prepend:list Sym)
| ActEnd (t:terminal)
| ActProtect (g:guard_certificate) (w:list Sym)
| ActReturn (q w:list Sym) (s:summary) (bs:list branch).
Record row := Row { row_finite : finite; row_rank : nat; row_action : action }.
Definition graph := list row.
Definition append_front p x := Fin (past x) (front x ++ p) (state x).
Lemma append_front_sound p x r : meaning (append_front p x) r = meaning x (p *> r).
Proof. unfold meaning,append_front. cbn. rewrite Str_app_assoc. reflexivity. Qed.
Definition branch_valid g q b :=
  match nth_error g (branch_target b) with
  | None => false
  | Some t => native_check (S (branch_steps b))
      (left_finite q (ret_Q (branch_state b)) (branch_prefix b)) (row_finite t)
  end.
Definition guard_check g :=
  andb (terminal_valid (guard_D_terminal g))
  (andb (terminal_valid (guard_F_terminal g))
  (andb (native_check (S (guard_D_steps g))
    (left_finite (guard_base g) D wa) (terminal_finite (guard_D_terminal g)))
    (native_check (S (guard_F_steps g))
    (left_finite (guard_base g) F ([0;0;0]++wa)) (terminal_finite (guard_F_terminal g))))).
Lemma guard_check_sound g : guard_check g = true -> guard_valid g.
Proof. unfold guard_check,guard_valid. repeat rewrite andb_true_iff. tauto. Qed.
Definition row_check (g:graph) (x:row) :=
  match row_action x with
  | ActNative n j => match nth_error g j with
    | Some y => native_check (S n) (row_finite x) (row_finite y) | None => false end
  | ActInclude j p => match nth_error g j with
    | Some y => andb (Nat.ltb (row_rank y) (row_rank x))
      (finite_equal (row_finite x) (append_front p (row_finite y)))
    | None => false end
  | ActEnd t => andb (terminal_valid t) (finite_equal (row_finite x) (terminal_finite t))
  | ActProtect gc w => andb (guard_check gc)
      (finite_equal (row_finite x) (right_finite (guard_full gc) w))
  | ActReturn q w s bs => andb (finite_equal (row_finite x) (right_finite q w))
      (andb (summary_valid s w) (andb (covers s bs) (forallb (branch_valid g q) bs)))
  end.

Lemma covered_branch s bs e : covers s bs = true -> In e (summary_exits s) ->
  exists b, In b bs /\ fst e = branch_state b /\ snd e = branch_prefix b.
Proof.
  intros HC Hin. unfold covers in HC. apply forallb_forall with (x:=e) in HC; [|exact Hin].
  apply existsb_exists in HC. destruct HC as [b [Hb He]].
  unfold branch_matches in He. apply andb_true_iff in He.
  destruct He as [H1 H2]. apply return_state_equal_sound in H1.
  apply sym_list_equal_sound in H2. exists b. auto.
Qed.

Lemma graph_sound (g:graph) : forallb (row_check g) g = true ->
  forall x, In x g -> forall r, leads (meaning (row_finite x) r) safe.
Proof.
  intros HG x Hx r n Hn. revert x Hx r Hn.
  induction n as [n IHn] using strong_induction.
  assert (HR : forall k x, row_rank x = k -> In x g -> forall r,
    halts_in tm (meaning (row_finite x) r) n ->
    exists m c, m <= n /\ safe c /\ halts_in tm c m).
  {
    intro k. induction k as [k IHk] using strong_induction.
    intros x Hrank Hx r Hn.
    pose proof HG as HX. apply forallb_forall with (x:=x) in HX; [|exact Hx].
    unfold row_check in HX. destruct (row_action x) as [steps j|j p|t|gc w|q w s bs] eqn:HA.
    - destruct (nth_error g j) as [y|] eqn:Hy; [|discriminate].
      pose proof (native_check_sound _ _ _ HX r) as Hp.
      destruct (reduce_progress _ _ _ Hp Hn) as [m [Hmn Hm]].
      destruct (IHn m Hmn y (nth_error_In _ _ Hy) r Hm) as [a [c [Ham Hrest]]].
      exists a,c. split; [lia|exact Hrest].
    - destruct (nth_error g j) as [y|] eqn:Hy; [|discriminate].
      apply andb_true_iff in HX. destruct HX as [Hlt He]. apply Nat.ltb_lt in Hlt.
      pose proof (finite_equal_sound _ _ He r) as Hsame.
      rewrite append_front_sound in Hsame. rewrite Hsame in Hn.
      eapply IHk; [rewrite <-Hrank; exact Hlt|reflexivity|eapply nth_error_In; exact Hy|exact Hn].
    - apply andb_true_iff in HX. destruct HX as [Ht He].
      rewrite (finite_equal_sound _ _ He r) in Hn.
      exact (terminal_sound t Ht r n Hn).
    - apply andb_true_iff in HX. destruct HX as [Hgc He].
      rewrite (finite_equal_sound _ _ He r),right_meaning in Hn.
      exact (guard_sound gc (guard_check_sound gc Hgc) (w *> r) n Hn).
    - apply andb_true_iff in HX. destruct HX as [He HX].
      apply andb_true_iff in HX. destruct HX as [Hs HX].
      apply andb_true_iff in HX. destruct HX as [HC HB].
      rewrite (finite_equal_sound _ _ He r),right_meaning in Hn.
      destruct (summary_sound s w Hs (put (const 0) q) r n Hn)
        as [m [c [Hmn [[e [p [r' [Hin ->]]]] Hm]]]].
      destruct (covered_branch s bs (e,p) HC Hin) as [b [Hb [Hs' Hp]]]. cbn in Hs',Hp. subst e p.
      apply forallb_forall with (x:=b) in HB; [|exact Hb].
      unfold branch_valid in HB.
      destruct (nth_error g (branch_target b)) as [y|] eqn:Hy; [|discriminate].
      assert (Hreturn : return_config (branch_state b) (put (const 0) q)
        (branch_prefix b *> r') -->+ meaning (row_finite y) r').
      { pose proof (native_check_sound (branch_steps b) _ _ HB r') as Hnative.
        rewrite left_meaning in Hnative. destruct (branch_state b); exact Hnative. }
      destruct (reduce_progress _ _ _ Hreturn Hm) as [a [Ham Ha]].
      destruct (IHn a ltac:(lia) y (nth_error_In _ _ Hy) r' Ha) as [z [d [Hza Hrest]]].
      exists z,d. split; [lia|exact Hrest].
  }
  intros x Hx r Hn. eapply HR; [reflexivity|exact Hx|exact Hn].
Qed.

Definition source_check g x :=
  existsb (fun y => finite_equal x (row_finite y)) g.
Definition entry_finite d a b c w :=
  left_finite ([0] ++ marker d ++ G [a;b;c]) B w.
Definition entries_check g :=
  forallb (fun d => forallb (fun a => forallb (fun b => forallb (fun c =>
    andb (source_check g (entry_finite d a b c [0;0;1;0;1]))
         (source_check g (entry_finite d a b c [0;0;1;1;1;0;1])))
    [UA;UT]) [UA;UT]) [UA;UT]) [CD;CF].
Definition complete_check g := andb (forallb (row_check g) g) (entries_check g).

Lemma checked_source g x : forallb (row_check g) g = true ->
  source_check g x = true -> forall r, leads (meaning x r) safe.
Proof.
  intros Hg Hx r. apply existsb_exists in Hx. destruct Hx as [y [Hy He]].
  rewrite (finite_equal_sound _ _ He r). apply graph_sound with g; assumption.
Qed.

Lemma checked_entries g : complete_check g = true -> B_entries.
Proof.
  unfold complete_check, entries_check. rewrite andb_true_iff.
  intros [Hg He] d a b c r.
  apply forallb_forall with (x:=d) in He; [|destruct d; cbn; auto].
  apply forallb_forall with (x:=a) in He; [|destruct a; cbn; auto].
  apply forallb_forall with (x:=b) in He; [|destruct b; cbn; auto].
  apply forallb_forall with (x:=c) in He; [|destruct c; cbn; auto].
  apply andb_true_iff in He. destruct He as [H1 H2]. split.
  - pose proof (checked_source _ _ Hg H1 r) as H.
    unfold entry_finite in H. rewrite left_meaning in H. exact H.
  - pose proof (checked_source _ _ Hg H2 r) as H.
    unfold entry_finite in H. rewrite left_meaning in H. exact H.
Qed.

Lemma bootstrap : c0 -->* coded CD [UA;UT;UA;UA]
  ([1;0;1;0;0;1;1;0;1;0;1;1;0;1;0;0;1;0;1] *> const 0).
Proof. unfold coded,body,HD,HD1,CE,wa,wY. solve_init. Qed.

Lemma complete_check_nonhalt g : complete_check g = true -> ~halts tm c0.
Proof.
  intros H. eapply multistep_nonhalt; [exact bootstrap|].
  apply safe_nonhalt; [exact (checked_entries g H)|].
  exists CD,[UA;UT;UA;UA],([1;0;1;0;0;1;1;0;1;0;1;1;0;1;0;0;1;0;1] *> const 0).
  split; [cbn; lia|reflexivity].
Qed.

(* Certificate search is untrusted: complete_check rechecks every row,
   every return-summary branch, and all 32 entry configurations. *)
Definition normalize x := Fin (clean (past x)) (front x) (state x).
Definition next x := option_map normalize (finite_step x).
Fixpoint remove_prefix (p w : list Sym) : option (list Sym) :=
  match p,w with
  | [],_ => Some w
  | a::p,b::w => if BB62.eqb_sym a b then remove_prefix p w else None
  | _,_ => None
  end.
Fixpoint parse_units (fuel : nat) d w : list unit * list Sym :=
  match fuel with
  | O => ([],w)
  | S n =>
    match remove_prefix (match d with CD => wY++wa | CF => wa++wb end) w with
    | Some r => let '(us,t) := parse_units n d r in (UT::us,t)
    | None => match remove_prefix wa w with
      | Some r => let '(us,t) := parse_units n d r in (UA::us,t)
      | None => ([],w)
      end
    end
  end.
Definition end_payload d w :=
  let '(us,t) := parse_units (List.length w) d w in
  if Nat.leb 3 (List.length us) then Some (Recovered d us t) else
  if Nat.leb 2 (List.length us) then
    match remove_prefix nine t with
    | Some r => Some (NineGain d us r)
    | None => match remove_prefix six010 t with
      | Some r => Some (SixGain d us r)
      | None => match d,us,remove_prefix (wY++wa++wa) t with
        | CF,[UA;UT],Some r => Some (YaaGain r) | _,_,_ => None end
      end
    end
  else None.
Definition end_at x :=
  match past x,state x,front x with
  | [],E,0::0::w => match remove_prefix wb w with
    | Some r => end_payload CF r | None => end_payload CD w end
  | _,_,_ => None
  end.
Definition is_F x := match state x with F => true | _ => false end.
Definition cut x :=
  match state x,front x with
  | F,[] | F,[_] | F,[0;0] => true
  | E,0::0::_ => match past x with [] => true | _ => false end
  | _,_ => false
  end.
Fixpoint finish (fuel count : nat) x : option (nat * terminal) :=
  match fuel with
  | O => None
  | S n => match end_at x,count with
    | Some t,S k => Some (k,t)
    | _,_ => match next x with Some y => finish n (S count) y | None => None end
    end
  end.
Fixpoint parse_stack (fuel : nat) w acc :=
  match w,fuel with
  | [],_ => Some acc
  | _,O => None
  | 1::0::w,S n => parse_stack n w (true::acc)
  | 1::w,S n => parse_stack n w (false::acc)
  | _,_ => None
  end.
Definition try_guard base ps extra :=
  match parse_stack (List.length extra) extra [] with
  | None => None
  | Some bs =>
    match finish 513 0 (normalize (left_finite base D wa)),
          finish 513 0 (normalize (left_finite base F ([0;0;0]++wa))) with
    | Some (nd,td),Some (nf,tf) => Some (GuardCert base ps bs nd td nf tf)
    | _,_ => None
    end
  end.
Fixpoint guard_pieces_search (fuel : nat) base ps w :=
  match fuel with
  | O => None
  | S n => match remove_prefix wL w with
    | Some r => match try_guard base ps r with
      | Some g => Some g
      | None => guard_pieces_search n base (ps++[PL]) r
      end
    | None => match remove_prefix [1;1] w with
      | Some r => guard_pieces_search n base (ps++[P11]) r
      | None => None
      end
    end
  end.
Fixpoint guard_base_search (fuel : nat) base w :=
  match fuel,w with
  | O,_ | _,[] => None
  | S n,a::r =>
    let candidate := match remove_prefix wX w with
      | Some tail => guard_pieces_search (List.length tail) (fast_rev base) [] tail
      | None => None end in
    match candidate with Some g => Some g
    | None => guard_base_search n (a::base) r end
  end.
Definition protect_at x :=
  if is_F x then guard_base_search (List.length (past x)) [0] (fast_rev (past x))
  else None.

(* A trie shares the common (state,past) prefix and stores front-prefix IDs.
   No completeness or data-structure theorem is needed by the checker. *)
Inductive trie := Empty | Node (value : option nat) (lo hi : trie).
Fixpoint descend key t :=
  match key,t with
  | [],_ => t
  | 0::k,Node _ l _ => descend k l
  | 1::k,Node _ _ r => descend k r
  | _,_ => Empty
  end.
Definition value t := match t with Empty => None | Node v _ _ => v end.
Fixpoint insert key v t :=
  let '(old,l,r) := match t with Empty => (None,Empty,Empty) | Node a b c => (a,b,c) end in
  match key with
  | [] => Node (Some v) l r
  | 0::k => Node old (insert k v l) r
  | 1::k => Node old l (insert k v r)
  end.
Definition state_key q : list Sym :=
  match q with A => [0;0;0] | B => [0;0;1] | C => [0;1;0]
  | D => [0;1;1] | E => [1;0;0] | F => [1;0;1] end.
Definition past_key x := state_key (state x) ++
  List.flat_map (fun b : Sym => [0;b]) (past x) ++ [1;1].
Definition full_key x := past_key x ++ front x.
Fixpoint shorter w t : option (nat * list Sym) :=
  match w,t with
  | [],_ | _,Empty => None
  | _,Node (Some j) _ _ => Some (j,w)
  | 0::w,Node None l _ => shorter w l
  | 1::w,Node None _ r => shorter w r
  end.
Record search := Search {
  ids : trie; fresh : nat; todo : list finite; back : list finite; done_rev : graph
}.
Definition intern x s :=
  let x := normalize x in
  match value (descend (full_key x) (ids s)) with
  | Some j => (j,s)
  | None => (fresh s, Search (insert (full_key x) (fresh s) (ids s))
      (S (fresh s)) (todo s) (x::back s) (done_rev s))
  end.
Fixpoint seek (fuel count : nat) x :=
  match fuel with
  | O => None
  | S n => match next x with
    | None => None
    | Some y =>
      let stop := match end_at y with Some _ => true | None =>
        if cut y then true else match protect_at y with Some _ => true | None => false end end in
      if stop then Some (count,y) else seek n (S count) y
    end
  end.
Definition walk x s :=
  match seek 1024 0 x with
  | Some (n,y) => let '(j,s) := intern y s in Some (n,j,s)
  | None => None
  end.
Definition pick_summary w :=
  match w with [0;0] => Cases00 | [1] => Cases1 | _ => AllCases end.
Fixpoint branches q es s : option (list branch * search) :=
  match es with
  | [] => Some ([],s)
  | (st,w)::es =>
    match walk (normalize (left_finite q (ret_Q st) w)) s with
    | None => None
    | Some (n,j,s) => match branches q es s with
      | None => None
      | Some (bs,s) => Some (Branch st w n j::bs,s)
      end
    end
  end.
Definition classify x s : option (action * search) :=
  match end_at x with Some t => Some (ActEnd t,s) | None =>
  match protect_at x with Some g => Some (ActProtect g (front x),s) | None =>
  match shorter (front x) (descend (past_key x) (ids s)) with
  | Some (j,p) => Some (ActInclude j p,s)
  | None => if andb (is_F x) (cut x) then
      let q := 0::fast_rev (past x) in
      let sm := pick_summary (front x) in
      match branches q (summary_exits sm) s with
      | Some (bs,s) => Some (ActReturn q (front x) sm bs,s)
      | None => None end
    else match walk x s with Some (n,j,s) => Some (ActNative n j,s) | None => None end
  end end end.
Definition pop s :=
  let qs := match todo s with [] => fast_rev (back s) | xs => xs end in
  let bs := match todo s with [] => [] | _ => back s end in
  match qs with [] => None
  | x::xs => Some (x,Search (ids s) (fresh s) xs bs (done_rev s)) end.
Fixpoint build (fuel : nat) s : option graph :=
  match pop s with
  | None => Some (fast_rev (done_rev s))
  | Some (x,s) => match fuel with
    | O => None
    | S n => match classify x s with
      | None => None
      | Some (a,s) => build n (Search (ids s) (fresh s) (todo s) (back s)
          (Row x (List.length (front x)) a::done_rev s))
      end
    end
  end.
Definition seeds := List.flat_map (fun d => List.flat_map (fun a =>
  List.flat_map (fun b => List.flat_map (fun c =>
    [entry_finite d a b c [0;0;1;0;1];entry_finite d a b c [0;0;1;1;1;0;1]])
      [UA;UT]) [UA;UT]) [UA;UT]) [CD;CF].
Definition initial := List.fold_left (fun s x => snd (intern x s)) seeds
  (Search Empty 0 [] [] []).
Definition generated : option graph := build 8000 initial.
Definition extract (g : option graph) : graph := match g with Some x => x | None => [] end.
Definition certificate : graph := extract generated.

Lemma certificate_checked : complete_check certificate = true.
Proof. vm_check_eq. Qed.

Theorem nonhalt: ~halts tm c0.
Proof. exact (complete_check_nonhalt certificate certificate_checked). Qed.

Print Assumptions nonhalt.
End TM1.

(* The same transition graph with a different blank-tape entry state. *)
Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC1RA_1LD0LA_---0LE_0LF1LE_0RA0LC").

Definition rename q := match q with
  | A => F | B => A | C => B | D => C | E => D | F => E end.
Lemma perm : Perm tm TM1.tm rename.
Proof.
  split.
  - intros [] []; cbn; congruence.
  - intros [] [] w d q H; inversion H; reflexivity.
Qed.

Lemma init : (F;; tape0) -[TM1.tm]->*
  TM1.coded TM1.CD [TM1.UA;TM1.UT;TM1.UT] ([1;0;1] *> 0inf).
Proof.
  eapply without_counter with (n:=406).
  apply multistep_c_spec; vm_compute; simpl_tape; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  apply (perm_nonhalt tm TM1.tm rename A tape0 perm).
  eapply multistep_nonhalt; [apply init|].
  apply TM1.safe_nonhalt; [exact (TM1.checked_entries _ TM1.certificate_checked)|].
  exists TM1.CD,[TM1.UA;TM1.UT;TM1.UT],([1;0;1] *> 0inf).
  split; [cbn; lia|reflexivity].
Qed.

Print Assumptions nonhalt.
End TM2.
