(* BB(2,5): self-similar rectangle growth, machine 60. *)
From BusyCoq Require Import Individual25.
From Coq Require Import String List Lia PeanoNat.
Import ListNotations.
Open Scope sym_scope.

(* New finite-rectangle proof, package03 only. The local rectangle language
   records boundary visits; every transition is checked against this tm. *)
Module TM60.
Definition tm := Eval compute in (TM_from_str "1RB2LA3LB4LB---_0LA4LB3RA4LA0RB").
Definition mtm := flip tm.

Inductive letter := a | b | c.
Definition ent x : Q := match x with a | c=>A | b=>B end.
Definition ext x : Q := match x with a | b=>B | c=>A end.
Definition code x : DH0*DH0 := ((ent x,[]),(ext x,[])).
Definition codes := map code.

Inductive Visit : Sym -> Q -> list letter -> Q -> Sym -> Prop :=
| visit_right s X t Y : tm(X,s)=Some(t,R,Y) -> Visit s X [] Y t
| visit_left s X w m M Y t : tm(X,s)=Some(w,L,ent m) ->
    Visit w (ext m) M Y t -> Visit s X (m::M) Y t.
Inductive Cell : Sym -> list letter -> list letter -> Sym -> Prop :=
| cell_nil s : Cell s [] [] s
| cell_cons s r M1 s1 R M2 t : Visit s (ent r) M1 (ext r) s1 ->
    Cell s1 R M2 t -> Cell s (r::R) (M1++M2) t.
Inductive Rect : list Sym -> list letter -> list letter -> list Sym -> Prop :=
| rect_nil R : Rect [] R R []
| rect_cons s R M t S L T : Cell s R M t -> Rect S M L T ->
    Rect (s::S) R L (t::T).

Lemma cell_single s r L t : Visit s (ent r) L (ext r) t -> Cell s [r] L t.
Proof. intro H; rewrite <- (app_nil_r L); econstructor; [exact H|constructor]. Qed.
Lemma cell_append s t u R1 L1 R2 L2 :
  Cell s R1 L1 t -> Cell t R2 L2 u -> Cell s (R1++R2) (L1++L2) u.
Proof.
  intros H; induction H; intro H2; [exact H2|].
  cbn; rewrite <-app_assoc; econstructor; eauto.
Qed.
Lemma cell_split R1 : forall s u R2 L, Cell s (R1++R2) L u ->
  exists L1 L2 t, L=L1++L2 /\ Cell s R1 L1 t /\ Cell t R2 L2 u.
Proof.
  induction R1 as [|r R1 IH]; intros s u R2 L H.
  - exists ([]:list letter),L,s; split; [reflexivity|]; split; [constructor|exact H].
  - inversion H; subst.
    match goal with HC:Cell _ (R1++R2) _ _ |- _ =>
      destruct(IH _ _ _ _ HC) as [L1 [L2 [t [EL [H1 H2]]]]] end.
    subst; do 3 eexists; split; [rewrite app_assoc; reflexivity|].
    split; [econstructor; eassumption|exact H2].
Qed.
Lemma rect_length S R L T : Rect S R L T -> length T=length S.
Proof. intro H; induction H; cbn; congruence. Qed.
Lemma rect_append S T U R1 L1 R2 L2 :
  Rect S R1 L1 T -> Rect T R2 L2 U -> Rect S (R1++R2) (L1++L2) U.
Proof.
  intros H; revert R2 L2 U; induction H; intros R2 L2 U H2; inversion H2; subst.
  - constructor.
  - econstructor; [eapply cell_append; eassumption|eauto].
Qed.
Lemma rect_split S : forall R1 R2 L U, Rect S (R1++R2) L U ->
  exists L1 L2 T, L=L1++L2 /\ Rect S R1 L1 T /\ Rect T R2 L2 U.
Proof.
  induction S as [|s S IH]; intros R1 R2 L U H; inversion H; subst.
  - exists R1,R2,([]:list Sym); split; [reflexivity|]; split; constructor.
  - match goal with HC:Cell _ (R1++R2) _ _ |- _ =>
      destruct(cell_split R1 _ _ _ _ HC) as [M1 [M2 [midS [EM [HMfirst HMrest]]]]] end.
    subst.
    match goal with HR:Rect S (M1++M2) _ _ |- _ =>
      destruct(IH _ _ _ _ HR) as [L1 [L2 [midT [EL [HLfirst HLrest]]]]] end.
    subst; exists L1,L2,(midS::midT); split; [reflexivity|]; split; econstructor; eassumption.
Qed.
Lemma rect_space S S' T T' R M L :
  Rect S R M S' -> Rect T M L T' -> Rect (S++T) R L (S'++T').
Proof. intros H; induction H; intro H2; [exact H2|cbn; econstructor; eauto]. Qed.
Lemma rect_cut S1 : forall S2 U R L, Rect (S1++S2) R L U ->
  exists M U1 U2, U=U1++U2 /\ length U1=length S1 /\
    Rect S1 R M U1 /\ Rect S2 M L U2.
Proof.
  induction S1 as [|s S1 IH]; intros S2 U R L H.
  - exists R,([]:list Sym),U; split; [reflexivity|]; split; [reflexivity|]; split; [constructor|exact H].
  - inversion H; subst.
    match goal with HR:Rect (S1++S2) _ _ _ |- _ =>
      destruct(IH _ _ _ _ HR) as [midM [U1 [U2 [EU [HL [Hcut1 Hcut2]]]]]] end.
    subst; eexists _,(_::U1),U2; split; [reflexivity|]; split; [cbn; congruence|].
    split; [econstructor; eassumption|exact Hcut2].
Qed.
Lemma rect_one s t R L : Cell s R L t -> Rect [s] R L [t].
Proof. intro H; econstructor; [exact H|constructor]. Qed.
Lemma cell_nilR s L t : Cell s [] L t -> L=[] /\ t=s.
Proof. intro H; inversion H; subst; auto. Qed.

(* Direct BusyCoq semantics: no copied integer tape or oracle machine. *)
Lemma visit_right_run s X t Y : tm(X,s)=Some(t,R,Y) -> forall l r,
  l {{X}}> (s>>r) -[mtm]->+ l <{{Y}} (t>>r).
Proof. destruct X,s; cbn[tm]; intro H; inversion H; subst; intros; unfold mtm; execute. Qed.
Lemma visit_left_run s X t Y : tm(X,s)=Some(t,L,Y) -> forall l r,
  l {{X}}> (s>>r) -[mtm]->+ (l<<t) {{Y}}> r.
Proof. destruct X,s; cbn[tm]; intro H; inversion H; subst; intros; unfold mtm; execute. Qed.
Lemma visit_sound s X M Y t : Visit s X M Y t -> forall r r',
  sideRLs mtm (codes M) r r' -> sideRL mtm (X,[]) (Y,[]) (s>>r) (t>>r').
Proof.
  intro H; induction H; intros r r' HS l; unfold to_DH_config; cbn.
  - inversion HS; subst; apply visit_right_run; exact H.
  - cbn[codes map code] in HS; inversion HS; subst.
    eapply progress_trans; [apply visit_left_run; exact H|].
    match goal with HR:sideRL mtm _ _ _ _ |- _ =>
      eapply progress_trans; [apply HR|] end.
    exact (IHVisit _ _ H7 l).
Qed.
Lemma cell_sound s R L t : Cell s R L t -> forall r r',
  sideRLs mtm (codes L) r r' -> sideRLs mtm (codes R) (s>>r) (t>>r').
Proof.
  intro H; induction H; intros r0 r' HS.
  - inversion HS; subst; constructor.
  - unfold codes in HS; rewrite map_app in HS.
    destruct(sideRLs_split HS) as [r1 [H1 H2]].
    cbn[codes map code]; econstructor.
    + eapply visit_sound; eassumption.
    + apply IHCell; exact H2.
Qed.
Lemma rect_sound S R L T : Rect S R L T -> forall r r',
  sideRLs mtm (codes L) r r' -> sideRLs mtm (codes R) (S*>r) (T*>r').
Proof.
  intro H; induction H; intros r r' HS; [exact HS|].
  cbn[Str_app]; eapply cell_sound; [exact H|apply IHRect; exact HS].
Qed.

(* A finite boundary history either completes some visits or supplies a
   long real execution during the next visit. This is the machine-generic
   bounded interface of LongN, re-proved here for Individual25 only. *)
Inductive Partial (machine:TM) : list(DH0*DH0) -> side -> nat -> Prop :=
| partial_done r : Partial machine [] r O
| partial_pass h1 h2 hs r r' n : sideRL machine h1 h2 r r' ->
    Partial machine hs r' n -> Partial machine ((h1,h2)::hs) r n
| partial_run h1 h2 hs r n :
    (forall l, exists k c', (n<=k)%nat /\
      l {{{(h1,R)}}} r -[machine]->> k / c') ->
    Partial machine ((h1,h2)::hs) r n.
Lemma partial_zero machine hs r : Partial machine hs r O.
Proof.
  destruct hs as [|[h1 h2] hs]; [constructor|].
  apply partial_run; intro l; exists O,(l {{{(h1,R)}}} r); split; [lia|constructor].
Qed.
Lemma partial_nil machine r n : Partial machine [] r n -> n=O.
Proof. intro H; inversion H; reflexivity. Qed.
Lemma partial_mono machine hs r n : Partial machine hs r n ->
  forall m, (m<=n)%nat -> Partial machine hs r m.
Proof.
  intro H; induction H; intros m HM.
  - assert(m=O) by lia; subst; constructor.
  - eapply partial_pass; [exact H|apply IHPartial; exact HM].
  - apply partial_run; intro l; destruct(H l) as [k [c' [HK HR]]].
    exists k,c'; split; [lia|exact HR].
Qed.
Lemma partial_prefix machine hs r n : Partial machine hs r n -> forall hs',
  Partial machine (hs++hs') r n.
Proof.
  intro H; induction H; intro hs'; cbn.
  - apply partial_zero.
  - eapply partial_pass; eauto.
  - apply partial_run; exact H.
Qed.
Lemma partial_split machine hs1 : forall hs2 r n,
  Partial machine (hs1++hs2) r n -> Partial machine hs1 r n \/
  exists r', sideRLs machine hs1 r r' /\ Partial machine hs2 r' n.
Proof.
  induction hs1 as [|[h1 h2] hs1 IH]; intros hs2 r n H.
  - right; exists r; split; [constructor|exact H].
  - inversion H; subst.
    + match goal with HP:Partial machine (hs1++hs2) _ _ |- _ =>
        destruct(IH _ _ _ HP) as [HF|[r'' [HS HF]]] end.
      * left; eapply partial_pass; eassumption.
      * right; exists r''; split; [econstructor; eassumption|exact HF].
    + left; apply partial_run; assumption.
Qed.
Lemma partial_after machine hs1 r r' : sideRLs machine hs1 r r' ->
  forall hs2 n, Partial machine hs2 r' n -> Partial machine (hs1++hs2) r n.
Proof. intro H; induction H; intros hs2 n HP; [exact HP|cbn; eapply partial_pass; eauto]. Qed.

Lemma visit_partial s X M Y t : Visit s X M Y t -> forall r n,
  Partial mtm (codes M) r n -> forall l, exists k c', (S n<=k)%nat /\
    l {{X}}> (s>>r) -[mtm]->> k / c'.
Proof.
  intro H; induction H; intros r n HP l.
  - apply partial_nil in HP; subst n.
    destruct(progress_multistep _ _ _ (visit_right_run _ _ _ _ H l r)) as [k HK].
    exists (S k),(l <{{Y}} (t>>r)); split; [lia|exact HK].
  - cbn[codes map code] in HP; inversion HP; subst.
    + match goal with HR:sideRL mtm _ _ _ _, HT:Partial mtm (codes M) _ _ |- _ =>
        destruct(progress_multistep _ _ _ (HR (l<<w))) as [k1 HK1];
        destruct(IHVisit _ _ HT l) as [k2 [c' [HN HK2]]] end.
      destruct(progress_multistep _ _ _ (visit_left_run _ _ _ _ H l r)) as [k0 HK0].
      exists (S k0+S k1+k2)%nat,c'; split; [lia|].
      eapply multistep_trans; [eapply multistep_trans; [exact HK0|exact HK1]|exact HK2].
    + match goal with HR:forall l, exists k c', _ /\ _ |- _ =>
        destruct(HR (l<<w)) as [k1 [c' [HN HK1]]] end.
      destruct(progress_multistep _ _ _ (visit_left_run _ _ _ _ H l r)) as [k0 HK0].
      exists (S k0+k1)%nat,c'; split; [lia|].
      eapply multistep_trans; eassumption.
Qed.
Lemma cell_partial s R L t : Cell s R L t -> R<>[] -> forall r n,
  Partial mtm (codes L) r n -> Partial mtm (codes R) (s>>r) (S n).
Proof.
  intro H; induction H; intros HNE r0 n HP; [contradiction|].
  unfold codes in HP; rewrite map_app in HP.
  destruct(partial_split mtm (codes M1) (codes M2) r0 n HP) as [HF|[r1 [HF HT]]].
  - cbn[codes map code]; apply partial_run.
    intro l; exact(visit_partial _ _ _ _ _ H r0 n HF l).
  - destruct R as [|next R].
    + destruct(cell_nilR _ _ _ H0) as [EL ES]; subst.
      apply partial_nil in HT; subst n.
      cbn[codes map code]; apply partial_run; intro l.
      pose proof(visit_sound _ _ _ _ _ H _ _ HF l) as HR.
      destruct(progress_multistep _ _ _ HR) as [k HK].
      exists (S k); eexists; split; [lia|exact HK].
    + cbn[codes map code]; eapply partial_pass.
      * eapply visit_sound; eassumption.
      * apply IHCell; [discriminate|exact HT].
Qed.

Lemma rect_width n : forall R L, Rect (repeat S0 n) R L (repeat S1 n) ->
  forall r k, Partial mtm (codes L) r k ->
    Partial mtm (codes R) ((repeat S0 n)*>r) (n+k)%nat.
Proof.
  induction n as [|n IH]; intros R L HR r k HP; inversion HR; subst.
  - exact HP.
  - assert(HNE:R<>[]).
    { intro E; subst R.
      match goal with HC:Cell S0 [] _ S1 |- _ =>
        destruct(cell_nilR _ _ _ HC); discriminate end. }
    cbn[repeat Str_app Nat.add].
    eapply cell_partial; [eassumption|exact HNE|].
    eapply IH; eassumption.
Qed.

Definition As n := repeat a n.
Fixpoint pw (w:list letter) n := match n with O=>[] | S n=>w++pw w n end.
Definition D := [c;a;b].
Definition E := [c;b;a].
Definition F := [b;c;a].
Lemma As_add m n : As(m+n)=As m++As n.
Proof. apply repeat_app. Qed.
Lemma pw_succ_end w n : pw w(S n)=pw w n++w.
Proof.
  induction n; [cbn[pw]; now rewrite app_nil_r|].
  change(w++pw w(S n)=(w++pw w n)++w).
  rewrite IHn,app_assoc; reflexivity.
Qed.
Lemma pw_conj x y n : x++pw(y++x)n=pw(x++y)n++x.
Proof.
  induction n; cbn[pw]; [now rewrite app_nil_r|].
  rewrite <-app_assoc,app_assoc,IHn; rewrite !app_assoc; reflexivity.
Qed.

Lemma cell0a : Cell 0 [a] [] 1.
Proof. apply cell_single; apply visit_right; reflexivity. Qed.
Lemma visit0b k : Visit 0 B (As k++[c]) B 1.
Proof.
  induction k; cbn[As repeat app].
  - eapply visit_left; [reflexivity|apply visit_right; reflexivity].
  - eapply visit_left; [reflexivity|exact IHk].
Qed.
Lemma cell0b k : Cell 0 [b] (As k++[c]) 1.
Proof. apply cell_single,visit0b. Qed.
Lemma cell1a : Cell 1 [a] [c;b;a] 0.
Proof.
  apply cell_single; eapply visit_left; [reflexivity|].
  eapply visit_left; [reflexivity|]; eapply visit_left; [reflexivity|apply visit_right; reflexivity].
Qed.
Lemma cell1b : Cell 1 [b] [b] 0.
Proof. apply cell_single; eapply visit_left; [reflexivity|apply visit_right; reflexivity]. Qed.
Lemma cell1c : Cell 1 [c] [a] 3.
Proof. apply cell_single; eapply visit_left; [reflexivity|apply visit_right; reflexivity]. Qed.
Lemma cell3a : Cell 3 [a] [b] 0.
Proof. apply cell_single; eapply visit_left; [reflexivity|apply visit_right; reflexivity]. Qed.
Lemma cell3b : Cell 3 [b] [a] 0.
Proof. apply cell_single; eapply visit_left; [reflexivity|apply visit_right; reflexivity]. Qed.

Arguments cell_append {s t u R1 L1 R2 L2} _ _.
Arguments rect_append {S T U R1 L1 R2 L2} _ _.
Arguments rect_space {S S' T T' R M L} _ _.
Ltac list_nf := repeat rewrite <-app_assoc; cbn[app].
Lemma cell1aa : Cell 1 [a;a] E 1.
Proof. exact(cell_append cell1a cell0a). Qed.
Lemma cell1E : Cell 1 E [a;a] 1.
Proof. exact(cell_append (cell_append cell1c cell3b) cell0a). Qed.
Lemma cell1D k : Cell 1 D ([a;b]++As k++[c]) 1.
Proof. exact(cell_append (cell_append cell1c cell3a) (cell0b k)). Qed.
Lemma cell0F : Cell 0 F D 0.
Proof. exact(cell_append (cell_append (cell0b O) cell1c) cell3a). Qed.
Lemma cell0ab : Cell 0 [a;b] [b] 0.
Proof. exact(cell_append cell0a cell1b). Qed.
Lemma cell1_A2 j : Cell 1 (As(2*j)) (pw E j) 1.
Proof.
  induction j as [|j IH]; [constructor|].
  replace(2*S j)%nat with (2+2*j)%nat by lia; rewrite As_add.
  change(Cell 1 ([a;a]++As(2*j)) (E++pw E j) 1).
  exact(cell_append cell1aa IH).
Qed.
Lemma cell1_E j : Cell 1 (pw E j) (As(2*j)) 1.
Proof.
  induction j as [|j IH]; [constructor|].
  replace(2*S j)%nat with (2+2*j)%nat by lia; rewrite As_add.
  change(Cell 1 (E++pw E j) ([a;a]++As(2*j)) 1).
  exact(cell_append cell1E IH).
Qed.
Lemma cell1_D0 m : Cell 1 (pw D m) (pw [a;b;c] m) 1.
Proof.
  induction m as [|m IH]; [constructor|].
  exact(cell_append (cell1D O) IH).
Qed.
Lemma cell0_F m : Cell 0 (pw F m) (pw D m) 0.
Proof. induction m; [constructor|exact(cell_append cell0F IHm)]. Qed.
Lemma cell0_odd q : Cell 0 (As(2*q+1)) (pw E q) 1.
Proof.
  replace(2*q+1)%nat with(1+2*q)%nat by lia; rewrite As_add.
  exact(cell_append cell0a (cell1_A2 q)).
Qed.
Lemma c_abc m : [c]++pw [a;b;c] m=pw D m++[c].
Proof. exact(pw_conj [c] [a;b] m). Qed.
Lemma cell1_Dk m k : Cell 1 (pw D(S m)) ([a;b]++As k++pw D m++[c]) 1.
Proof.
  pose proof(cell_append (cell1D k) (cell1_D0 m)) as H.
  change(Cell 1 (D++pw D m) ([a;b]++As k++pw D m++[c]) 1).
  replace([a;b]++As k++pw D m++[c]) with (([a;b]++As k++[c])++pw [a;b;c] m).
  - exact H.
  - repeat rewrite <-app_assoc. rewrite <-c_abc. reflexivity.
Qed.
Lemma cell1_C j m s k :
  Cell 1 (pw E j++pw D(S m)++pw E s)
    (As(2*j+1)++[b]++As k++pw D m++[c]++As(2*s)) 1.
Proof.
  pose proof(cell_append (cell_append (cell1_E j) (cell1_Dk m k)) (cell1_E s)) as H.
  replace(2*j+1)%nat with(2*j+1)%nat by reflexivity; rewrite As_add.
  repeat rewrite <-app_assoc in H; cbn[app] in H.
  repeat rewrite <-app_assoc; cbn[As repeat app]; exact H.
Qed.

Definition Zeros n R L := Rect (repeat S0 n) R L (repeat S1 n).
Lemma rect_ones_b n : Rect (repeat S1 n) [b] [b] (repeat S0 n).
Proof. induction n; [constructor|econstructor; [apply cell1b|exact IHn]]. Qed.
Lemma cell_words s t R L R' L' : Cell s R L t -> R=R' -> L=L' -> Cell s R' L' t.
Proof. intros; subst; assumption. Qed.
Lemma rect_cast S R L T S' R' L' T' : Rect S R L T ->
  S=S' -> R=R' -> L=L' -> T=T' -> Rect S' R' L' T'.
Proof. intros; subst; assumption. Qed.
Lemma c_abc_tail m z : c::(pw [a;b;c] m++z)=pw D m++c::z.
Proof.
  change([c]++pw [a;b;c] m++z=pw D m++[c]++z).
  rewrite app_assoc,c_abc; list_nf; reflexivity.
Qed.
Lemma rect_pair j m s :
  Rect [1;1] (pw E j++pw D(S m)++pw E(S s))
    (pw E(S j)++pw D(S m)++pw E s) [1;1].
Proof.
  eapply rect_cons; [apply cell1_C with(k:=O)|].
  apply rect_one.
  pose proof(cell_append (cell_append (cell_append (cell_append
    (cell_append (cell_append (cell_append (cell1_A2 j) cell1a) (cell0b O))
      (cell1_D0 m)) cell1c) cell3a) cell0a) (cell1_A2 s)) as G.
  eapply cell_words; [exact G| |].
  - replace(2*S s)%nat with(1+1+2*s)%nat by lia.
    rewrite !As_add; unfold As; cbn[repeat]; list_nf; reflexivity.
  - rewrite !pw_succ_end; unfold D,E,As; cbn[repeat].
    list_nf; rewrite c_abc_tail; list_nf; reflexivity.
Qed.
Lemma rect_pairs m i : forall s,
  Rect (repeat S1 (2*i)) (pw D(S m)++pw E(i+s))
    (pw E i++pw D(S m)++pw E s) (repeat S1 (2*i)).
Proof.
  induction i as [|i IH]; intro s.
  - cbn[pw repeat Nat.mul Nat.add]; constructor.
  - pose proof(rect_space (IH (S s)) (rect_pair i m s)) as G.
    replace(2*S i)%nat with(2*i+2)%nat by lia; rewrite !repeat_app.
    replace(S i+s)%nat with(i+S s)%nat by lia; exact G.
Qed.
Lemma rect_wall h m e k :
  Rect (repeat S1 (2*h+1)) (pw D(S m)++pw E(h+e))
    (As(2*h+1)++[b]++As k++pw D m++[c]++As(2*e))
    (repeat S1 (2*h+1)).
Proof.
  rewrite !repeat_app.
  exact(rect_space (rect_pairs m h e) (rect_one _ _ _ _ (cell1_C h m e k))).
Qed.
Definition theta m k := match m with O=>[] | S _=>As k++pw D m end.
Definition Good d w M P :=
  (forall m q k, Zeros d (P++pw F m++As(d+1+2*q))
    (As k++pw D(M-1+m)++[c]++As(2*q+2))) /\
  (forall m q k, Zeros w (a::(pw D(M-1+m)++[c]++As(w+1+2*q)))
    (P++theta m k++pw E q)).

Lemma good_base : Good 2 1 1 [a;b].
Proof.
  split; intros m q k; unfold Zeros.
  - eapply rect_cons.
    + eapply cell_words.
      * exact(cell_append (cell_append cell0ab (cell0_F m)) (cell0_odd(S q))).
      * replace(2*S q+1)%nat with(2+1+2*q)%nat by lia; list_nf; reflexivity.
      * reflexivity.
    + apply rect_one. eapply cell_words.
      * exact(cell_append (cell_append (cell0b k) (cell1_D0 m)) (cell1_E(S q))).
      * list_nf; reflexivity.
      * replace(2*S q)%nat with(2*q+2)%nat by lia.
        list_nf; rewrite c_abc_tail; reflexivity.
  - apply rect_one; destruct m as [|m].
    + eapply cell_words.
      * exact(cell_append (cell_append (cell_append (cell_append cell0a cell1c) cell3a) cell0a) (cell1_A2 q)).
      * cbn[As repeat pw app Nat.sub Nat.add]; list_nf; reflexivity.
      * cbn[theta]; list_nf; reflexivity.
    + eapply cell_words.
      * exact(cell_append (cell_append (cell_append (cell_append (cell_append
          (cell_append cell0a (cell1D k)) (cell1_D0 m)) cell1c) cell3a) cell0a) (cell1_A2 q)).
      * cbn[As repeat pw app Nat.sub Nat.add]; list_nf; reflexivity.
      * cbn[theta]; rewrite pw_succ_end.
        list_nf; rewrite c_abc_tail; unfold D; list_nf; reflexivity.
Qed.

Lemma zeros_space n m R M L : Zeros n R M -> Zeros m M L -> Zeros(n+m) R L.
Proof. unfold Zeros; rewrite !repeat_app; apply rect_space. Qed.
Lemma bDca j e : [b]++pw D j++[c]++As(S e)=pw F(S j)++As e.
Proof.
  pose proof(pw_conj [b] [c;a] j) as H.
  change([b]++pw D j=pw F j++[b]) in H.
  change([b]++pw D j++[c;a]++As e=pw F(S j)++As e).
  rewrite (app_assoc [b] (pw D j)),H,pw_succ_end.
  unfold F; list_nf; reflexivity.
Qed.
Lemma echo d w M P h : Good d w M P -> w=(2*h+1)%nat ->
  Zeros(d+w) (P++As(d+w)) P.
Proof.
  intros [HR HT] HW; subst w.
  specialize(HR O h 1%nat); specialize(HT O O O).
  cbn[theta pw] in HR,HT.
  rewrite !Nat.add_0_r in HR.
  rewrite Nat.mul_0_r,!Nat.add_0_r,!app_nil_r in HT.
  replace(d+1+2*h)%nat with(d+(2*h+1))%nat in HR by lia.
  replace(2*h+1+1)%nat with(2*h+2)%nat in HT by lia.
  cbn[As repeat app] in HR.
  eapply zeros_space; [exact HR|exact HT].
Qed.
Lemma replicate_split (x:Sym) p q U1 U2 :
  repeat x(p+q)=U1++U2 -> length U1=p ->
  U1=repeat x p /\ U2=repeat x q.
Proof.
  intros H HL; pose proof(f_equal (@length Sym) H) as HT.
  rewrite repeat_length,length_app,HL in HT.
  destruct(repeat_eq_app x (p+q) U1 U2 H) as [H1 H2].
  rewrite HL in H1; assert(HL2:length U2=q) by lia; rewrite HL2 in H2; auto.
Qed.
Lemma theta_pos m k : (0<m)%nat -> theta m k=As k++pw D m.
Proof. destruct m; [lia|reflexivity]. Qed.
Arguments zeros_space {n m R M L} _ _.
Lemma good_step d w M P : Good d w M P -> (1<=M)%nat ->
  d=(2*M)%nat -> (w mod 2=1)%nat ->
  exists P', Good (2*d) (2*w+(d+w)) (2*M) P'.
Proof.
  intros HG HM HD HW.
  assert(HW':w=(2*(w/2)+1)%nat).
  { pose proof(Nat.div_mod w 2 ltac:(lia)); lia. }
  pose proof(echo d w M P (w/2) HG HW') as E0.
  assert(EC:Rect (repeat S0 w++repeat S0 d) (P++As(d+w)) P (repeat S1(w+d))).
  { rewrite <-repeat_app; replace(w+d)%nat with(d+w)%nat by lia; exact E0. }
  destruct(rect_cut (repeat S0 w) (repeat S0 d) _ _ _ EC)
    as [H [U1 [U2 [EU [HL [X Y]]]]]].
  rewrite repeat_length in HL.
  destruct(replicate_split S1 w d U1 U2 EU HL) as [EU1 EU2]; subst U1 U2.
  destruct HG as [GR GT].
  exists(H++[b]++P); split; intros m q k.
  - pose proof(rect_append (rect_append Y (rect_ones_b d)) (GR m(q+M)O)) as B1.
    pose proof(GR (M+m) q k) as B2.
    assert(EMid:(P++[b])++(As O++pw D(M-1+m)++[c]++As(2*(q+M)+2))=
      P++pw F(M+m)++As(d+1+2*q)).
    { pose proof(bDca (M-1+m) (d+1+2*q)) as HB.
      replace(S(M-1+m)) with(M+m)%nat in HB by lia.
      replace(S(d+1+2*q)) with(2*(q+M)+2)%nat in HB by lia.
      rewrite <-HB; cbn[As repeat]; list_nf; reflexivity. }
    rewrite EMid in B1.
    pose proof(zeros_space B1 B2) as G.
    unfold Zeros in G|-*; eapply rect_cast; [exact G| | | |].
    + replace(d+d)%nat with(2*d)%nat by lia; reflexivity.
    + replace(d+1+2*(q+M))%nat with(2*d+1+2*q)%nat by lia.
      list_nf; reflexivity.
    + replace(M-1+(M+m))%nat with(2*M-1+m)%nat by lia; reflexivity.
    + replace(d+d)%nat with(2*d)%nat by lia; reflexivity.
  - pose proof(GT (M+m) (d+w-M+q) (d+w)) as T1.
    rewrite theta_pos in T1 by lia.
    pose proof(rect_wall (w/2+M) (M+m-1) (w/2+1+q) 1%nat) as W.
    assert(W':Rect (repeat S1(d+w)) (pw D(M+m)++pw E(d+w-M+q))
      (As(d+w)++[b]++a::(pw D(M-1+m)++[c]++As(w+1+2*q))) (repeat S1(d+w))).
    { eapply rect_cast; [exact W| | | |].
      - replace(2*(w/2+M)+1)%nat with(d+w)%nat by lia; reflexivity.
      - replace(S(M+m-1)) with(M+m)%nat by lia.
        replace(w/2+M+(w/2+1+q))%nat with(d+w-M+q)%nat by lia; reflexivity.
      - replace(2*(w/2+M)+1)%nat with(d+w)%nat by lia.
        replace(M+m-1)%nat with(M-1+m)%nat by lia.
        replace(2*(w/2+1+q))%nat with(w+1+2*q)%nat by lia.
        cbn[As repeat]; list_nf; reflexivity.
      - replace(2*(w/2+M)+1)%nat with(d+w)%nat by lia; reflexivity. }
    pose proof(rect_append E0 W') as B2.
    pose proof(rect_append (rect_append X (rect_ones_b w)) (GT m q k)) as B3.
    repeat rewrite <-app_assoc in T1.
    repeat rewrite <-app_assoc in B2.
    repeat rewrite <-app_assoc in B3.
    cbn[app] in T1,B2,B3.
    pose proof(zeros_space (zeros_space T1 B2) B3) as G.
    unfold Zeros in G|-*; eapply rect_cast; [exact G| | | |].
    + replace(w+(d+w)+w)%nat with(2*w+(d+w))%nat by lia; reflexivity.
    + replace(M-1+(M+m))%nat with(2*M-1+m)%nat by lia.
      replace(w+1+2*(d+w-M+q))%nat with(2*w+(d+w)+1+2*q)%nat by lia.
      reflexivity.
    + list_nf; reflexivity.
    + replace(w+(d+w)+w)%nat with(2*w+(d+w))%nat by lia; reflexivity.
Qed.
Lemma all_ranks r : exists d w M P, (1<=M)%nat /\ d=(2*M)%nat /\
  (w mod 2=1)%nat /\ (r<w)%nat /\ (r<M)%nat /\ Good d w M P.
Proof.
  induction r as [|r IH].
  - exists 2%nat,1%nat,1%nat,[a;b].
    split; [lia|]; split; [reflexivity|]; split; [reflexivity|];
    split; [lia|]; split; [lia|apply good_base].
  - destruct IH as [d [w [M [P [HM [HD [HW [HRW [HRM HG]]]]]]]]].
    destruct(good_step d w M P HG HM HD HW) as [P' HG'].
    exists(2*d)%nat,(2*w+(d+w))%nat,(2*M)%nat,P'.
    split; [lia|]; split; [lia|]; split.
    + replace(2*w+(d+w))%nat with(w+(w+M)*2)%nat by lia.
      rewrite Nat.Div0.mod_add; exact HW.
    + split; [lia|]; split; [lia|exact HG'].
Qed.

(* The right-hand driver is proved directly in the original machine. *)
Definition U n : side := ([S0;S4;S2]^^n)*>0inf.
Lemma driver1 n : sideRL tm (A,[]) (A,[]) (U n) (S2>>U n).
Proof.
  induction n; intro l; unfold to_DH_config,U; cbn[lpow Str_app].
  - execute.
  - do 3 step; eapply progress_trans; [apply IHn|execute].
Qed.
Lemma driver2 n : sideRL tm (B,[]) (B,[]) (S2>>U n) (S4>>S2>>U n).
Proof. intro l; unfold to_DH_config; cbn; step; eapply progress_trans; [apply driver1|execute]. Qed.
Lemma driver3 n : sideRL tm (B,[]) (A,[]) (S4>>S2>>U n) (U(S n)).
Proof. intro l; unfold to_DH_config; cbn; step; eapply progress_trans; [apply driver2|unfold U; cbn[lpow Str_app]; execute]. Qed.

Definition cycle : list(DH0*DH0) :=
  [((A,[]),(A,[]));((B,[]),(B,[]));((B,[]),(A,[]))].
Definition drive j := [((B,[]),(A,[]))]++cycle^^j.
Lemma drive_sound j : sideRLs tm (drive j) 0inf (U j).
Proof.
  induction j as [|j IH].
  - cbn[drive lpow]; eapply sideRLseq_S with(r2:=0inf).
    + intro l; unfold to_DH_config; cbn.
      apply progress_base.
      pose proof(@step_left tm B A S0 S0 l 0inf eq_refl) as H.
      cbn[move_left] in H; rewrite <-const_unfold in H; exact H.
    + constructor.
  - unfold drive at 1.
    replace(cycle^^S j) with(cycle^^j++cycle) by (cbn[lpow]; apply lpow_shift).
    rewrite app_assoc; eapply sideRLs_trans; [exact IH|].
    unfold cycle; econstructor; [apply driver1|].
    econstructor; [apply driver2|]; econstructor; [apply driver3|constructor].
Qed.
Lemma cycle_lcons j : lcons (A,[]) (cycle^^j)=(codes(pw D j),(A,[])).
Proof.
  induction j; [reflexivity|].
  change(lcons (A,[]) (cycle++cycle^^j)=(codes(D++pw D j),(A,[]))).
  unfold cycle at 1; cbn[app lcons]; rewrite IHj; reflexivity.
Qed.
Lemma drive_lcons j : lcons (A,[]) (drive j)=(codes(a::pw D j),(A,[])).
Proof. unfold drive; cbn[app lcons]; rewrite cycle_lcons; reflexivity. Qed.
Lemma pw_length x j : length(pw x j)=(j*length x)%nat.
Proof. induction j; cbn[pw]; [reflexivity|rewrite length_app,IHj; cbn; lia]. Qed.
Lemma drive_length j : length(codes(a::pw D j))=(1+3*j)%nat.
Proof. unfold codes; rewrite length_map; cbn[length]; rewrite pw_length; change(S(j*3)=1+3*j)%nat; lia. Qed.

(* The driver need only realize a long enough prefix. If the partial
   rectangle completes a visit, the actual driver returns for the next;
   otherwise that visit already supplies the required real steps. *)
Lemma partial_driver machine ls : forall h1 h2 pre suffix l l' r n,
  lcons h1 ls=(pre,h2) -> (n<=length pre)%nat ->
  sideRLs machine ls l l' -> Partial (flip machine) (pre++suffix) r n ->
  exists c', l {{{(h1,R)}}} r -[flip machine]->> n / c'.
Proof.
  induction ls as [|[hin hout] ls IH]; intros h1 h2 pre suffix l l' r n HE HN HD HP.
  - cbn[lcons] in HE; inversion HE; subst; cbn in HN.
    assert(n=O) by lia; subst; eexists; constructor.
  - cbn[lcons] in HE; destruct(lcons hout ls) as [pre' hfinal] eqn:ET.
    inversion HE; subst; clear HE; cbn[length] in HN.
    inversion HD; subst; clear HD.
    destruct n as [|n]; [eexists; constructor|].
    cbn[app] in HP; inversion HP; subst; clear HP.
    + match goal with
      HR:sideRL (flip machine) h1 hin r ?rr,
      HT:Partial (flip machine) (pre'++suffix) ?rr (S n),
      HL:sideRL machine hin hout l ?ll,
      HS:sideRLs machine ls ?ll l' |- _ =>
        pose proof(partial_mono _ _ _ _ HT n ltac:(lia)) as HTn;
        destruct(IH hout _ pre' suffix ll l' rr n ET ltac:(lia) HS HTn) as [c' HC];
        pose proof(progress_trans _ _ _ _ (HR l) (to_DH_config_progress_flip(HL rr))) as HH
      end.
      destruct(progress_multistep _ _ _ HH) as [k HK].
      pose proof(multistep_trans _ _ _ _ _ _ HK HC) as HAll.
      replace(S k+n)%nat with(S n+k)%nat in HAll by lia.
      destruct(rewind_split _ _ _ _ _ HAll) as [c0' [H0 H1]].
      exists c0'; exact H0.
    + match goal with HR:forall l, exists k c', _ /\ _ |- _ =>
        destruct(HR l) as [k [c' [HK HRUN]]] end.
      replace k with(S n+(k-S n))%nat in HRUN by lia.
      destruct(rewind_split _ _ _ _ _ HRUN) as [c0' [H0 H1]].
      exists c0'; exact H0.
Qed.
Lemma repeat_blank n : (repeat S0 n)*>0inf=0inf.
Proof. induction n; cbn[repeat Str_app]; [reflexivity|rewrite IHn,<-const_unfold; reflexivity]. Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  assert(Hmirror:~halts mtm c0).
  { apply nonhalt_iff; intro n.
  destruct(all_ranks n) as [d [w [M [P [HM [HD [HW [HNW [HNM [_ GT]]]]]]]]]].
  pose proof(GT O O O) as HT.
  cbn[theta pw] in HT; rewrite Nat.mul_0_r,!Nat.add_0_r,!app_nil_r in HT.
  pose proof(rect_width w _ _ HT 0inf O (partial_zero mtm (codes P) 0inf)) as HP.
  rewrite Nat.add_0_r,repeat_blank in HP.
  apply partial_mono with(m:=n) in HP; [|lia].
  change(Partial mtm (codes((a::pw D(M-1))++([c]++As(w+1)))) 0inf n) in HP.
  unfold codes in HP; rewrite map_app in HP.
  exact(partial_driver tm (drive(M-1)) (A,[]) (A,[])
    (codes(a::pw D(M-1))) (codes([c]++As(w+1))) 0inf (U(M-1)) 0inf n
    (drive_lcons(M-1)) ltac:(rewrite drive_length; lia) (drive_sound(M-1)) HP). }
  intro H; apply Hmirror; exact(flip_halts tm c0 H).
Qed.

End TM60.
Print Assumptions TM60.nonhalt.
