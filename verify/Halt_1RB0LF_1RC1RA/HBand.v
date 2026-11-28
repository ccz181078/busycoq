(** Finishing a node into a lemma, the table of lemmas and the recursion over nodes. *)
From Coq Require Import ZArith Lia Uint63 List Bool PArray.
Import ListNotations.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Map Walk.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Ints HLines HCore HAbs.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.

(** ** Finishing: the region of a lemma, moved to reference W1, with lines that do not matter dropped *)
Definition lo_at1 (Wp W1 : int) (x : Line) : int := (lv x - ((lt x * (Wp - W1)) >> 30))%uint63.
Definition lo_at2 (Wp W2 : int) (x : Line) : int := (lv x + ((lt x * (W2 - Wp)) >> 30) + 1)%uint63.
Definition hi_at1 (Wp W1 : int) (x : Line) : int := (lv x - ((lt x * (Wp - W1)) >> 30) - 1)%uint63.
Definition hi_at2 (Wp W2 : int) (x : Line) : int := (lv x + ((lt x * (W2 - Wp)) >> 30))%uint63.

Record L3v := mkL3 { kt : int; k1 : int; k2 : int }.
Fixpoint lo_dom (a1 a2 : int) (acc : list L3v) : bool :=
  match acc with [] => false | k :: t => ((a1 <=? k1 k)%uint63 && (a2 <=? k2 k)%uint63) || lo_dom a1 a2 t end.
Fixpoint lo_drop (a1 a2 : int) (acc : list L3v) : list L3v :=
  match acc with [] => [] | k :: t => if (k1 k <=? a1)%uint63 && (k2 k <=? a2)%uint63 then lo_drop a1 a2 t else k :: lo_drop a1 a2 t end.
Fixpoint lo_keep (Wp W1 W2 : int) (raw : list Line) (acc : list L3v) : list L3v :=
  match raw with
  | [] => acc
  | x :: t =>
    let a1 := (lo_at1 Wp W1 x + 2)%uint63 in let a2 := (lo_at2 Wp W2 x + 2)%uint63 in
    if lo_dom a1 a2 acc then lo_keep Wp W1 W2 t acc
    else lo_keep Wp W1 W2 t (mkL3 (lt x) a1 a2 :: lo_drop a1 a2 acc)
  end.
Fixpoint hi_dom (a1 a2 : int) (acc : list L3v) : bool :=
  match acc with [] => false | k :: t => ((k1 k <=? a1)%uint63 && (k2 k <=? a2)%uint63) || hi_dom a1 a2 t end.
Fixpoint hi_drop (a1 a2 : int) (acc : list L3v) : list L3v :=
  match acc with [] => [] | k :: t => if (a1 <=? k1 k)%uint63 && (a2 <=? k2 k)%uint63 then hi_drop a1 a2 t else k :: hi_drop a1 a2 t end.
Fixpoint hi_keep (Wp W1 W2 : int) (raw : list Line) (acc : list L3v) : list L3v :=
  match raw with
  | [] => acc
  | x :: t =>
    let a1 := (hi_at1 Wp W1 x - 2)%uint63 in let a2 := (hi_at2 Wp W2 x - 2)%uint63 in
    if hi_dom a1 a2 acc then hi_keep Wp W1 W2 t acc
    else hi_keep Wp W1 W2 t (mkL3 (lt x) a1 a2 :: hi_drop a1 a2 acc)
  end.
Fixpoint finL (k : list L3v) : list Line := match k with [] => [] | y :: t => mkLine (kt y) (k1 y) :: finL t end.

(** The checks that make the choice of kept lines irrelevant for soundness. *)
Definition line_okb (x : Line) : bool := (lt x <=? TONE)%uint63 && (lv x <? 4611686018427387904)%uint63.
Definition dom_lo_b (r W1 W2 : int) (k x : Line) : bool :=
  let f1 := ((lt x * (r - W1)) >> 30)%uint63 in
  let f2 := ((lt x * (W2 - r)) >> 30)%uint63 in
  let fk := ((lt k * (W2 - W1)) >> 30)%uint63 in
  (lv x <=? lv k + f1)%uint63 && (lv x + f2 + 1 <=? lv k + fk)%uint63.
Definition dom_hi_b (r W1 W2 : int) (k x : Line) : bool :=
  let f1 := ((lt x * (r - W1)) >> 30)%uint63 in
  let f2 := ((lt x * (W2 - r)) >> 30)%uint63 in
  let fk := ((lt k * (W2 - W1)) >> 30)%uint63 in
  (lv k + f1 + 1 <=? lv x)%uint63 && (lv k + fk + 1 <=? lv x + f2)%uint63.

Definition KF : nat := 6.
Fixpoint finish_try (f : nat) (b : Ent) (W W1 W2 : int) : option Ent :=
  match f with O => None | S f =>
    let Wp := eW b in
    let kl := lo_keep Wp W1 W2 (elo b) [] in let ku := hi_keep Wp W1 W2 (ehi b) [] in
    if (Nat.leb (List.length kl) KF) && (Nat.leb (List.length ku) KF) then
      let lo := finL kl in let hi := finL ku in
      if forallb line_okb lo && forallb line_okb hi
         && forallb (fun x => existsb (fun k => dom_lo_b Wp W1 W2 k x) lo) (elo b)
         && forallb (fun x => existsb (fun k => dom_hi_b Wp W1 W2 k x) hi) (ehi b) then
        Some (mkEnt (ec b) (era b) (erb b) (ez b) (ed2 b) W1 W1 W2 lo hi
               (eY b) (elast b) (edet b) (edlast b) (edres b) (eGm b))
      else None
    else finish_try f b W (W - ((W - W1) >> 1))%uint63 (W + ((W2 - W) >> 1))%uint63
  end.

Definition finish_w (b : Ent) (W : int) : option Ent :=
  let W1 := max_ (eW1 b) (if (1073741824 <=? W)%uint63 then (W - 1073741824)%uint63 else 0%uint63) in
  let W2 := min_ (eW2 b) (W + 1073741824)%uint63 in
  if (W1 <=? W)%uint63 && (W <=? W2)%uint63 && (W =? eW b)%uint63 && (W <=? 1152921504606846976)%uint63 then finish_try 4 b W W1 W2 else None.

(** ** Soundness of finishing *)
Lemma fl_val (t a c : int) : phi t <= TT -> phi c <= phi a -> phi a - phi c <= 4294967296 ->
  TT * phi ((t * (a - c)) >> 30)%uint63 <= phi t * (phi a - phi c) < TT * (phi ((t * (a - c)) >> 30)%uint63 + 1) /\
  0 <= phi ((t * (a - c)) >> 30)%uint63 <= 4294967296.
Proof.
  intros Lt Hc Hd. pose proof (phi_bd63 t) as Bt.
  assert (Dm : phi (a - c)%uint63 = phi a - phi c) by pv.
  assert (B : 0 <= phi t * (phi a - phi c) <= TT * 4294967296).
  { split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]. }
  assert (M : phi (t * (a - c))%uint63 = phi t * (phi a - phi c)).
  { apply phi_of_cg; [cgs; unfold cg; rewrite Dm; reflexivity|lia]. }
  rewrite phi_lsr30, M.
  pose proof (fl_lo (phi t * (phi a - phi c))) as F1. pose proof (fl_hi (phi t * (phi a - phi c))) as F2.
  set (m := phi t * (phi a - phi c)) in *. set (f := m / TT) in *.
  clear M Dm. clearbody f. lia.
Qed.

Lemma dom_lo_sound r W1 W2 k x b S g :
  line_ok k -> line_ok x -> phi W1 <= phi r <= phi W2 -> phi W2 - phi W1 <= 4294967296 -> 1 <= g ->
  phi W1 * g <= PP * S -> PP * S <= phi W2 * g ->
  dom_lo_b r W1 W2 k x = true -> lo_l (phi W1) k b S g -> lo_l (phi r) x b S g.
Proof.
  intros [Lkt Lkv] [Lxt Lxv] Hr Hw Hg S1 S2 D Hl. unfold dom_lo_b in D. cbv zeta in D.
  destruct (fl_val (lt x) r W1 Lxt ltac:(lia) ltac:(lia)) as (F1a & F1b).
  destruct (fl_val (lt x) W2 r Lxt ltac:(lia) ltac:(lia)) as (F2a & F2b).
  destruct (fl_val (lt k) W2 W1 Lkt ltac:(lia) ltac:(lia)) as (F3a & F3b).
  apply andb_prop in D. destruct D as [D1 D2]. apply leb_true in D1, D2.
  set (f1 := ((lt x * (r - W1)) >> 30)%uint63) in *.
  set (f2 := ((lt x * (W2 - r)) >> 30)%uint63) in *.
  set (fk := ((lt k * (W2 - W1)) >> 30)%uint63) in *.
  clearbody f1 f2 fk.
  assert (A1 : phi (lv k + f1)%uint63 = phi (lv k) + phi f1) by pv.
  assert (A2 : phi (lv x + f2 + 1)%uint63 = phi (lv x) + phi f2 + 1) by pv.
  assert (A3 : phi (lv k + fk)%uint63 = phi (lv k) + phi fk) by pv.
  rewrite A1 in D1. rewrite A2, A3 in D2.
  pose proof (phi_bd63 (lt x)). pose proof (phi_bd63 (lt k)).
  unfold lo_l in *.
  apply (dom_lo (phi (lt k)) (phi (lv k) - VO) (phi W1) (phi W2) (phi (lt x)) (phi (lv x) - VO) (phi r) (phi f1) (phi f2) (phi fk) b S g); try lia.
  exact Hl.
Qed.

Lemma dom_hi_sound r W1 W2 k x b S g :
  line_ok k -> line_ok x -> phi W1 <= phi r <= phi W2 -> phi W2 - phi W1 <= 4294967296 -> 1 <= g ->
  phi W1 * g <= PP * S -> PP * S <= phi W2 * g ->
  dom_hi_b r W1 W2 k x = true -> hi_l (phi W1) k b S g -> hi_l (phi r) x b S g.
Proof.
  intros [Lkt Lkv] [Lxt Lxv] Hr Hw Hg S1 S2 D Hl. unfold dom_hi_b in D. cbv zeta in D.
  destruct (fl_val (lt x) r W1 Lxt ltac:(lia) ltac:(lia)) as (F1a & F1b).
  destruct (fl_val (lt x) W2 r Lxt ltac:(lia) ltac:(lia)) as (F2a & F2b).
  destruct (fl_val (lt k) W2 W1 Lkt ltac:(lia) ltac:(lia)) as (F3a & F3b).
  apply andb_prop in D. destruct D as [D1 D2]. apply leb_true in D1, D2.
  set (f1 := ((lt x * (r - W1)) >> 30)%uint63) in *.
  set (f2 := ((lt x * (W2 - r)) >> 30)%uint63) in *.
  set (fk := ((lt k * (W2 - W1)) >> 30)%uint63) in *.
  clearbody f1 f2 fk.
  assert (A1 : phi (lv k + f1 + 1)%uint63 = phi (lv k) + phi f1 + 1) by pv.
  assert (A2 : phi (lv k + fk + 1)%uint63 = phi (lv k) + phi fk + 1) by pv.
  assert (A3 : phi (lv x + f2)%uint63 = phi (lv x) + phi f2) by pv.
  rewrite A1 in D1. rewrite A2, A3 in D2.
  pose proof (phi_bd63 (lt x)). pose proof (phi_bd63 (lt k)).
  unfold hi_l in *.
  apply (dom_hi (phi (lt k)) (phi (lv k) - VO) (phi W1) (phi W2) (phi (lt x)) (phi (lv x) - VO) (phi r) (phi f1) (phi f2) (phi fk) b S g); try lia.
  exact Hl.
Qed.

Lemma line_okb_spec x : line_okb x = true -> line_ok x.
Proof.
  unfold line_okb, line_ok. intros H. apply andb_prop in H. destruct H as [H1 H2].
  apply leb_true in H1. apply ltb_true in H2. split; [exact H1|exact H2].
Qed.

Lemma finish_try_sound f b W W1 W2 e :
  ent_ok b -> phi W <= 1152921504606846976 -> phi (eW1 b) <= phi W1 -> phi W2 <= phi (eW2 b) -> phi W1 <= phi W <= phi W2 ->
  phi W - 1073741824 <= phi W1 -> phi W2 <= phi W + 1073741824 -> W = eW b ->
  finish_try f b W W1 W2 = Some e -> ent_ok e.
Proof.
  revert W1 W2. induction f as [|f IH]; intros W1 W2 Hb HW H1 H2 H3 H4 H5 HE H; [discriminate|].
  cbn [finish_try] in H. cbv zeta in H.
  destruct ((Nat.leb (List.length (lo_keep (eW b) W1 W2 (elo b) [])) KF) && (Nat.leb (List.length (hi_keep (eW b) W1 W2 (ehi b) [])) KF)) eqn:C.
  2:{ pose proof (phi_bd63 W1). pose proof (phi_bd63 W2). pose proof (phi_bd63 (eW2 b)). assert (Ma : phi (W - W1)%uint63 = phi W - phi W1) by pv.
      assert (Mb : phi (W2 - W)%uint63 = phi W2 - phi W) by pv.
      assert (Mc : phi ((W - W1) >> 1)%uint63 = (phi W - phi W1) / 2) by (rewrite lsr_spec, Ma; reflexivity).
      assert (Md : phi ((W2 - W) >> 1)%uint63 = (phi W2 - phi W) / 2) by (rewrite lsr_spec, Mb; reflexivity).
      assert (Bc : 0 <= (phi W - phi W1) / 2 <= phi W - phi W1) by (clear -H3; Z.div_mod_to_equations; lia).
      assert (Bd : 0 <= (phi W2 - phi W) / 2 <= phi W2 - phi W) by (clear -H3; Z.div_mod_to_equations; lia).
      assert (Me : phi (W - ((W - W1) >> 1))%uint63 = phi W - (phi W - phi W1) / 2) by (rewrite <- Mc; pv).
      assert (Mf : phi (W + ((W2 - W) >> 1))%uint63 = phi W + (phi W2 - phi W) / 2) by (rewrite <- Md; pv).
      apply (IH (W - ((W - W1) >> 1))%uint63 (W + ((W2 - W) >> 1))%uint63 Hb HW); try exact H; try exact HE; lia. }
  destruct (forallb line_okb (finL (lo_keep (eW b) W1 W2 (elo b) [])) && forallb line_okb (finL (hi_keep (eW b) W1 W2 (ehi b) []))
         && forallb (fun x => existsb (fun k => dom_lo_b (eW b) W1 W2 k x) (finL (lo_keep (eW b) W1 W2 (elo b) []))) (elo b)
         && forallb (fun x => existsb (fun k => dom_hi_b (eW b) W1 W2 k x) (finL (hi_keep (eW b) W1 W2 (ehi b) []))) (ehi b)) eqn:G; [|discriminate].
  injection H as <-.
  apply andb_prop in G. destruct G as [G G4]. apply andb_prop in G. destruct G as [G G3]. apply andb_prop in G. destruct G as [G1 G2].
  set (lo := finL (lo_keep (eW b) W1 W2 (elo b) [])) in *.
  set (hi := finL (hi_keep (eW b) W1 W2 (ehi b) [])) in *.
  clearbody lo hi.
  rewrite forallb_forall in G1, G2, G3, G4.
  destruct Hb as [Bd Sem]. destruct Bd as (BL & BU & BW & BW1 & BW2 & BY & BY4 & BL2 & Bc & BD & BG & BWa & BWb).
  subst W.
  split.
  - unfold ent_bd; cbn [elo ehi eW eW1 eW2 eY elast edlast eGm ec]. repeat split; try lia; try assumption.
    + apply Forall_forall. intros x Hx. apply line_okb_spec. apply G1. exact Hx.
    + apply Forall_forall. intros x Hx. apply line_okb_spec. apply G2. exact Hx.
  - intros B a b0 g HS Ha Hb Hg HG Hreg HPre HDet. cbn [ec era erb ez ed2 eW eW1 eW2 elo ehi eY elast edet edlast edres eGm] in *.
    unfold reg in Hreg. cbn [eW eW1 eW2 elo ehi] in Hreg. destruct Hreg as (RL & RU & R1 & R2). rewrite Forall_forall in RL, RU.
    assert (B0 : 0 <= phi (eW1 b)) by (pose proof (phi_bd63 (eW1 b)); lia).
    apply (Sem B a b0 g); try assumption.
    unfold reg. repeat split.
    + apply Forall_forall. intros x Hx. pose proof (G3 x Hx) as Ex. apply existsb_exists in Ex. destruct Ex as (k & Hk & Dk).
      apply (dom_lo_sound (eW b) W1 W2 k x b0 (a + b0) g); try assumption; try lia.
      * apply line_okb_spec. apply G1. exact Hk.
      * eapply In_Forall; [exact BL|exact Hx].
      * apply RL. exact Hk.
    + apply Forall_forall. intros x Hx. pose proof (G4 x Hx) as Ex. apply existsb_exists in Ex. destruct Ex as (k & Hk & Dk).
      apply (dom_hi_sound (eW b) W1 W2 k x b0 (a + b0) g); try assumption; try lia.
      * apply line_okb_spec. apply G2. exact Hk.
      * eapply In_Forall; [exact BU|exact Hx].
      * apply RU. exact Hk.
    + eapply Z.le_trans; [|exact R1]. apply Z.mul_le_mono_nonneg_r; lia.
    + eapply Z.le_trans; [exact R2|]. apply Z.mul_le_mono_nonneg_r; lia.
Qed.

(** ** The table *)
Record Ctx := mkCtx { xc : int; xra : int; xrb : int }.
Inductive Tr := TL | TN (kc klo khi : int) (e : Ent) (l r : Tr).
Record Mem := mkMem { mt : array Tr; mn : int }.
Definition TSIZE : int := 1048576.
Definition TMASK : int := 1048575.
Definition LIMIT : int := 500000.
(** A new array each time: a global one would keep every old version of the table alive through the persistent array's history. *)
Definition mem0 (_ : int) : Mem := mkMem (PArray.make TSIZE TL) 0.

Definition octave (W : int) : int := (63 - head0 W)%uint63.
Definition wcell (W : int) : int := (W >> (let e := octave W in if (e <? 50)%uint63 then 28%uint63 else (28 - (e - 50))%uint63))%uint63.
Definition slot (v : Env) (x : Ctx) (W : int) : int :=
  ((((xc x * 2654435761 + xra x * 40503 + xrb x * 1000003 + octave W * 16777619 + vz v * 131 + vd2 v * 2147483659 + wcell W * 1000000007) * 1400714819323198485) >> 40) land TMASK)%uint63.

Definition keyok (v : Env) (x : Ctx) (e : Ent) : bool :=
  (ec e =? xc x)%uint63 && (era e =? xra x)%uint63 && (erb e =? xrb x)%uint63 && (ez e =? vz v)%uint63 && (ed2 e =? vd2 v)%uint63.

Fixpoint lo_ok (l : list Line) (dW beta : int) : bool :=
  match l with [] => true | x :: t => (lv x + ((lt x * dW) >> 30) + 2 <=? beta + VOFF)%uint63 && lo_ok t dW beta end.
Fixpoint hi_ok (l : list Line) (dW beta : int) : bool :=
  match l with [] => true | x :: t => (beta + VOFF + 1 <=? lv x + ((lt x * dW) >> 30))%uint63 && hi_ok t dW beta end.
Definition in_region (e : Ent) (beta W : int) : bool :=
  (eW1 e <=? W)%uint63 && (W <=? eW2 e)%uint63 && (let dW := (W - eW1 e)%uint63 in lo_ok (elo e) dW beta && hi_ok (ehi e) dW beta).

Fixpoint look (t : Tr) (v : Env) (x : Ctx) (beta W : int) : option Ent :=
  match t with
  | TL => None
  | TN k klo khi e l r =>
    if (beta <? klo)%uint63 then look l v x beta W
    else if (khi <? beta)%uint63 then look r v x beta W
    else if keyok v x e && in_region e beta W then Some e
    else if (beta <? k)%uint63 then look l v x beta W else look r v x beta W
  end.
Fixpoint ins (t : Tr) (k klo khi : int) (e : Ent) : Tr :=
  match t with
  | TL => TN k klo khi e TL TL
  | TN k' a b e' l r => if (k <? k')%uint63 then TN k' a b e' (ins l k klo khi e) r else TN k' a b e' l (ins r k klo khi e)
  end.
Fixpoint maxlo (l : list Line) (dW m : int) : int :=
  match l with [] => m | x :: t => maxlo t dW (let u := (lv x + ((lt x * dW) >> 30))%uint63 in if (m <? u)%uint63 then u else m) end.
Fixpoint minhi (l : list Line) (dW m : int) : int :=
  match l with [] => m | x :: t => minhi t dW (let u := (lv x + ((lt x * dW) >> 30))%uint63 in if (u <? m)%uint63 then u else m) end.

Fixpoint tr_ok (t : Tr) : Prop :=
  match t with TL => True | TN _ _ _ e l r => ent_ok e /\ tr_ok l /\ tr_ok r end.
Lemma look_sound t v x beta W e : tr_ok t -> look t v x beta W = Some e -> ent_ok e.
Proof.
  induction t as [|k klo khi e' l IHl r IHr]; intros Ht H; cbn in H; [discriminate|].
  destruct Ht as (He & Hl & Hr).
  destruct (beta <? klo)%uint63; [apply IHl; assumption|].
  destruct (khi <? beta)%uint63; [apply IHr; assumption|].
  destruct (keyok v x e' && in_region e' beta W); [injection H as <-; exact He|].
  destruct (beta <? k)%uint63; [apply IHl; assumption|apply IHr; assumption].
Qed.
Lemma ins_ok t k klo khi e : tr_ok t -> ent_ok e -> tr_ok (ins t k klo khi e).
Proof.
  induction t as [|k' a b e' l IHl r IHr]; intros Ht He; cbn.
  - exact (conj He (conj I I)).
  - destruct Ht as (H1 & H2 & H3). destruct (k <? k')%uint63; cbn.
    + exact (conj H1 (conj (IHl H2 He) H3)).
    + exact (conj H1 (conj H2 (IHr H3 He))).
Qed.
Definition mem_ok (m : Mem) : Prop := forall i, tr_ok (PArray.get (mt m) i).
Lemma mem0_ok u : mem_ok (mem0 u).
Proof. intros i. unfold mem0. cbn [mt]. rewrite PArray.get_make. exact I. Qed.
Lemma mem_set_ok t s k klo khi e : (forall i, tr_ok (PArray.get t i)) -> ent_ok e ->
  forall i, tr_ok (PArray.get (PArray.set t s (ins (PArray.get t s) k klo khi e)) i).
Proof.
  intros Ht He i. destruct (s =? i)%uint63 eqn:Es.
  - apply Uint63.eqb_spec in Es. subst i. destruct (s <? PArray.length t)%uint63 eqn:L.
    + rewrite PArray.get_set_same by exact L. apply ins_ok; [apply Ht|exact He].
    + assert (Hd : PArray.get (PArray.set t s (ins (PArray.get t s) k klo khi e)) s = PArray.get t s).
      { rewrite PArray.get_out_of_bounds by (rewrite PArray.length_set; exact L).
        rewrite PArray.default_set. rewrite PArray.get_out_of_bounds by exact L. reflexivity. }
      rewrite Hd. apply Ht.
  - apply Uint63.eqb_false_spec in Es. rewrite PArray.get_set_other by exact Es. apply Ht.
Qed.

(** ** The recursion *)
Definition bld0 (v : Env) (x : Ctx) (W : int) : Ent :=
  mkEnt (xc x) (xra x) (xrb x) (vz v) (vd2 v) W (if (2147483648 <=? W)%uint63 then (W - 2147483648)%uint63 else 0%uint63) (W + 2147483648)%uint63
        [] [] 0 0 false 0 4 0.

Lemma bld0_ok v x W : phi (xc x) < 1099511627776 -> phi W <= 1152921504606846976 -> ent_ok (bld0 v x W).
Proof.
  intros Hc HW. split.
  - unfold ent_bd, bld0; cbn [elo ehi eW eW1 eW2 eY elast edlast eGm ec]. pose proof (phi_bd63 W).
    assert (E1 : phi (W + 2147483648)%uint63 = phi W + 2147483648) by pv. rewrite E1.
    assert (E2 : phi W - 2147483648 <= phi (if (2147483648 <=? W)%uint63 then (W - 2147483648)%uint63 else 0%uint63) <= 1152921504606846976).
    { destruct (2147483648 <=? W)%uint63 eqn:C.
      - apply leb_true in C. change (phi 2147483648%uint63) with 2147483648 in C. assert (F : phi (W - 2147483648)%uint63 = phi W - 2147483648) by pv. rewrite F. lia.
      - apply leb_false in C. change (phi 2147483648%uint63) with 2147483648 in C. change (phi 0%uint63) with 0. lia. }
    repeat split; try (constructor; fail); try lia; try reflexivity; try (vm_compute; reflexivity).
    all: try (vm_compute; intro X0; discriminate X0).
  - intros B a b g _ _ _ _ _ _ _ _. cbn [eY]. change (phi 0%uint63) with 0. rewrite Z.add_0_r. apply Rch_refl.
Qed.

Definition finish (b : Ent) (beta W : int) : option Ent :=
  match finish_w b W with
  | Some e => if in_region e beta W then Some e else None
  | None => None
  end.
Lemma finish_sound b beta W e : ent_ok b -> finish b beta W = Some e -> ent_ok e.
Proof.
  intros Hb H. unfold finish, finish_w in H. cbv zeta in H.
  set (W1 := max_ (eW1 b) (if (1073741824 <=? W)%uint63 then (W - 1073741824)%uint63 else 0%uint63)) in *.
  set (W2 := min_ (eW2 b) (W + 1073741824)%uint63) in *.
  destruct ((W1 <=? W)%uint63 && (W <=? W2)%uint63 && (W =? eW b)%uint63 && (W <=? 1152921504606846976)%uint63) eqn:C; [|discriminate].
  apply andb_prop in C. destruct C as [C C4]. apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  apply leb_true in C1, C2, C4. apply Uint63.eqb_spec in C3. change (phi 1152921504606846976%uint63) with 1152921504606846976 in C4.
  destruct (finish_try 4 b W W1 W2) as [e'|] eqn:F; [|discriminate].
  assert (He' : ent_ok e').
  { apply (finish_try_sound 4 b W W1 W2 e' Hb C4); try exact F; try exact C3; try lia.
    - unfold W1. rewrite phi_max. lia.
    - unfold W2. rewrite phi_min. lia.
    - unfold W1. rewrite phi_max. destruct (1073741824 <=? W)%uint63 eqn:D.
      + apply leb_true in D. change (phi 1073741824%uint63) with 1073741824 in D. assert (X : phi (W - 1073741824)%uint63 = phi W - 1073741824) by pv. lia.
      + apply leb_false in D. change (phi 1073741824%uint63) with 1073741824 in D. change (phi 0%uint63) with 0. lia.
    - unfold W2. rewrite phi_min. assert (X : phi (W + 1073741824)%uint63 = phi W + 1073741824) by pv. lia. }
  destruct (in_region e' beta W); [|discriminate]. injection H as <-. exact He'.
Qed.

Definition WMIN : int := 274877906944.
Definition Lfuel : nat := 64.

Fixpoint sec_go (rec : Mem -> Ctx -> int -> int -> Mem * option Ent) (v : Env) (x11 x00 : Ctx) (beta W w4 w2 w34 : int)
    (g : nat) (m : Mem) (b : Ent) : Mem * option Ent :=
  match g with
  | O => (m, None)
  | S g' =>
    let pos := (beta + (eY b << 28))%uint63 in
    if (W + 64 <=? pos)%uint63 then (m, Some b)
    else if (W <=? pos + 64)%uint63 then (m, None)
    else if (pos + 64 <? w4)%uint63 then
      match stop_rounds b v false beta with
      | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g' m b2
      | None => (m, None)
      end
    else if (pos <? w4 + 64)%uint63 then (m, None)
    else if (pos + 64 <? w2)%uint63 then
      let '(m1, och) := rec m x11 (pos - w4)%uint63 w4 in
      match och with
      | None => (m1, None)
      | Some ch =>
        match absorb b ch false with
        | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g' m1 b2
        | None => (m1, None)
        end
      end
    else if (pos <? w2 + 64)%uint63 then (m, None)
    else if (pos + 64 <? w34)%uint63 then
      match stop_rounds b v true beta with
      | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g' m b2
      | None => (m, None)
      end
    else if (pos <? w34 + 64)%uint63 then (m, None)
    else
      let '(m1, och) := rec m x00 (pos - w34)%uint63 w4 in
      match och with
      | None => (m1, None)
      | Some ch =>
        match absorb b ch true with
        | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g' m1 b2
        | None => (m1, None)
        end
      end
  end.

Definition sec_loop (rec : Mem -> Ctx -> int -> int -> Mem * option Ent) (v : Env) (x : Ctx) (beta W : int) (g : nat) (m : Mem) (b : Ent) : Mem * option Ent :=
  let ra := xra x in let rb := xrb x in let c := xc x in
  let w4 := (W >> 2)%uint63 in
  let kind := kind_of ra rb in
  let ra1 := ra_next ra rb kind in let rb1 := rb_next ra rb kind in
  let c1 := (c + kcost kind)%uint63 in
  let ra0 := ra_next ra rb 0 in let rb0 := rb_next ra rb 0 in
  sec_go rec v (mkCtx (c1 + 3)%uint63 (ra_next ra1 rb1 0) (rb_next ra1 rb1 0)) (mkCtx (c + 6)%uint63 (ra_next ra0 rb0 0) (rb_next ra0 rb0 0))
    beta W w4 (W >> 1)%uint63 (3 * w4)%uint63 g m b.

Fixpoint bn (f : nat) (m : Mem) (v : Env) (x : Ctx) (beta W : int) : Mem * option Ent :=
  match f with
  | O => (m, None)
  | S f' =>
    if (beta <? 32)%uint63 || (W <? 8192)%uint63 || (1152921504606846976 <? W)%uint63 || (1099511627776 <=? xc x)%uint63 then (m, None) else
    let memo := (WMIN <=? W)%uint63 in
    let s := if memo then slot v x W else 0%uint63 in
    match (if memo then look (PArray.get (mt m) s) v x beta W else None) with
    | Some e => (m, Some e)
    | None =>
      let '(m1, ob) := sec_loop (fun m' x' b' W' => bn f' m' v x' b' W') v x beta W Lfuel m (bld0 v x W) in
      match ob with
      | None => (m1, None)
      | Some b =>
        match finish b beta W with
        | None => (m1, None)
        | Some e =>
          if memo then
            let dW := (W - eW1 e)%uint63 in
            let klo := (maxlo (elo e) dW 0 - VOFF)%uint63 in
            let khi := (minhi (ehi e) dW 4611686018427387903 - VOFF)%uint63 in
            let m2 := if (LIMIT <=? mn m1)%uint63 then mem0 0%uint63 else m1 in
            (mkMem (PArray.set (mt m2) s (ins (PArray.get (mt m2) s) ((klo + khi) >> 1)%uint63 klo khi e)) (mn m2 + 1)%uint63, Some e)
          else (m1, Some e)
        end
      end
    end
  end.

(** ** Soundness of the recursion *)
Definition res_ok (r : Mem * option Ent) : Prop := mem_ok (fst r) /\ forall e, snd r = Some e -> ent_ok e.

Lemma sec_go_sound rec v x11 x00 beta W w4 w2 w34 : phi (vz v) = 6 \/ phi (vz v) = 22 ->
  (forall m x' b' W', mem_ok m -> res_ok (rec m x' b' W')) ->
  forall g m b, mem_ok m -> ent_ok b -> res_ok (sec_go rec v x11 x00 beta W w4 w2 w34 g m b).
Proof.
  intros Hz Hrec. induction g as [|g IH]; intros m b Hm Hb.
  { split; [exact Hm|intros e H; discriminate]. }
  cbn [sec_go]. cbv zeta.
  assert (St : forall dl, res_ok match stop_rounds b v dl beta with
      | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g m b2
      | None => (m, None) end).
  { intros dl. destruct (stop_rounds b v dl beta) as [b2|] eqn:S.
    - apply IH; [exact Hm|]. exact (proj1 (stop_sound b v dl beta b2 Hb Hz S)).
    - split; [exact Hm|intros e H; discriminate]. }
  assert (Ch : forall X Y Z dl, res_ok (let '(m1, och) := rec m X Y Z in
      match och with
      | None => (m1, None)
      | Some ch =>
        match absorb b ch dl with
        | Some b2 => sec_go rec v x11 x00 beta W w4 w2 w34 g m1 b2
        | None => (m1, None)
        end
      end)).
  { intros X Y Z dl. destruct (Hrec m X Y Z Hm) as [H1 H2]. destruct (rec m X Y Z) as [m1 och]. cbn [fst snd] in H1, H2.
    destruct och as [ch|].
    - destruct (absorb b ch dl) as [b2|] eqn:A.
      + apply IH; [exact H1|]. exact (proj1 (absorb_sound b ch dl b2 Hb (H2 ch eq_refl) A)).
      + split; [exact H1|intros e H; discriminate].
    - split; [exact H1|intros e H; discriminate]. }
  assert (N1 : res_ok (m, None)) by (split; [exact Hm|intros e H; discriminate]).
  assert (N2 : res_ok (m, Some b)) by (split; [exact Hm|intros e H; injection H as <-; exact Hb]).
  repeat (match goal with |- res_ok (if ?c then _ else _) => destruct c end); try assumption; try apply St; try apply Ch.
Qed.

Theorem bn_sound f : forall m v x beta W, phi (vz v) = 6 \/ phi (vz v) = 22 -> mem_ok m -> res_ok (bn f m v x beta W).
Proof.
  induction f as [|f IH]; intros m v x beta W Hz Hm.
  { split; [exact Hm|intros e H; discriminate]. }
  cbn [bn].
  destruct ((beta <? 32)%uint63 || (W <? 8192)%uint63 || (1152921504606846976 <? W)%uint63 || (1099511627776 <=? xc x)%uint63) eqn:C.
  { split; [exact Hm|intros e H; discriminate]. }
  repeat (apply orb_false_iff in C; destruct C as [C ?]). rename H into C4. rename H0 into C3. rename H1 into C2.
  apply ltb_false in C3. apply leb_false in C4. change (phi 1152921504606846976%uint63) with 1152921504606846976 in C3. change (phi 1099511627776%uint63) with 1099511627776 in C4.
  cbv zeta.
  set (s := if (WMIN <=? W)%uint63 then slot v x W else 0%uint63).
  destruct (if (WMIN <=? W)%uint63 then look (PArray.get (mt m) s) v x beta W else None) as [e|] eqn:L.
  { split; [exact Hm|]. intros e' H. cbn in H. injection H as <-. destruct (WMIN <=? W)%uint63; [|discriminate]. eapply look_sound; [apply Hm|exact L]. }
  assert (HS : res_ok (sec_loop (fun m' x' b' W' => bn f m' v x' b' W') v x beta W Lfuel m (bld0 v x W))).
  { unfold sec_loop. cbv zeta. apply sec_go_sound; [exact Hz|intros m' x' b' W' Hm'; apply IH; assumption|exact Hm|apply bld0_ok; assumption]. }
  destruct (sec_loop (fun m' x' b' W' => bn f m' v x' b' W') v x beta W Lfuel m (bld0 v x W)) as [m1 ob].
  destruct HS as [H1 H2]. cbn [fst snd] in H1, H2.
  destruct ob as [b|]; [|split; [exact H1|intros e H; discriminate]].
  destruct (finish b beta W) as [e|] eqn:F; [|split; [exact H1|intros e H; discriminate]].
  assert (He : ent_ok e) by exact (finish_sound b beta W e (H2 b eq_refl) F).
  destruct (WMIN <=? W)%uint63.
  - set (m2 := if (LIMIT <=? mn m1)%uint63 then mem0 0%uint63 else m1).
    assert (Hm2 : mem_ok m2) by (unfold m2; destruct (LIMIT <=? mn m1)%uint63; [apply mem0_ok|exact H1]).
    split.
    + intros i. cbn [fst mt]. apply mem_set_ok; [exact Hm2|exact He].
    + intros e' H. cbn [snd] in H. injection H as <-. exact He.
  - split; [exact H1|]. intros e' H. cbn [snd] in H. injection H as <-. exact He.
Qed.
