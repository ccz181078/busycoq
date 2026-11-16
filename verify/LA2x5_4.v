(* Self-contained BB(2,5) halting proof; only BusyCoq and Coq dependencies.
   The last Qed performs the long computation. *)
From BusyCoq Require Import Individual25 FastRev.
From Coq Require Uint63 PArray.
From Coq Require Import List String NArith ZArith ZifyNat Lia.
Import PrimInt63 ListNotations.
Set Warnings "-abstract-large-number".

Unset Implicit Arguments.
(** [sideRLs] only describes calls in which every signal returns.  This
    companion predicate describes a finite signal stream whose execution
    halts while processing one of its signals; the unused suffix is retained
    in the index but is deliberately unconstrained. *)
Inductive sideRLs_halt (tm : TM) : list (DH0 * DH0) -> side -> Prop :=
| sideRLs_halt_here hR hL hs r :
    (forall l, halts tm (l {{{ (hR,R) }}} r)) ->
    sideRLs_halt tm ((hR,hL)::hs) r
| sideRLs_halt_next hR hL hs r r' :
    sideRL tm hR hL r r' ->
    sideRLs_halt tm hs r' ->
    sideRLs_halt tm ((hR,hL)::hs) r.

#[export] Hint Constructors sideRLs_halt : core.

Lemma sideRLs_halt_app_left tm hs1 hs2 r :
  sideRLs_halt tm hs1 r ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_app_right tm hs1 hs2 r r' :
  sideRLs tm hs1 r r' ->
  sideRLs_halt tm hs2 r' ->
  sideRLs_halt tm (hs1 ++ hs2) r.
Proof.
  intros H.
  induction H; cbn; eauto.
Qed.

Lemma sideRLs_halt_split tm hs1 hs2 r :
  sideRLs_halt tm (hs1 ++ hs2) r ->
  sideRLs_halt tm hs1 r \/
  exists r', sideRLs tm hs1 r r' /\ sideRLs_halt tm hs2 r'.
Proof.
  gen r.
  induction hs1 as [|[hR hL] hs1 IH]; cbn; intros r H.
  - right. exists r. split; [constructor|exact H].
  - inverts H.
    + left. constructor. exact H4.
    + specialize (IH _ H5).
      destruct IH as [IH|[r'' [IH1 IH2]]].
      * left. econstructor 2; eauto.
      * right. exists r''. split; [econstructor; eauto|exact IH2].
Qed.

(** A halting version of [sideRLs_segLRs_concat].  It is the extra case
    needed by the [segRLs_lrcons] constructor: after each returned right-side
    call, [segLRs] carries the head through the finite word to the next call. *)
Lemma sideRLs_halt_segLRs_concat tm hs h1 h2 w1 w2 r :
  segLRs tm hs w1 w2 ->
  sideRLs_halt tm (lrcons h1 hs h2) r ->
  forall l, halts tm (l <* w1 {{{ (h1,R) }}} r).
Proof.
  intros Hseg.
  gen h1 h2 r.
  induction Hseg; intros h1' h2' r Hhalt l.
  - cbn in Hhalt.
    inverts Hhalt; eauto.
    match goal with
    | Hnone : sideRLs_halt _ [] _ |- _ => inverts Hnone
    end.
  - cbn in Hhalt.
    inverts Hhalt.
    + eauto.
    + eapply halts_evstep.
      1: eapply IHHseg; eassumption.
      eapply progress_evstep.
      eapply progress_evstep_trans with
        (c' := (w1 *> l) {{{ (h1,L) }}} r').
      * apply H4.
      * apply H.
Qed.

(** If a segment emits a signal stream which later halts, then the input
    stream halts as well.  Unlike the extensional experiment in the old
    backup file, this theorem is proved by induction over the actual
    [segRLs] derivation, so the halting case cannot hold vacuously. *)
Lemma segRLs_sideRLs_halt_concat tm hs1 hs2 w1 w2 r :
  segRLs tm hs1 hs2 w1 w2 ->
  sideRLs_halt tm hs2 r ->
  sideRLs_halt tm hs1 (w1 *> r).
Proof.
  intros Hseg.
  gen r.
  induction Hseg; intros r Hhalt.
  - inverts Hhalt.
  - econstructor 2.
    + intros l. apply H.
    + eapply IHHseg. exact Hhalt.
  - apply sideRLs_halt_split in Hhalt.
    destruct Hhalt as [Hprefix|[r' [Hprefix Hsuffix]]].
    + constructor 1. intros l.
      eapply halts_evstep.
      1: eapply sideRLs_halt_segLRs_concat; eauto.
      apply H.
    + econstructor 2.
      * intros l.
        follow H.
        eapply progress_evstep_trans.
        2: apply H0.
        eapply sideRLs_segLRs_concat; eauto.
      * eapply IHHseg. exact Hsuffix.
Qed.

(* Unlike sideRL_rec, keep fuel exhaustion distinct from halting. *)
Inductive SideResult :=
| OutOfFuel
| Returned (q:Q) (r:side)
| Halted.

Definition result_spec tm l0 c result := match result with
| OutOfFuel => True
| Returned q r => c -[tm]->+ l0 <{{q}} r
| Halted => halts tm c end.

Lemma result_step tm l0 c c' result :
  c -[tm]-> c' -> result_spec tm l0 c' result -> result_spec tm l0 c result.
Proof. destruct result; cbn; intros; eauto using progress_step,halts_step. Qed.

Fixpoint sideRL_halt_rec (tm:TM) (l:list Sym) (r:side) (q:Q) (T:nat) :=
match T with
| O => OutOfFuel
| S T => match r with m>>r => match tm(q,m) with
  | None => Halted
  | Some(m,L,q) => match l with
    | [] => Returned q (m>>r)
    | m'::l => sideRL_halt_rec tm l (m'>>m>>r) q T end
  | Some(m,R,q) => sideRL_halt_rec tm (m::l) r q T
  end end
end.

Lemma sideRL_halt_rec_spec tm T : forall l r q l0,
  result_spec tm l0 (l0 <* l {{q}}> r) (sideRL_halt_rec tm l r q T).
Proof.
  induction T; intros l [m r] q l0; cbn[sideRL_halt_rec result_spec]; [trivial|].
  destruct (tm(q,m)) as [[[m' []] q']|] eqn:E.
  - destruct l as [|x l].
    + cbn[result_spec]; do 2 econstructor; exact E.
    + eapply result_step; [eapply step_left; exact E|exact (IHT l (x>>m'>>r) q' l0)].
  - eapply result_step; [eapply step_right; exact E|exact (IHT (m'::l) r q' l0)].
  - apply halted_halts; exact E.
Qed.

Definition calls (qs:list Q) : list (DH0*DH0) :=
  List.map (fun q=>((q,[]),(A,[]))) qs.

Definition FlowHalts tm pre period r :=
  exists n, sideRLs_halt tm (calls (pre++period^^n)) r.

Inductive LeftRun tm : list Q -> side -> side -> Prop :=
| left_run_nil l : LeftRun tm [] l l
| left_run_cons q qs l l' l'' :
    (forall r, l <{{A}} r -[tm]->+ l' {{q}}> r) ->
    LeftRun tm qs l' l'' -> LeftRun tm (q::qs) l l''.
Lemma left_run_app tm qs l l' : LeftRun tm qs l l' -> forall qs' l'',
  LeftRun tm qs' l' l'' -> LeftRun tm (qs++qs') l l''.
Proof. intro H; induction H; cbn; intros; eauto using left_run_nil,left_run_cons. Qed.

Lemma left_run_halt tm qs l l' : LeftRun tm qs l l' -> forall q r,
  sideRLs_halt tm (calls (q::qs)) r -> halts tm (l {{q}}> r).
Proof.
  intro H; induction H; intros q0 r HH; cbn[calls] in HH;
    inversion HH as [hR hL hs r0 HH0|hR hL hs r0 r' HR HH']; subst.
  - apply HH0.
  - inversion HH'.
  - apply HH0.
  - eapply halts_evstep; [apply IHLeftRun; exact HH'|].
    follow100 (HR l); apply progress_evstep,H.
Qed.
Lemma rotate_pow {X} (q:X) qs n : q::(qs++[q])^^n=(q::qs)^^n++[q].
Proof.
  induction n; cbn[lpow app]; [reflexivity|].
  rewrite <-List.app_assoc; cbn[app]; rewrite IHn; rewrite List.app_assoc; reflexivity.
Qed.
Lemma left_cycles tm qs (L:nat->side) :
  (forall n, LeftRun tm qs (L n) (L (1+n))) ->
  forall k n, LeftRun tm (qs^^k) (L n) (L (k+n)).
Proof.
  intro H; induction k; intro n; cbn[lpow]; [constructor|].
  eapply left_run_app; [apply H|applys_eq (IHk (1+n)); flia].
Qed.
Lemma left_period_halt tm q qs (L:nat->side) r :
  (forall n, LeftRun tm (qs++[q]) (L n) (L (1+n))) ->
  FlowHalts tm [] (q::qs) r -> halts tm (L 0%nat {{q}}> r).
Proof.
  intros HL [n HH].
  eapply left_run_halt with (qs:=(qs++[q])^^n).
  - eapply left_cycles; exact HL.
  - rewrite rotate_pow; unfold calls; rewrite List.map_app.
    apply sideRLs_halt_app_left; exact HH.
Qed.

Set Implicit Arguments.

Definition LocalTable := Q -> Sym -> option (Sym * list Q).
Module LocalColumns.
Fixpoint feed_acc (tr:LocalTable) qs s acc := match qs with
| [] => Some (s,fast_rev acc)
| q::qs => match tr q s with
  | None => None
  | Some(s,ws) => feed_acc tr qs s (fast_rev_append ws acc)
  end end.
Definition feed tr qs s := feed_acc tr qs s [].

End LocalColumns.

Lemma calls_app xs ys : calls (xs++ys)=calls xs++calls ys.
Proof. apply List.map_app. Qed.

Lemma calls_pow qs n : calls (qs^^n)=(calls qs)^^n.
Proof. induction n; cbn[lpow]; [reflexivity|rewrite calls_app,IHn; reflexivity]. Qed.
Lemma seg_cycle_pow tm u v w n : segRLs tm u v w w -> segRLs tm (u^^n) (v^^n) w w.
Proof. intro H; induction n; cbn[lpow]; [constructor|eapply segRLs_trans; eauto]. Qed.

Module PackedSignals.
Definition idx (n:nat) := Uint63.of_Z (Z.of_nat n).
Definition unidx (i:Uint63.int) := Z.to_nat (Uint63.to_Z i).
Lemma idx_unidx i : idx (unidx i)=i.
Proof.
  unfold idx,unidx. rewrite Z2Nat.id by (pose proof (Uint63.to_Z_bounded i); lia).
  apply Uint63.of_to_Z.
Qed.
Lemma unidx_lt i n : Uint63.ltb i (idx n)=true -> unidx i<n.
Proof.
  rewrite Uint63.ltb_spec. unfold idx,unidx.
  rewrite Uint63.of_Z_spec. pose proof (Uint63.to_Z_bounded i).
  pose proof (Z.mod_le (Z.of_nat n) Uint63.wB). intro HI.
  assert (0<Uint63.wB)%Z by (vm_compute; reflexivity).
  lia.
Qed.

Fixpoint alln n (f:nat->bool) := match n with
| O=>true | S k=> if f k then alln k f else false end.
Lemma alln_spec n f : alln n f=true -> forall i, i<n -> f i=true.
Proof.
  induction n; cbn; intros H i Hi; [lia|].
  destruct (f n) eqn:E; [|discriminate].
  destruct (Nat.eq_dec i n); [subst; exact E|apply IHn; lia || assumption].
Qed.
Fixpoint fill {X} n (f:Uint63.int->X) (a:PArray.array X) := match n with
| O=>a | S k=>PArray.set (fill k f a) (idx k) (f (idx k)) end.
Definition tabulate {X} n (f:Uint63.int->X) d := fill n f (PArray.make (idx n) d).

(* A sentinel code carries at most eight bits, least significant bit first.
   Only the small table constructors decode it, never the large hot loops. *)
Fixpoint decode fuel (i:Uint63.int) : list Q := match fuel with
| O=>[]
| S k=>if Uint63.leb i 1%uint63 then [] else
   (if Uint63.eqb (Uint63.land i 1%uint63) 0%uint63 then A else B)::
   decode k (Uint63.lsr i 1%uint63)
end.
Definition word := decode 8.
Definition words := List.flat_map word.
Fixpoint code_nat (qs:list Q) : nat := match qs with
| []=>1 | q::qs=>code_nat qs+code_nat qs+match q with A=>0|B=>1 end end.
Definition encode qs := idx (code_nat qs).
Fixpoint pack_slow fuel qs : list Uint63.int := match fuel,qs with
| O,_ | _,[]=>[]
| S k,_=>encode (firstn 8 qs)::pack_slow k (skipn 8 qs) end.
Definition eqs := Eqb.list_eqb q_eqb.
Lemma eqs_spec x y : eqs x y=true -> x=y.
Proof. unfold eqs; destruct (Eqb.list_eqb_spec q_eqb x y q_eqb_spec); congruence. Qed.
Lemma words_app xs ys : words (xs++ys)=words xs++words ys.
Proof. apply flat_map_app. Qed.
Lemma words_rev_acc xs w : words (fast_rev (w::xs))=words (fast_rev xs)++word w.
Proof. rewrite !fast_rev_spec; cbn[List.rev]; rewrite words_app; cbn[words flat_map]; rewrite app_nil_r; reflexivity. Qed.

Definition Join := (Uint63.int * Uint63.int)%type.
Definition JRow := PArray.array (option Join).
Definition JTable := PArray.array JRow.
Definition join_entry a b : option Join :=
  let qs:=word a++word b in
  if Nat.ltb (List.length qs) 8 then Some(1%uint63,encode qs)
  else Some(encode(firstn 8 qs),encode(skipn 8 qs)).
Definition join_table : JTable :=
  tabulate 512 (fun a=>tabulate 512 (join_entry a) None) (PArray.make 512%uint63 None).
Definition join_get (t:JTable) a b :=
  if Uint63.ltb a 512%uint63 then
  if Uint63.ltb b 512%uint63 then PArray.get (PArray.get t a) b else None else None.
Definition join_ok (t:JTable) := alln 512 (fun a=>alln 512 (fun b=>
  match join_get t (idx a) (idx b) with
  | None=>true | Some(u,v)=>eqs (word (idx a)++word (idx b)) (word u++word v) end)).
Lemma join_get_spec t : join_ok t=true -> forall a b u v,
  join_get t a b=Some(u,v) -> word a++word b=word u++word v.
Proof.
  intros H a b u v E.
  assert (HA:unidx a<512). {
    unfold join_get in E; destruct (Uint63.ltb a 512%uint63) eqn:F; [|discriminate].
    apply (@unidx_lt a 512); exact F. }
  assert (HB:unidx b<512). {
    unfold join_get in E; destruct (Uint63.ltb a 512%uint63); [|discriminate].
    destruct (Uint63.ltb b 512%uint63) eqn:F; [|discriminate].
    apply (@unidx_lt b 512); exact F. }
  pose proof (@alln_spec _ _ (@alln_spec _ _ H _ HA) _ HB) as HJ.
  rewrite !idx_unidx,E in HJ. apply eqs_spec,HJ.
Qed.

(* Output chunks are accumulated in reverse order, with one pending short
   word. All concatenation is a finite-table lookup. *)
Fixpoint push_words (t:JTable) ws acc pending := match ws with
| []=>Some(acc,pending)
| w::ws=>match join_get t pending w with
  | None=>None
  | Some(full,part)=>push_words t ws
      (if Uint63.eqb full 1%uint63 then acc else full::acc) part
  end end.
Definition finish_words acc pending :=
  fast_rev (if Uint63.eqb pending 1%uint63 then acc else pending::acc).
Lemma finish_words_spec acc pending :
  words (finish_words acc pending)=words (fast_rev acc)++word pending.
Proof.
  unfold finish_words. destruct (Uint63.eqb pending 1%uint63) eqn:E.
  - apply Uint63.eqb_spec in E; subst; cbn[word decode]; rewrite app_nil_r; reflexivity.
  - apply words_rev_acc.
Qed.
Lemma push_words_spec t (HT:join_ok t=true) ws : forall acc p acc' p',
  push_words t ws acc p=Some(acc',p') ->
  words(fast_rev acc')++word p'=(words(fast_rev acc)++word p)++words ws.
Proof.
  induction ws as [|w ws IH]; intros acc p acc' p'; cbn[push_words].
  - intro E; inversion E; subst; cbn[words flat_map]; rewrite app_nil_r; reflexivity.
  - destruct (join_get t p w) as [[u v]|] eqn:E; [|discriminate].
    intro H; apply IH in H.
    pose proof (@join_get_spec t HT p w u v E) as HJ.
    destruct (Uint63.eqb u 1%uint63) eqn:EU.
    + apply Uint63.eqb_spec in EU; subst u.
      change (word p++word w=word v) in HJ.
      change (words(fast_rev acc')++word p'=(words(fast_rev acc)++word v)++words ws) in H.
      rewrite H; cbn[words flat_map]; rewrite <-HJ; repeat rewrite app_assoc; reflexivity.
    + rewrite H,words_rev_acc; cbn[words flat_map].
      rewrite <- (app_assoc (words(fast_rev acc)) (word u) (word v)),<-HJ.
      repeat rewrite app_assoc; reflexivity.
Qed.
End PackedSignals.

Import PackedSignals.
Module PackedColumns.
Definition digit i : Sym := if Uint63.eqb i 0%uint63 then 1 else
  if Uint63.eqb i 1%uint63 then 3 else 4.
Definition block i := [digit (Uint63.mod i 3%uint63);
  digit (Uint63.mod (Uint63.div i 3%uint63) 3%uint63);
  digit (Uint63.mod (Uint63.div i 9%uint63) 3%uint63)].
Definition undigit (s:Sym) : option nat := match s with
  | 1=>Some 0%nat | 3=>Some 1%nat | 4=>Some 2%nat | _=>None end.
Definition block_code ss := match ss with
| [a;b;c]=>match undigit a,undigit b,undigit c with
  | Some a,Some b,Some c=>Some(idx(a+b*3+c*9)) | _,_,_=>None end
| _=>None end.
Lemma block_code_spec ss g : block_code ss=Some g -> block g=ss.
Proof.
  destruct ss as [|a [|b [|c [|d ss]]]]; try discriminate.
  destruct a,b,c; cbn[block_code undigit]; intro E; try discriminate;
    inversion E; subst; reflexivity.
Qed.
Definition Entry := (Uint63.int * list Uint63.int)%type.
Definition Row := PArray.array (option Entry).
Definition Table := PArray.array Row.
Definition get (t:Table) g w :=
  if Uint63.ltb g 27%uint63 then
  if Uint63.ltb w 512%uint63 then PArray.get (PArray.get t g) w else None else None.
Definition table_ok tm (t:Table) := alln 27 (fun g=>alln 512 (fun w=>
  match get t (idx g) (idx w) with
  | None=>true | Some(g',out)=>BoundedConfig.segRLs_c tm
    (calls(word(idx w))) (calls(words out)) (block(idx g)) (block g') 256 end)).
Lemma get_spec tm t : table_ok tm t=true -> forall g w g' out,
  get t g w=Some(g',out) ->
  segRLs tm (calls(word w)) (calls(words out)) (block g) (block g').
Proof.
  intros H g w g' out E.
  assert (HG:unidx g<27). {
    unfold get in E; destruct (Uint63.ltb g 27%uint63) eqn:F; [|discriminate].
    apply (@unidx_lt g 27); exact F. }
  assert (HW:unidx w<512). {
    unfold get in E; destruct (Uint63.ltb g 27%uint63); [|discriminate].
    destruct (Uint63.ltb w 512%uint63) eqn:F; [|discriminate].
    apply (@unidx_lt w 512); exact F. }
  pose proof (@alln_spec _ _ (@alln_spec _ _ H _ HG) _ HW) as HH.
  rewrite !idx_unidx,E in HH. eapply BoundedConfig.segRLs_c_spec; exact HH.
Qed.

Fixpoint cross_slow tr ss qs := match ss with
| []=>Some([],qs)
| s::ss=>match LocalColumns.feed tr qs s with
  | None=>None | Some(s',out)=>match cross_slow tr ss out with
    | None=>None | Some(ss',out')=>Some(s'::ss',out') end end end.
Definition make_entry tr g w := match cross_slow tr (block g) (word w) with
| None=>None | Some(ss,qs)=>match block_code ss with
  | None=>None | Some g'=>Some(g',pack_slow (List.length qs) qs) end end.
Definition make_table tr : Table := tabulate 27
  (fun g=>tabulate 512 (make_entry tr g) None) (PArray.make 512%uint63 None).

Fixpoint feed_acc (t:Table) (j:JTable) ws g acc p := match ws with
| []=>Some(g,acc,p)
| w::ws=>match get t g w with
  | None=>None | Some(g',out)=>match push_words j out acc p with
    | None=>None | Some(acc',p')=>feed_acc t j ws g' acc' p' end end end.
Definition feed t j ws g := match feed_acc t j ws g [] 1%uint63 with
| None=>None | Some(g',acc,p)=>Some(g',finish_words acc p) end.

Lemma feed_acc_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) ws :
  forall g acc p g' acc' p', feed_acc t j ws g acc p=Some(g',acc',p') ->
  exists out, words(fast_rev acc')++word p'=(words(fast_rev acc)++word p)++out /\
  segRLs tm (calls(words ws)) (calls out) (block g) (block g').
Proof.
  induction ws as [|w ws IH]; intros g acc p g' acc' p'; cbn[feed_acc].
  - intro E; inversion E; subst; exists (@nil Q); split; [rewrite app_nil_r; reflexivity|constructor].
  - destruct (get t g w) as [[g0 out]|] eqn:E0; [|discriminate].
    destruct (push_words j out acc p) as [[acc0 p0]|] eqn:E1; [|discriminate].
    intro E; destruct (IH _ _ _ _ _ _ E) as [rest [HW HR]].
    exists (words out++rest); split.
    + rewrite HW,(@push_words_spec j HJ _ _ _ _ _ E1),app_assoc; reflexivity.
    + change (words(w::ws)) with (word w++words ws); rewrite !calls_app.
      eapply segRLs_trans; [eapply get_spec; eauto|exact HR].
Qed.
Lemma feed_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) ws g g' out :
  feed t j ws g=Some(g',out) ->
  segRLs tm (calls(words ws)) (calls(words out)) (block g) (block g').
Proof.
  unfold feed; destruct (feed_acc t j ws g [] 1%uint63) as [[[g0 acc] p]|] eqn:E; [|discriminate].
  intro H; inversion H; subst. rewrite finish_words_spec.
  destruct (@feed_acc_spec tm t j HT HJ _ _ _ _ _ _ _ E) as [out [HW HR]].
  change (words(fast_rev acc)++word p=out) in HW. rewrite HW; exact HR.
Qed.

Lemma feed_acc_app t j xs : forall ys g acc p,
  feed_acc t j (xs++ys) g acc p=match feed_acc t j xs g acc p with
  | None=>None | Some(g',acc',p')=>feed_acc t j ys g' acc' p' end.
Proof.
  induction xs; cbn; intros; [reflexivity|].
  destruct (get t g a) as [[g0 out]|]; [|reflexivity].
  destruct (push_words j out acc p) as [[acc0 p0]|]; [apply IHxs|reflexivity].
Qed.
Fixpoint feed_iter t j ws n g acc p := match n with
| O=>Some(g,acc,p)
| S n=>match feed_acc t j ws g acc p with None=>None
  | Some(g',acc',p')=>feed_iter t j ws n g' acc' p' end end.
Definition feed_pow t j ws n g := match feed_iter t j ws n g [] 1%uint63 with
| None=>None | Some(g',acc,p)=>Some(g',finish_words acc p) end.
Lemma feed_iter_eq t j ws n : forall g acc p,
  feed_iter t j ws n g acc p=feed_acc t j (ws^^n) g acc p.
Proof.
  induction n; intros; cbn[feed_iter lpow]; [reflexivity|].
  rewrite feed_acc_app; destruct (feed_acc t j ws g acc p) as [[[g0 acc0] p0]|]; auto.
Qed.
Lemma feed_pow_eq t j ws n g : feed_pow t j ws n g=feed t j (ws^^n) g.
Proof. unfold feed_pow,feed; rewrite feed_iter_eq; reflexivity. Qed.
Lemma words_pow ws n : words(ws^^n)=(words ws)^^n.
Proof. induction n; cbn[lpow]; [reflexivity|rewrite words_app,IHn; reflexivity]. Qed.

Fixpoint feed_state t ws g := match ws with
| []=>Some g | w::ws=>match get t g w with
  | None=>None | Some(g',_)=>feed_state t ws g' end end.
Fixpoint state_index g seen := match seen with
| []=>None | x::xs=>if Uint63.eqb g x then Some 0%nat else
  match state_index g xs with None=>None | Some n=>Some(1+n) end end.
Fixpoint cycle_params t ws fuel g seen := match fuel with
| O=>None | S fuel=>match state_index g seen with
  | Some i=>Some(i,List.length seen-i)
  | None=>match feed_state t ws g with
    | None=>None | Some g'=>cycle_params t ws fuel g' (seen++[g]) end end end.
Record Flow := flow {pre:list Uint63.int; period:list Uint63.int}.
Record Crossing := crossing {state:Uint63.int; warmup:nat; copies:nat; output:Flow}.
Definition advance t j g f := match feed t j (pre f) g with
| None=>None | Some(g1,pp)=>match cycle_params t (period f) 28 g1 [] with
  | None=>None | Some(k,m)=>match feed_pow t j (period f) k g1 with
    | None=>None | Some(g2,warm)=>match feed_pow t j (period f) m g2 with
      | None=>None | Some(g3,per)=>if Uint63.eqb g2 g3 then
        Some(crossing g2 k m (flow(pp++warm) per)) else None end end end end.
Definition FHalts tm f r := FlowHalts tm (words(pre f)) (words(period f)) r.
Lemma advance_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) g f c :
  advance t j g f=Some c ->
  segRLs tm (calls(words(pre f)++words(period f)^^warmup c))
    (calls(words(pre(output c)))) (block g) (block(state c)) /\
  segRLs tm (calls(words(period f)^^copies c))
    (calls(words(period(output c)))) (block(state c)) (block(state c)).
Proof.
  unfold advance; destruct (feed t j (pre f) g) as [[g1 pp]|] eqn:E0; [|discriminate].
  destruct (cycle_params t (period f) 28 g1 []) as [[k m]|]; [|discriminate].
  rewrite !feed_pow_eq.
  destruct (feed t j (period f^^k) g1) as [[g2 warm]|] eqn:E1; [|discriminate].
  rewrite feed_pow_eq.
  destruct (feed t j (period f^^m) g2) as [[g3 per]|] eqn:E2; [|discriminate].
  destruct (Uint63.eqb g2 g3) eqn:EG; [|discriminate].
  apply Uint63.eqb_spec in EG; subst g3.
  intro E; inversion E; subst; cbn[pre period output warmup copies state]; split.
  - rewrite words_app,!calls_app; eapply segRLs_trans.
    + eapply feed_spec; eauto.
    + rewrite <-words_pow; eapply feed_spec; eauto.
  - rewrite <-words_pow; eapply feed_spec; eauto.
Qed.
Lemma advance_halt tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) g f c r :
  advance t j g f=Some c -> FHalts tm (output c) r -> FHalts tm f (block g*>r).
Proof.
  intros E [n HH]; destruct (@advance_spec tm t j HT HJ g f c E) as [HP HC].
  exists (warmup c+n*copies c).
  eapply segRLs_sideRLs_halt_concat; [|exact HH].
  rewrite lpow_add,lpow_mul,app_assoc,!calls_app,!calls_pow.
  eapply segRLs_trans; [rewrite <-calls_pow,<-calls_app; exact HP|].
  apply seg_cycle_pow; rewrite <-!calls_pow; exact HC.
Qed.
End PackedColumns.

Import PackedSignals PackedColumns.
Module PackedRun.
Definition ResultSpec tm qs r (x:side+bool) := match x with
| inl r'=>sideRLs tm (calls qs) r r'
| inr b=>b=true -> sideRLs_halt tm (calls qs) r end.
Fixpoint raw tm fuel qs r : side+bool := match qs with
| []=>inl r
| q::qs=>match sideRL_halt_rec tm [] r q fuel with
  | Halted=>inr true | Returned A r'=>raw tm fuel qs r' | _=>inr false end end.
Lemma raw_spec tm fuel qs : forall r, ResultSpec tm qs r (raw tm fuel qs r).
Proof.
  induction qs as [|q qs IH]; intro r; cbn[raw ResultSpec]; [constructor|].
  pose proof (sideRL_halt_rec_spec tm fuel [] r q) as H.
  destruct (sideRL_halt_rec tm [] r q fuel) as [|q' r'|]; cbn[result_spec] in H.
  - discriminate.
  - destruct q'; [|discriminate]. specialize (IH r').
    destruct (raw tm fuel qs r') as [r''|b]; cbn[ResultSpec] in *.
    + econstructor; eauto.
    + intro E; econstructor 2; eauto.
  - intro E; constructor; exact H.
Qed.
Fixpoint raw_words tm fuel ws r : side+bool := match ws with
| []=>inl r | w::ws=>match raw tm fuel (word w) r with
  | inr b=>inr b | inl r'=>raw_words tm fuel ws r' end end.
Lemma raw_words_spec tm fuel ws : forall r,
  ResultSpec tm (words ws) r (raw_words tm fuel ws r).
Proof.
  induction ws as [|w ws IH]; intro r; cbn[raw_words words flat_map ResultSpec]; [constructor|].
  pose proof (raw_spec tm fuel (word w) r) as H.
  destruct (raw tm fuel (word w) r) as [r'|b]; cbn[ResultSpec] in H.
  - specialize (IH r'); destruct (raw_words tm fuel ws r') as [r''|b]; cbn[ResultSpec] in *;
      rewrite calls_app; eauto using sideRLs_trans,sideRLs_halt_app_right.
  - intro E; rewrite calls_app; apply sideRLs_halt_app_left,H,E.
Qed.

Definition Tape := (list Uint63.int * side)%type.
Fixpoint denote_groups gs r := match gs with []=>r | g::gs=>block g*>denote_groups gs r end.
Definition denote (x:Tape) := denote_groups (fst x) (snd x).
Definition TapeSpec tm qs x (y:Tape+bool) := match y with
| inl y=>sideRLs tm (calls qs) (denote x) (denote y)
| inr b=>b=true ->sideRLs_halt tm (calls qs) (denote x) end.
Fixpoint pipe tm t j fuel gs ws r : Tape+bool := match gs with
| []=>match raw_words tm fuel ws r with
  | inl r'=>inl([],r') | inr b=>inr b end
| g::gs=>match feed t j ws g with
  | None=>inr false
  | Some(g',out)=>match pipe tm t j fuel gs out r with
    | inl(gs',r')=>inl(g'::gs',r') | inr b=>inr b end end end.
Lemma pipe_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) fuel gs :
  forall ws r, TapeSpec tm (words ws) (gs,r) (pipe tm t j fuel gs ws r).
Proof.
  induction gs as [|g gs IH]; intros ws r; cbn[pipe].
  - pose proof (raw_words_spec tm fuel ws r) as H.
    destruct (raw_words tm fuel ws r); exact H.
  - destruct (feed t j ws g) as [[g' out]|] eqn:E; [|discriminate].
    pose proof (@feed_spec tm t j HT HJ ws g g' out E) as HS.
    specialize (IH out r); destruct (pipe tm t j fuel gs out r) as [[gs' r']|b];
      cbn[TapeSpec denote fst snd denote_groups] in *.
    + eapply segRLs_sideRLs_concat; eauto.
    + intro EB; eapply segRLs_sideRLs_halt_concat; eauto.
Qed.

(* Only already nonblank triples enter the table. The right frontier stays
   in the original-machine interpreter, including its exceptional B return. *)
Fixpoint split_tape fuel (r:side) : Tape := match fuel with
| O=>([],r)
| S fuel=>match r with a>>r1=>match r1 with b>>r2=>match r2 with c>>r3=>
    match r3 with d>>_=>if sym_eqb d 0 then ([],r) else
    match block_code [a;b;c] with
    | None=>([],r) | Some g=>let '(gs,rest):=split_tape fuel r3 in (g::gs,rest)
    end end end end end end.
Lemma split_tape_spec fuel : forall r, denote(split_tape fuel r)=r.
Proof.
  induction fuel; intro r; [reflexivity|].
  destruct r as [a [b [c [d r]]]]; cbn[split_tape].
  destruct (sym_eqb d 0); [reflexivity|].
  destruct (block_code [a;b;c]) as [g|] eqn:E; [|reflexivity].
  specialize (IHfuel (d>>r)); destruct (split_tape fuel (d>>r)) as [gs rest].
  cbn[denote fst snd denote_groups] in *.
  rewrite (@block_code_spec [a;b;c] g E),IHfuel; reflexivity.
Qed.
Lemma denote_groups_app xs : forall ys r,
  denote_groups (xs++ys) r=denote_groups xs (denote_groups ys r).
Proof. induction xs; cbn; intros; [reflexivity|rewrite IHxs; reflexivity]. Qed.
Definition grow '(gs,r) : Tape := let '(more,rest):=split_tape 80 r in (gs++more,rest).
Lemma grow_spec x : denote(grow x)=denote x.
Proof.
  destruct x as [gs r]; unfold grow.
  pose proof (split_tape_spec 80 r) as H; destruct (split_tape 80 r) as [more rest].
  change (denote_groups more rest=r) in H.
  change (denote_groups (gs++more) rest=denote_groups gs r).
  rewrite denote_groups_app,H; reflexivity.
Qed.

Record Config := config { tape:Tape; todo:list Uint63.int }.
Definition Future tm period x := FlowHalts tm (words(todo x)) (words period) (denote(tape x)).
Definition batch tm t j rawfuel period x : Config+bool :=
  let input:=match todo x with []=>period | xs=>xs end in
  match input with []=>inr false | _=>
    match pipe tm t j rawfuel (fst(tape x)) (firstn 4096 input) (snd(tape x)) with
    | inr b=>inr b | inl y=>inl(config(grow y)(skipn 4096 input)) end end.
Lemma consume tm xs ys period r r' : sideRLs tm (calls(words xs)) r r' ->
  FlowHalts tm (words ys) (words period) r' ->
  FlowHalts tm (words(xs++ys)) (words period) r.
Proof.
  intros HR [n H]; exists n; rewrite words_app,<-app_assoc,!calls_app.
  eapply sideRLs_halt_app_right; [exact HR|rewrite <-calls_app; exact H].
Qed.
Lemma consume_halt tm xs ys period r : sideRLs_halt tm (calls(words xs)) r ->
  FlowHalts tm (words(xs++ys)) (words period) r.
Proof.
  intro H; exists 0%nat; cbn[lpow]; rewrite app_nil_r,words_app,calls_app.
  apply sideRLs_halt_app_left,H.
Qed.
Lemma unfold_period tm period r : FlowHalts tm (words period) (words period) r ->
  FlowHalts tm [] (words period) r.
Proof. intros [n H]; exists (1+n); exact H. Qed.
Lemma batch_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) fuel period x :
  (match batch tm t j fuel period x with inl y=>Future tm period y | inr b=>b=true end) ->
  Future tm period x.
Proof.
  destruct x as [[gs r] pending]; cbn[batch tape todo].
  assert (HELP:forall input, input<>[] ->
    (match pipe tm t j fuel gs (firstn 4096 input) r with
     | inl y=>Future tm period (config(grow y)(skipn 4096 input)) | inr b=>b=true end) ->
    FlowHalts tm (words input) (words period) (denote(gs,r))). {
    intros input HNE; pose proof (@pipe_spec tm t j HT HJ fuel gs (firstn 4096 input) r) as H.
    destruct (pipe tm t j fuel gs (firstn 4096 input) r) as [y|b]; cbn[TapeSpec] in H.
    - unfold Future; cbn[tape todo]; rewrite grow_spec; intro HH.
      rewrite <- (firstn_skipn 4096 input); eapply consume; eauto.
    - intro EB; rewrite <- (firstn_skipn 4096 input); eapply consume_halt; eauto. }
  destruct pending as [|w ws].
  - destruct period as [|p ps]; [discriminate|]. intro H; apply unfold_period; apply HELP; [discriminate|].
    unfold batch in H; cbn[tape todo fst snd] in *.
    destruct (pipe tm t j fuel gs (firstn 4096 (p::ps)) r); exact H.
  - intro H; apply HELP; [discriminate|].
    unfold batch in H; cbn[tape todo fst snd] in *.
    destruct (pipe tm t j fuel gs (firstn 4096 (w::ws)) r); exact H.
Qed.
Definition run tm t j rawfuel period x fuel := Eqb.N_iter_until (batch tm t j rawfuel period) (inl x) fuel.
Lemma run_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) rawfuel period x fuel :
  run tm t j rawfuel period x fuel=inr true -> Future tm period x.
Proof.
  pose proof (@Eqb.N_iter_until_spec Config bool (batch tm t j rawfuel period) (inl x) fuel
    (fun y=>Future tm period y ->Future tm period x)
    (fun b=>b=true ->Future tm period x)) as H.
  unfold run; intro E; rewrite E in H; apply H; [|auto|reflexivity].
  intros y HY; pose proof (@batch_spec tm t j HT HJ rawfuel period y) as HS.
  destruct (batch tm t j rawfuel period y); auto.
Qed.
End PackedRun.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB3RB3LA4LA2RB_2LB3RA---1RA1LA").
Definition tr : LocalTable := fun q s => match q,s with
| A,1=>Some(4,[B]) | B,1=>Some(4,[A])
| A,2=>Some(3,[]) | B,2=>None
| A,3=>Some(4,[]) | B,3=>Some(4,[A;B])
| A,4=>Some(3,[B]) | B,4=>Some(1,[])
| _,0=>None end.
Definition L n := 0inf <* <[3;3;2;3;1]^^n.
Lemma emit1 n r : L n <* <[3;3] <{{A}} r -[tm]->+ L n <* <[3;3;2] {{B}}> r.
Proof. unfold L. es. Qed.
Lemma emit2 n r : L n <* <[3;3;2] <{{A}} r -[tm]->+ L n <* <[3;3;2;1] {{A}}> r.
Proof. unfold L. es. Qed.
Lemma emit3 n r : L n <* <[3;3;2;1] <{{A}} r -[tm]->+ L n <* <[3;3;2;3] {{B}}> r.
Proof. unfold L. es. Qed.
Lemma emit4 n r : L n <* <[3;3;2;3] <{{A}} r -[tm]->+ L n <* <[3;3;2;1;2] {{B}}> r.
Proof. unfold L. es. Qed.
Lemma emit5 n r : L n <* <[3;3;2;1;2] <{{A}} r -[tm]->+ L n <* <[3;3;2;3;1] {{A}}> r.
Proof. unfold L. es. Qed.
Lemma emit6 n r : L n <* <[3;3;2;3;1] <{{A}} r -[tm]->+ L n <* <[3;3;2;3;3] {{B}}> r.
Proof. unfold L. es. Qed.
Lemma emit7 n r : L n <* <[3;3;2;3;3] <{{A}} r -[tm]->+ L n <* <[3;3;2;3;1;3] {{B}}> r.
Proof. unfold L. es. Qed.
Lemma emit8 n r : L n <* <[3;3;2;3;1;3] <{{A}} r -[tm]->+ L (1+n) <* <[3;3] {{A}}> r.
Proof. unfold L. es. Qed.
Definition emit_period := [A;B;A;B;B;A;B;B].
Definition left n := L n <* <[3;3].
Lemma left_round n : LeftRun tm [B;A;B;B;A;B;B;A] (left n) (left (1+n)).
Proof.
  unfold left; econstructor; [apply emit1|]. econstructor; [apply emit2|].
  econstructor; [apply emit3|]. econstructor; [apply emit4|].
  econstructor; [apply emit5|]. econstructor; [apply emit6|].
  econstructor; [apply emit7|]. econstructor; [apply emit8|constructor].
Qed.
Lemma init : c0 -[tm]->* left 0 {{A}}> [4;4] *> 0inf.
Proof. unfold left,L; es. Qed.
Lemma from_flow : FlowHalts tm [] emit_period ([4;4] *> 0inf) -> halts tm c0.
Proof.
  intro H; eapply halts_evstep; [|exact init].
  eapply (@left_period_halt tm A [B;A;B;B;A;B;B] left).
  - apply left_round.
  - exact H.
Qed.
Import PackedSignals PackedColumns PackedRun.
Definition table := make_table tr.
Definition joins := join_table.
Definition tables_ok := if table_ok tm table then join_ok joins else false.
Definition input := PackedColumns.flow [] [encode emit_period].
Fixpoint warmup (n:nat) r : side+bool := match n with
| O=>inl r
| S n=>match raw tm 10000 emit_period r with
  | inl r'=>warmup n r' | inr b=>inr b end end.
Lemma warmup_spec n : forall r,
  (match warmup n r with inl r'=>FlowHalts tm [] emit_period r' | inr b=>b=true end) ->
  FlowHalts tm [] emit_period r.
Proof.
  induction n; intro r; cbn[warmup]; [auto|].
  pose proof (raw_spec tm 10000 emit_period r) as H.
  destruct (raw tm 10000 emit_period r) as [r'|b]; cbn[ResultSpec] in H.
  - intro E; destruct (IHn _ E) as [k HK]; exists (1+k).
    change (sideRLs_halt tm (calls(emit_period++emit_period^^k)) r).
    rewrite calls_app; eapply sideRLs_halt_app_right; eauto.
  - intro E; exists 1%nat; change (sideRLs_halt tm (calls emit_period) r); apply H,E.
Qed.
Fixpoint lower n t j gs f := match n with
| O=>Some(gs,f)
| S n=>match gs with []=>None | g::gs=>match advance t j g f with
  | None=>None | Some c=>lower n t j gs (output c) end end end.
Lemma lower_spec tm t j (HT:table_ok tm t=true) (HJ:join_ok j=true) n :
  forall gs f gs' f' r, lower n t j gs f=Some(gs',f') ->
  FHalts tm f' (denote(gs',r)) -> FHalts tm f (denote(gs,r)).
Proof.
  induction n; intros gs f gs' f' r; cbn[lower].
  - intro E; inversion E; subst; auto.
  - destruct gs as [|g gs]; [discriminate|].
    destruct (advance t j g f) as [c|] eqn:E; [|discriminate].
    intros EE HH; change (FHalts tm f (block g*>denote(gs,r))).
    eapply (@advance_halt tm t j HT HJ g f c _ E); eapply IHn; eauto.
Qed.
Definition prepare_from n table joins seed := match warmup 10000 seed with
| inr b=>inr b
| inl r=>let '(gs,tail):=split_tape 80 r in
  match lower n table joins gs input with
  | None=>inr false
  | Some(gs',f)=>inl(f,config(gs',tail)(pre f)) end end.
Definition check_from n table joins seed fuel := if table_ok tm table then if join_ok joins then
  match prepare_from n table joins seed with
  | inr b=>b
  | inl(f,x)=>match run tm table joins 10000 (period f) x fuel with
    | inr b=>b | inl _=>false end end else false else false.
Opaque table joins warmup.
Lemma check_from_spec n table joins seed fuel : check_from n table joins seed fuel=true -> FlowHalts tm [] emit_period seed.
Proof.
  unfold check_from.
  destruct (table_ok tm table) eqn:HT; [|discriminate].
  destruct (join_ok joins) eqn:HJ; [|discriminate].
  intro HC; apply (warmup_spec 10000).
  unfold prepare_from in HC; destruct (warmup 10000 seed) as [r|b]; [|exact HC].
  pose proof (split_tape_spec 80 r) as HR.
  destruct (split_tape 80 r) as [gs tail].
  destruct (lower n table joins gs input) as [[gs' f]|] eqn:E; [|discriminate].
  destruct (run tm table joins 10000 (period f) (config(gs',tail)(pre f)) fuel) as [y|b] eqn:ER;
    [discriminate|].
  subst b. apply (@run_spec tm table joins HT HJ) in ER.
  rewrite <-HR. change (FHalts tm input (denote(gs,tail))).
  exact (@lower_spec tm table joins HT HJ n gs input gs' f tail E ER).
Qed.
Definition prepare n := prepare_from n table joins ([4;4]*>0inf).
Definition check n fuel := check_from n table joins ([4;4]*>0inf) fuel.
Lemma check_spec n table joins fuel : check_from n table joins ([4;4]*>0inf) fuel=true -> halts tm c0.
Proof.
  intro H; apply from_flow.
  exact (@check_from_spec n table joins ([4;4]*>0inf) fuel H).
Qed.
(* FINAL LONG COMPUTATION *)
(* Cut after 11 triples; stop as soon as the right frontier halts.
   This final computation is left for the user; see LA2x5_4_COQ.md. *)
Theorem halt: halts tm c0.
Proof.
  apply (@check_spec 11 table joins 200000000%N).
  native_check_eq.
Qed.

Print Assumptions halt.
End TM4.

