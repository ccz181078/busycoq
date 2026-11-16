From BusyCoq Require Import Individual25 FastRev LongitudinalHalt25.
From Coq Require Import List String NArith ZifyNat Lia.
Import ListNotations.
Set Implicit Arguments.

Definition LocalTable := Q -> Sym -> option (Sym * list Q).
Record Flow := flow {pre:list Q; period:list Q}.
Record Crossing := crossing {
  cycle_state:Sym; warmup:nat; copies:nat; output:Flow }.

Fixpoint feed_acc (tr:LocalTable) qs s acc := match qs with
| [] => Some (s,fast_rev acc)
| q::qs => match tr q s with
  | None => None
  | Some(s,ws) => feed_acc tr qs s (fast_rev_append ws acc)
  end end.
Definition feed tr qs s := feed_acc tr qs s [].

(* Repeated periods are traversed without constructing [qs^^n]. *)
Fixpoint feed_rev (tr:LocalTable) qs s acc := match qs with
| []=>Some(s,acc)
| q::qs=>match tr q s with None=>None
  | Some(s,ws)=>feed_rev tr qs s (fast_rev_append ws acc) end end.
Fixpoint feed_iter tr qs n s acc := match n with
| O=>Some(s,acc)
| S n=>match feed_rev tr qs s acc with None=>None
  | Some(s,acc)=>feed_iter tr qs n s acc end end.
Definition feed_pow tr qs n s := match feed_iter tr qs n s [] with
| None=>None | Some(s,acc)=>Some(s,fast_rev acc) end.
Lemma feed_rev_app tr xs : forall ys s acc,
  feed_rev tr (xs++ys) s acc = match feed_rev tr xs s acc with
  | None=>None |Some(s,acc)=>feed_rev tr ys s acc end.
Proof.
  induction xs; cbn; intros; [reflexivity|].
  destruct (tr a s) as [[s' ws]|]; [apply IHxs|reflexivity].
Qed.
Lemma feed_iter_eq tr qs n : forall s acc,
  feed_iter tr qs n s acc=feed_rev tr (qs^^n) s acc.
Proof.
  induction n; cbn[feed_iter lpow]; intros; [reflexivity|].
  rewrite feed_rev_app; destruct (feed_rev tr qs s acc) as [[s' acc']|]; auto.
Qed.
Lemma feed_acc_rev tr qs : forall s acc,
  feed_acc tr qs s acc=match feed_rev tr qs s acc with
  | None=>None |Some(s,acc)=>Some(s,fast_rev acc) end.
Proof.
  induction qs; cbn; intros; [reflexivity|].
  destruct (tr a s) as [[s' ws]|]; [apply IHqs|reflexivity].
Qed.
Lemma feed_pow_eq tr qs n s : feed_pow tr qs n s=feed tr (qs^^n) s.
Proof. unfold feed_pow,feed; rewrite feed_iter_eq,feed_acc_rev; reflexivity. Qed.

Fixpoint feed_state (tr:LocalTable) qs s := match qs with
| []=>Some s
| q::qs=>match tr q s with None=>None |Some(s,_)=>feed_state tr qs s end end.
Fixpoint state_index s (seen:list Sym) := match seen with
| []=>None
| s'::seen=>if sym_eqb s s' then Some 0%nat else
    match state_index s seen with None=>None |Some i=>Some(1+i) end end.
Fixpoint cycle_params tr p fuel s seen := match fuel with
| O=>None
| S fuel=>match state_index s seen with
  | Some i=>Some(i,List.length seen-i)
  | None=>match feed_state tr p s with
    | None=>None |Some s'=>cycle_params tr p fuel s' (seen++[s]) end end end.

Definition advance tr s f := match feed tr (pre f) s with
| None => None
| Some(s,pp) => match period f with
  | [] => Some(crossing s 0 0 (flow pp []))
  | p => match cycle_params tr p 6 s [] with
    | None=>None
    | Some(k,m)=>match feed_pow tr p k s with
      | None=>None
      | Some(s',warm)=>match feed_pow tr p m s' with
        | None=>None
        | Some(s'',per)=>if sym_eqb s' s'' then
            Some(crossing s' k m (flow (pp++warm) per)) else None
        end end end end end.
Fixpoint columns tr n ss f := match n with
| O => Some f
| S n => match ss with
  | [] => match advance tr 0 f with None=>None |Some c=>columns tr n [] (output c) end
  | s::ss => match advance tr s f with None=>None |Some c=>columns tr n ss (output c) end
  end end.

Definition TableSpec tm (tr:LocalTable) := forall q s s' qs,
  tr q s=Some(s',qs) -> segRLs tm (calls [q]) (calls qs) [s] [s'].
Lemma calls_app xs ys : calls (xs++ys)=calls xs++calls ys.
Proof. apply List.map_app. Qed.
Lemma reverse_acc {X} (xs acc:list X) : fast_rev (fast_rev_append xs acc)=fast_rev acc++xs.
Proof. rewrite !fast_rev_spec,fast_rev_append_spec,List.rev_app_distr,List.rev_involutive; reflexivity. Qed.

Lemma feed_acc_spec tm tr (HT:TableSpec tm tr) qs : forall s acc s' ws,
  feed_acc tr qs s acc=Some(s',ws) -> exists out,
    ws=fast_rev acc++out /\ segRLs tm (calls qs) (calls out) [s] [s'].
Proof.
  induction qs as [|q qs IH]; intros s acc s' ws; cbn[feed_acc].
  - intro H; inversion H; subst; exists (@nil Q); split; [rewrite app_nil_r; reflexivity|constructor].
  - destruct (tr q s) as [[s0 out]|] eqn:E; [|discriminate]; intro H.
    destruct (IH _ _ _ _ H) as [rest [EW HR]].
    exists (out++rest); split.
    + rewrite EW,reverse_acc,app_assoc; reflexivity.
    + change (calls (q::qs)) with (calls [q]++calls qs); rewrite calls_app.
      eapply segRLs_trans; [apply HT; exact E|exact HR].
Qed.
Lemma feed_spec tm tr (HT:TableSpec tm tr) qs s s' ws :
  feed tr qs s=Some(s',ws) -> segRLs tm (calls qs) (calls ws) [s] [s'].
Proof. intro H; destruct (@feed_acc_spec tm tr HT qs s [] s' ws H) as [out [-> HR]]; exact HR. Qed.

Lemma advance_spec tm tr (HT:TableSpec tm tr) s f c : advance tr s f=Some c ->
  segRLs tm (calls (pre f++period f^^warmup c)) (calls (pre(output c))) [s] [cycle_state c] /\
  segRLs tm (calls (period f^^copies c)) (calls (period(output c))) [cycle_state c] [cycle_state c].
Proof.
  unfold advance; destruct (feed tr (pre f) s) as [[s1 pp]|] eqn:E0; [|discriminate].
  destruct (period f) as [|q p] eqn:EP.
  - intro H; inversion H; subst; cbn[pre period output warmup copies cycle_state lpow].
    rewrite app_nil_r; split; [eapply feed_spec; eauto|constructor].
  - destruct (cycle_params tr (q::p) 6 s1 []) as [[k m]|]; [|discriminate].
    rewrite !feed_pow_eq.
    destruct (feed tr ((q::p)^^k) s1) as [[s2 warm]|] eqn:E1; [|discriminate].
    rewrite feed_pow_eq.
    destruct (feed tr ((q::p)^^m) s2) as [[s3 per]|] eqn:E2; [|discriminate].
    destruct (sym_eqb_spec s2 s3); [subst s3|discriminate].
    intro H; inversion H; subst; cbn[pre period output warmup copies cycle_state].
    split.
    + rewrite !calls_app; eapply segRLs_trans; eapply feed_spec; eauto.
    + eapply feed_spec; eauto.
Qed.

Lemma calls_pow qs n : calls (qs^^n)=(calls qs)^^n.
Proof. induction n; cbn[lpow]; [reflexivity|rewrite calls_app,IHn; reflexivity]. Qed.
Lemma seg_cycle_pow tm u v w n : segRLs tm u v w w -> segRLs tm (u^^n) (v^^n) w w.
Proof. intro H; induction n; cbn[lpow]; [constructor|eapply segRLs_trans; eauto]. Qed.

Lemma advance_halt tm tr (HT:TableSpec tm tr) s f c r : advance tr s f=Some c ->
  FlowHalts tm (pre(output c)) (period(output c)) r -> FlowHalts tm (pre f) (period f) (s>>r).
Proof.
  intros E [n HH]; destruct (@advance_spec tm tr HT s f c E) as [HP HC].
  exists (warmup c+n*copies c).
  eapply (@segRLs_sideRLs_halt_concat tm _ _ [s] [cycle_state c] r); [|exact HH].
  rewrite lpow_add,lpow_mul,app_assoc,!calls_app,!calls_pow.
  eapply segRLs_trans; [rewrite <-calls_pow,<-calls_app; exact HP|].
  apply seg_cycle_pow; rewrite <-!calls_pow; exact HC.
Qed.
Lemma columns_halt tm tr (HT:TableSpec tm tr) n : forall ss f g,
  columns tr n ss f=Some g -> FlowHalts tm (pre g) (period g) (skipn n ss*>0inf) ->
  FlowHalts tm (pre f) (period f) (ss*>0inf).
Proof.
  induction n; intros ss f g; cbn[columns].
  - intro E; inversion E; subst; trivial.
  - destruct ss as [|s ss].
    + destruct (advance tr 0 f) as [c|] eqn:E; [|discriminate].
      intros H HH; rewrite List.skipn_nil in HH.
      specialize (IHn [] _ _ H); rewrite List.skipn_nil in IHn; specialize (IHn HH).
      applys_eq (@advance_halt tm tr HT 0 f c 0inf E IHn).
      rewrite <-const_unfold; reflexivity.
    + destruct (advance tr s f) as [c|] eqn:E; [|discriminate].
      intros H HH; eapply (@advance_halt tm tr HT s f c (ss*>0inf)); [exact E|eapply IHn; eauto].
Qed.

Definition check_columns tm tr n seed input fuel := match columns tr n seed input with
| None=>false
| Some f=>flow_halt_c tm (pre f) (period f) (skipn n seed*>0inf) fuel end.
Lemma check_columns_spec tm tr (HT:TableSpec tm tr) n seed input fuel :
  check_columns tm tr n seed input fuel=true ->
  FlowHalts tm (pre input) (period input) (seed*>0inf).
Proof.
  unfold check_columns; destruct (columns tr n seed input) as [f|] eqn:E; [|discriminate].
  intro H; eapply columns_halt; [exact HT|exact E|eapply flow_halt_c_spec; exact H].
Qed.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB3LA4LA2RB1LA_2LA4RB---3RA3LA").
Definition tr : LocalTable := fun q s => match q,s with
| A,0=>Some(3,[B]) | A,1=>Some(3,[]) | A,2=>Some(4,[]) | A,3=>Some(4,[B]) | A,4=>Some(1,[])
| B,0=>Some(2,[]) | B,1=>Some(1,[B]) | B,2=>None | B,3=>Some(4,[A;B]) | B,4=>Some(3,[]) end.
Lemma tr_spec : TableSpec tm tr.
Proof.
  intros q s s' qs; destruct q,s; cbn[tr]; intro H; inversion H; subst;
    apply BoundedConfig.segRLs_c_spec with (T:=10); reflexivity.
Qed.
Definition seed := [1;3].
Definition input := flow [] [B].
Definition snapshot n := columns tr n seed input.
Definition check n fuel := check_columns tm tr n seed input fuel.

Definition left n := 0inf <* <[1;2] <* [4]^^n.
Lemma emit n r : left n <{{A}} r -[tm]->+ left (1+n) {{B}}> r.
Proof. unfold left; es. Qed.
Lemma init : c0 -[tm]->* left 0 {{B}}> seed *> 0inf.
Proof. unfold left,seed; es. Qed.
Lemma check_spec n fuel : check n fuel=true -> halts tm c0.
Proof.
  intro H; eapply halts_evstep; [|exact init].
  eapply (@left_period_halt tm B [] left).
  - intro k; econstructor; [apply emit|constructor].
  - exact (@check_columns_spec tm tr tr_spec n seed input fuel H).
Qed.

Theorem halt : halts tm c0.
Proof. apply check_spec with (n:=36) (fuel:=50000%N); native_check_eq. Time Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB3LA4LA1LA2RA_2LA4RB---0RA0LA").
Definition tr : LocalTable := fun q s => match q,s with
| A,0=>Some(3,[B]) | A,1=>Some(3,[]) | A,2=>Some(4,[]) | A,3=>Some(1,[]) | A,4=>Some(4,[A])
| B,0=>Some(2,[]) | B,1=>Some(4,[B;A]) | B,2=>None | B,3=>Some(3,[A;B]) | B,4=>Some(0,[]) end.
Lemma tr_spec : TableSpec tm tr.
Proof.
  intros q s s' qs; destruct q,s; cbn[tr]; intro H; inversion H; subst;
    apply BoundedConfig.segRLs_c_spec with (T:=10); reflexivity.
Qed.
Definition seed := [3;3;3].
Definition input := flow [] [B;A;B;B;A].
Definition snapshot n := columns tr n seed input.
Definition check n fuel := check_columns tm tr n seed input fuel.
Definition left n := 0inf <* <[1;1;2] <* <[1;1;2]^^n <* [1].
Lemma emit1 n r : left n <{{A}} r -[tm]->+ left n << 0 {{A}}> r.
Proof. unfold left; es. Qed.
Lemma emit2 n r : left n << 0 <{{A}} r -[tm]->+ left n << 1 {{B}}> r.
Proof. es. Qed.
Lemma emit3 n r : left n << 1 <{{A}} r -[tm]->+ left n << 1 << 4 {{B}}> r.
Proof. unfold left; es; finish. Qed.
Lemma emit4 n r : left n << 1 << 4 <{{A}} r -[tm]->+ left n << 1 << 2 {{A}}> r.
Proof. es. Qed.
Lemma emit5 n r : left n << 1 << 2 <{{A}} r -[tm]->+ left (1+n) {{B}}> r.
Proof. unfold left; es; finish. Qed.
Lemma init : c0 -[tm]->* left 0 {{B}}> seed *> 0inf.
Proof. unfold left,seed; es. Qed.
Lemma check_spec n fuel : check n fuel=true -> halts tm c0.
Proof.
  intro H; eapply halts_evstep; [|exact init].
  eapply (@left_period_halt tm B [A;B;B;A] left).
  - intro k; econstructor; [apply emit1|].
    econstructor; [apply emit2|].
    econstructor; [apply emit3|].
    econstructor; [apply emit4|].
    econstructor; [apply emit5|constructor].
  - exact (@check_columns_spec tm tr tr_spec n seed input fuel H).
Qed.

Theorem halt : halts tm c0.
Proof. apply check_spec with (n:=47) (fuel:=9000000%N); native_check_eq. Time Qed.

End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB2RA3LA4LA2RB_2LA---1LA1RA3RA").
Definition tr : LocalTable := fun q s => match q,s with
| A,0=>Some(3,[B;A]) | A,1=>Some(3,[A]) | A,2=>Some(3,[]) | A,3=>Some(4,[]) | A,4=>Some(3,[B])
| B,0=>Some(2,[]) | B,1=>None | B,2=>Some(1,[]) | B,3=>Some(3,[A;A]) | B,4=>Some(4,[A]) end.
Lemma tr_spec : TableSpec tm tr.
Proof.
  intros q s s' qs; destruct q,s; cbn[tr]; intro H; inversion H; subst;
    apply BoundedConfig.segRLs_c_spec with (T:=10); reflexivity.
Qed.
Definition seed := [3;4;4;4].
Definition input := flow [] [B;A;A].
Definition snapshot n := columns tr n seed input.
Definition check n fuel := check_columns tm tr n seed input fuel.
Definition left n := 0inf <* <[1;1;2;3] <* [2]^^(3+n*2).
Lemma emit1 n r : left n <{{A}} r -[tm]->+ left n << 1 {{A}}> r.
Proof. unfold left; es. Qed.
Lemma emit2 n r : left n << 1 <{{A}} r -[tm]->+ left n << 2 {{A}}> r.
Proof. es. Qed.
Lemma emit3 n r : left n << 2 <{{A}} r -[tm]->+ left (1+n) {{B}}> r.
Proof. unfold left; es. Qed.
Lemma init : c0 -[tm]->* left 0 {{B}}> seed *> 0inf.
Proof. unfold left,seed; es. Qed.
Lemma check_spec n fuel : check n fuel=true -> halts tm c0.
Proof.
  intro H; eapply halts_evstep; [|exact init].
  eapply (@left_period_halt tm B [A;A] left).
  - intro k; econstructor; [apply emit1|].
    econstructor; [apply emit2|].
    econstructor; [apply emit3|constructor].
  - exact (@check_columns_spec tm tr tr_spec n seed input fuel H).
Qed.

Theorem halt : halts tm c0.
Proof. apply check_spec with (n:=30) (fuel:=17000000%N); native_check_eq. Time Qed.

End TM3.

Print Assumptions TM1.halt.
Print Assumptions TM2.halt.
Print Assumptions TM3.halt.

