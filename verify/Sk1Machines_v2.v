(* Sk1 Class1 TM23, TM25 and TM26; TM25/26 reconstruct PR42.
   Ten local counter rules + RLE/affine symbolic execution, in the style of
   Sk1Machines.v. No PR execution trace or block certificate is imported.
   Counts are binary N; expansion to nat occurs only in specifications. *)
From BusyCoq Require Import Individual62 Helper Eqb FastRev ES_v3 Permute.
Require Import NArith PeanoNat ZifyNat Lia String List.
Import Eqb.
Open Scope sym_scope.

Module Affine.
Definition t := (N * list N)%type.
Fixpoint dot (xs:list N) (rho:list N) : N := match xs,rho with
  | a::xs,x::rho => (a*x+dot xs rho)%N | _,_ => 0%N end.
Definition value rho (e:t) := (fst e+dot (snd e) rho)%N.
Definition val rho e := N.to_nat (value rho e).
Definition const (n:N) : t := (n,[]).
Fixpoint adds (xs ys:list N) := match xs,ys with
  | [],_ => ys | _,[] => xs | a::xs,b::ys => (a+b)%N::adds xs ys end.
Definition add (e f:t) : t := ((fst e+fst f)%N,adds (snd e) (snd f)).
Definition scale k (e:t) : t := ((k*fst e)%N,map (N.mul k) (snd e)).
Definition sub k (e:t) : option t :=
  if (k<=?fst e)%N then Some ((fst e-k)%N,snd e) else None.
Definition zero (e:t) := (fst e=?0)%N && forallb (fun a=>(a=?0)%N) (snd e).

Lemma dot_adds rho xs ys : dot (adds xs ys) rho=(dot xs rho+dot ys rho)%N.
Proof. gen ys rho. induction xs; intros [|b ys] [|x rho]; cbn; try lia.
  rewrite IHxs. nia. Qed.
Lemma dot_scale rho k xs : dot (map (N.mul k) xs) rho=(k*dot xs rho)%N.
Proof. gen rho. induction xs; intros [|x rho]; cbn; try lia. rewrite IHxs. nia. Qed.
Lemma dot_zero rho xs : forallb (fun a=>(a=?0)%N) xs=true -> dot xs rho=0%N.
Proof. gen rho. induction xs; intros [|x rho]; cbn; intros; try reflexivity.
  destruct (N.eqb_spec a 0); [subst; cbn in *; apply IHxs; assumption|discriminate]. Qed.
Lemma val_const rho k : val rho (const k)=N.to_nat k.
Proof. unfold val,value,const. cbn. rewrite N.add_0_r. reflexivity. Qed.
Lemma val_add rho e f : val rho (add e f)=val rho e+val rho f.
Proof. destruct e,f. unfold val,value,add; cbn. rewrite dot_adds.
  rewrite !N2Nat.inj_add. lia. Qed.
Lemma val_scale rho k e : val rho (scale k e)=N.to_nat k*val rho e.
Proof. destruct e. unfold val,value,scale; cbn. rewrite dot_scale.
  rewrite !N2Nat.inj_add,!N2Nat.inj_mul. nia. Qed.
Lemma val_sub rho k e f : sub k e=Some f -> val rho e=N.to_nat k+val rho f.
Proof. destruct e as [c xs]. unfold sub. cbn. destruct (N.leb_spec k c); try discriminate.
  intros E; inverts E. unfold val,value; cbn. rewrite !N2Nat.inj_add. lia. Qed.
Lemma val_zero rho e : zero e=true -> val rho e=0%nat.
Proof. destruct e as [c xs]. unfold zero; cbn. destruct (N.eqb_spec c 0); try discriminate.
  subst. intros E. unfold val,value; cbn. rewrite dot_zero by exact E. reflexivity. Qed.
End Affine.

Module AffineRuns.
Definition t := list (list Sym * Affine.t).
Fixpoint denote rho (s:t) : side := match s with
  | [] => 0inf | (w,n)::s => w^^Affine.val rho n *> denote rho s end.
Definition push w n (s:t) :=
  if Affine.zero n then s else match w,s with
  | [],_ => s
  | _,(v,m)::s' => if eqb w v then (w,Affine.add n m)::s' else (w,n)::s
  | _,[] => if eqb w [0;0;0;0] then [] else [(w,n)] end.

Lemma nil_power {A} n : (@nil A)^^n=[].
Proof. induction n; cbn; assumption || reflexivity. Qed.
Lemma zeros4 n : [0;0;0;0]^^n *> 0inf=0inf.
Proof. induction n; cbn [lpow]; [reflexivity|].
  rewrite Str_app_assoc,IHn. cbn. rewrite <-!const_unfold. reflexivity. Qed.
Lemma push_spec rho w n s : denote rho (push w n s)=w^^Affine.val rho n *> denote rho s.
Proof.
  unfold push. destruct (Affine.zero n) eqn:E.
  - rewrite Affine.val_zero by exact E. reflexivity.
  - destruct w as [|b w]; [rewrite nil_power; reflexivity|].
    destruct s as [|[v m] s]; cbn [denote].
    + destruct (eqb_spec (b::w) [0;0;0;0]) as [Ew|Ew];
        [rewrite Ew; symmetry; apply zeros4|reflexivity].
    +
    destruct (eqb_spec (b::w) v); subst; cbn [denote]; [|reflexivity].
    rewrite Affine.val_add,lpow_add,Str_app_assoc. reflexivity.
Qed.

Definition pop (s:t) : option (list Sym*t) := match s with
  | [] => Some ([0;0;0;0],[])
  | (w,n)::s => match Affine.sub 1 n with
    | Some m => Some (w,push w m s) | None => None end end.

Lemma pop_spec rho s w s' : pop s=Some(w,s') -> denote rho s=w *> denote rho s'.
Proof.
  destruct s as [|[v n] s]; cbn [pop].
  - intros H; inverts H. cbn [denote Str_app]. rewrite <-!const_unfold. reflexivity.
  - destruct (Affine.sub 1 n) as [m|] eqn:E; try discriminate.
    intros H; inverts H. cbn [denote]. rewrite push_spec,(Affine.val_sub rho _ _ _ E).
    change (N.to_nat 1) with 1%nat. cbn [Nat.add lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Fixpoint cut k s : option(list (list Sym)*t) := match k with
  | O => Some ([],s)
  | S k => match pop s with
    | Some(w,s) => match cut k s with
      | Some(v,s) => Some(w::v,s) | None => None end
    | None => None end end.
Lemma cut_spec rho k s w s' : cut k s=Some(w,s') -> denote rho s=List.concat w *> denote rho s'.
Proof.
  gen s w s'. induction k; intros s w s' H; cbn [cut] in H.
  - inverts H. reflexivity.
  - destruct (pop s) as [[u t]|] eqn:E; try discriminate.
    destruct (cut k t) as [[v t']|] eqn:F; inverts H.
    rewrite (pop_spec rho _ _ _ E),(IHk _ _ _ F). cbn [List.concat].
    rewrite Str_app_assoc. reflexivity.
Qed.
Definition push_words ws s := fold_right (fun w s=>push w (Affine.const 1) s) s ws.
Lemma push_words_spec rho ws s : denote rho (push_words ws s)=List.concat ws *> denote rho s.
Proof. induction ws; [reflexivity|].
  change (denote rho (push a (Affine.const 1) (push_words ws s))=
    (a++List.concat ws) *> denote rho s).
  rewrite push_spec,Affine.val_const. change (N.to_nat 1) with 1%nat.
  cbn [lpow]. rewrite app_nil_r,IHws,Str_app_assoc. reflexivity. Qed.
End AffineRuns.

Module AffineMachine.
Record config := Cfg { left:AffineRuns.t; right:AffineRuns.t; state:Q; direction:dir }.
#[export] Instance config_eqb : Eqb config.
Proof.
  refine (Build_Eqb _ (fun c c' => eqb (left c,right c,state c,direction c)
    (left c',right c',state c',direction c')) _).
  intros [l r q d] [l' r' q' d']; cbn [left right state direction].
  destruct (eqb_spec (l,r,q,d) (l',r',q',d')); constructor; congruence.
Defined.
Definition denote rho c := match direction c with
  | L => AffineRuns.denote rho (left c) <{{state c}} AffineRuns.denote rho (right c)
  | R => AffineRuns.denote rho (left c) {{state c}}> AffineRuns.denote rho (right c) end.
Definition oriented (q:Q) d (s t:side) := match d with
  | L => s <{{q}} t | R => t {{q}}> s end.

Definition local tm q d back front :=
  match BoundedConfig.steps1 tm 500 (BoundedConfig.Build_T back front q d) with
  | Some (BoundedConfig.Build_T out [] q' d',true) => Some (out,q',d')
  | _ => None end.

Lemma local_spec tm q d back front out q' d' :
  local tm q d back front=Some(out,q',d') -> forall l r,
  BoundedConfig.to_config (BoundedConfig.Build_T back front q d) l r -[tm]->+
  BoundedConfig.to_config (BoundedConfig.Build_T out [] q' d') l r.
Proof.
  unfold local. pose proof (BoundedConfig.steps1_spec tm 500
    (BoundedConfig.Build_T back front q d)) as H.
  destruct (BoundedConfig.steps1 tm 500 (BoundedConfig.Build_T back front q d))
    as [[[u v a b] flag]|] eqn:E; try discriminate.
  destruct v,flag; try discriminate. intros G; inverts G. exact H.
Qed.

Definition block_step tm c : option config :=
  let '(Cfg l r q d):=c in
  match AffineRuns.pop (match d with L=>l | R=>r end) with
  | None => None
  | Some(w,s) => match local tm q d [] w with
    | None => None
    | Some(v,q',d') => Some (match d,d' with
      | L,L => Cfg s (AffineRuns.push v (Affine.const 1) r) q' L
      | L,R => Cfg (AffineRuns.push v (Affine.const 1) s) r q' R
      | R,L => Cfg l (AffineRuns.push v (Affine.const 1) s) q' L
      | R,R => Cfg (AffineRuns.push v (Affine.const 1) l) s q' R end) end end.

Lemma block_step_spec tm rho c c' : block_step tm c=Some c' ->
  denote rho c -[tm]->+ denote rho c'.
Proof.
  destruct c as [l r q []]; cbn [block_step].
  - destruct (AffineRuns.pop l) as [[w s]|] eqn:E; try discriminate.
    destruct (local tm q L [] w) as [[[v q'] d']|] eqn:F; try discriminate.
    destruct d'; intros G; inverts G; cbn [denote left right state direction];
      rewrite AffineRuns.push_spec,Affine.val_const;
      change (N.to_nat 1) with 1%nat; cbn [lpow]; rewrite app_nil_r;
      rewrite (AffineRuns.pop_spec rho _ _ _ E);
      exact (local_spec _ _ _ _ _ _ _ _ F (AffineRuns.denote rho s) (AffineRuns.denote rho r)).
  - destruct (AffineRuns.pop r) as [[w s]|] eqn:E; try discriminate.
    destruct (local tm q R [] w) as [[[v q'] d']|] eqn:F; try discriminate.
    destruct d'; intros G; inverts G; cbn [denote left right state direction];
      rewrite AffineRuns.push_spec,Affine.val_const;
      change (N.to_nat 1) with 1%nat; cbn [lpow]; rewrite app_nil_r;
      rewrite (AffineRuns.pop_spec rho _ _ _ E);
      exact (local_spec _ _ _ _ _ _ _ _ F (AffineRuns.denote rho l) (AffineRuns.denote rho s)).
Qed.

Definition scan_rule tm q d back front :=
  match local tm q d back front with
  | Some(out,q',d') => if eqb q q' then if eqb d d' then
      skip_prefix_list back out else None else None
  | None => None end.

Lemma scan_rule_spec tm q d back front v : scan_rule tm q d back front=Some v ->
  forall s t, oriented q d (front *> s) (back *> t) -[tm]->+
    oriented q d s (back *> v *> t).
Proof.
  unfold scan_rule. destruct (local tm q d back front) as [[[u q'] d']|] eqn:E;
    try discriminate. destruct (eqb_spec q q'),(eqb_spec d d'); try discriminate; subst q' d'.
  intros F. apply skip_prefix_list_spec in F. subst u. intros s t.
  destruct d; cbn [oriented]; rewrite <-Str_app_assoc.
  - exact (local_spec _ _ _ _ _ _ _ _ E s t).
  - exact (local_spec _ _ _ _ _ _ _ _ E t s).
Qed.

Lemma scan_many tm q d back front v n s t : scan_rule tm q d back front=Some v ->
  oriented q d (front^^n *> s) (back *> t) -[tm]->*
    oriented q d s (back *> v^^n *> t).
Proof.
  intros H. gen t. induction n; intros t; cbn [lpow]; [constructor|].
  rewrite !Str_app_assoc. eapply evstep_trans; [apply progress_evstep,scan_rule_spec,H|].
  specialize (IHn (v *> t)). rewrite <- (Str_app_assoc (v^^n) v t),lpow_shift,Str_app_assoc in IHn.
  exact IHn.
Qed.

Definition mk q d s t := match d with L=>Cfg s t q L | R=>Cfg t s q R end.
Lemma denote_mk rho q d s t : denote rho (mk q d s t)=
  oriented q d (AffineRuns.denote rho s) (AffineRuns.denote rho t).
Proof. destruct d; reflexivity. Qed.

Definition scan_stacks tm q d k keep s t : option config := match s with
  | [] => None
  | (w,n)::s => Affine.sub keep n &&& fun take =>
      if (1<?fst take)%N then
      AffineRuns.cut k t &&& fun '(ws,t') =>
      scan_rule tm q d (List.concat ws) w &&& fun v =>
      Some (mk q d (AffineRuns.push w (Affine.const keep) s)
        (AffineRuns.push_words ws (AffineRuns.push v take t')))
      else None end.

Lemma scan_stacks_spec tm rho q d k keep s t c' :
  scan_stacks tm q d k keep s t=Some c' ->
  denote rho (mk q d s t) -[tm]->* denote rho c'.
Proof.
  destruct s as [|[w n] s]; cbn [scan_stacks if_Some]; [discriminate|].
  destruct (Affine.sub keep n) as [take|] eqn:E; cbn [if_Some]; [|discriminate].
  destruct (1<?fst take)%N; [|discriminate].
  destruct (AffineRuns.cut k t) as [[ws t']|] eqn:F; cbn [if_Some]; [|discriminate].
  destruct (scan_rule tm q d (List.concat ws) w) as [v|] eqn:G;
    cbn [if_Some]; [|discriminate].
  intros H; inverts H. rewrite !denote_mk.
  rewrite AffineRuns.push_words_spec,!AffineRuns.push_spec,Affine.val_const.
  cbn [AffineRuns.denote]. rewrite (Affine.val_sub rho _ _ _ E),
    (AffineRuns.cut_spec rho _ _ _ _ F),Nat.add_comm,lpow_add,Str_app_assoc.
  apply scan_many,G.
Qed.

Definition near (s:AffineRuns.t) :=
  (fold_right (fun wn a => N.min 4 (fst (snd wn))+a)%N 0%N s <=? 3)%N.
Definition scan_step tm c :=
  let '(Cfg l r q d):=c in
  let s:=match d with L=>l | R=>r end in
  let t:=match d with L=>r | R=>l end in
  if near l then None else
  let keep:=match d with L=>if near (tl s) then 4%N else 0%N | R=>0%N end in
  match scan_stacks tm q d 0 keep s t with
  | Some c=>Some c | None=>match scan_stacks tm q d 1 keep s t with
    | Some c=>Some c | None=>scan_stacks tm q d 2 keep s t end end.

Lemma scan_step_spec tm rho c c' : scan_step tm c=Some c' ->
  denote rho c -[tm]->* denote rho c'.
Proof.
  destruct c as [l r q d]. unfold scan_step. destruct (near l); [discriminate|].
  destruct (scan_stacks tm q d 0 _ _ _) eqn:E.
  - intros H; inverts H. apply (scan_stacks_spec tm rho) in E. destruct d; exact E.
  - destruct (scan_stacks tm q d 1 _ _ _) eqn:F.
    + intros H; inverts H. apply (scan_stacks_spec tm rho) in F. destruct d; exact F.
    + intros H. apply (scan_stacks_spec tm rho) in H. destruct d; exact H.
Qed.
End AffineMachine.

Lemma repeat_grow tm (C:nat -> side -> Q*tape) w k
  (H:forall a r, C a (w *> w *> r) -[tm]->+ C (a+k) (w *> r)) n a r :
  C a (w^^(1+n) *> r) -[tm]->* C (a+n*k) (w *> r).
Proof.
  gen a. induction n; intros a.
  - cbn [lpow Nat.mul Nat.add]. rewrite app_nil_r,Nat.add_0_r. constructor.
  - change (C a ((w ++ w ++ w^^n) *> r) -[tm]->* C (a+(1+n)*k) (w *> r)).
    rewrite !Str_app_assoc. eapply evstep_trans; [apply progress_evstep,H|].
    rewrite <-Str_app_assoc. applys_eq (IHn (a+k)); flia.
Qed.

Module Sk1Rules.
Definition tm :=
  Eval compute in (TM_from_str "1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Definition X : list Sym := [1;0;1;1].
Definition Y : list Sym := [1;1;0;1].
Definition U : list Sym := [0;1;0;0].
Definition V : list Sym := [0;0;1;0].

Lemma growA a r :
  0inf <* <[0;0;0;1] <* (rev X)^^(1+a) <{{A}} U *> U *> r -->+
  0inf <* <[0;0;0;1] <* (rev X)^^(3+a) <{{A}} U *> r.
Proof. unfold X,U. es. Qed.

Lemma growB a r :
  0inf <* (rev Y)^^(1+a) <{{B}} [1;0;1;0] *> V *> V *> r -->+
  0inf <* (rev Y)^^(3+a) <{{B}} [1;0;1;0] *> V *> r.
Proof. unfold Y,V. es. Qed.

Lemma growC a r :
  0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(1+a) <* <[1;1;0;1] {{F}}>
    [1;0;0;0;1;0;0;0] *> r -->+
  0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(3+a) <* <[1;1;0;1] {{F}}>
    [1;0;0;0] *> r.
Proof. es. Qed.

Lemma growD a r :
  0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(1+a) <{{A}}
    [0;1;0;1;0;0;0;1;0;0;0;1] *> r -->+
  0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(3+a) <{{A}}
    [0;1;0;1;0;0;0;1] *> r.
Proof. es. Qed.

Lemma growAA a b r :
  0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(1+a) <* <[1;1;1;0]^^(1+b) <{{A}}
    [0;1;0;1;0;0;0;1;0;0;0;1] *> r -->+
  0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(5+a) <* <[1;1;1;0]^^(1+b) <{{A}}
    [0;1;0;1;0;0;0;1] *> r.
Proof. es. Qed.

Lemma growBB a b r :
  0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(1+a) <* <[1;1;0;1]^^(1+b) <{{B}}
    [1;0;1;0;0;0;1;0;0;0;1;0] *> r -->+
  0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(5+a) <* <[1;1;0;1]^^(1+b) <{{B}}
    [1;0;1;0;0;0;1;0] *> r.
Proof. es. Qed.

Lemma growCC a b r :
  0inf <* <[1;1;0;1]^^(1+a) <* <[1;1;1;1] <* <[0;1;1;1]^^(1+b)
    <* <[1;1;0;1] {{F}}> [1;0;0;0;1;0;0;0] *> r -->+
  0inf <* <[1;1;0;1]^^(5+a) <* <[1;1;1;1] <* <[0;1;1;1]^^(1+b)
    <* <[1;1;0;1] {{F}}> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma growDD a b r :
  0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(1+a) <* <[1;1;1;1]
    <* <[1;0;1;1]^^(1+b) <{{A}} [0;1;0;0;0;1;0;0] *> r -->+
  0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(5+a) <* <[1;1;1;1]
    <* <[1;0;1;1]^^(1+b) <{{A}} [0;1;0;0] *> r.
Proof. es. Qed.

(* A cut in the middle of the same two-counter cycle. Unlike growAA,
   this head returns before inspecting the next source word. *)
Lemma growAA_mid a b r :
  0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(1+a) <* <[1;1;1;0]^^(1+b)
    <* <[1;1;1;1] {{D}}> [0;1;0;0] *> r -->+
  0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(5+a) <* <[1;1;1;0]^^(1+b)
    <* <[1;1;1;1] {{D}}> r.
Proof. es. Qed.

Lemma growE a r :
  0inf <{{B}} [1;0;1;0] *> [1;0;0;0]^^(1+a) *> [1;0;0;1;0;0;0;0;1;0;0;0;1;0;0;0] *> r -->+
  0inf <{{B}} [1;0;1;0] *> [1;0;0;0]^^(5+a) *> [1;0;0;1;0;0;0;0;1;0;0;0] *> r.
Proof. es. Qed.

Inductive phase := PA | PB | PC | PD | PAA | PBB | PCC | PDD | PM | PE.
Definition source p : list Sym := match p with
  | PA | PDD | PM => [0;1;0;0] | PB | PBB => [0;0;1;0]
  | PC | PCC | PE => [1;0;0;0] | PD | PAA => [0;0;0;1] end.
Definition gain p := match p with PA | PB | PC | PD => 2 | _ => 4 end.
Definition stage p a b r := match p with
  | PA => 0inf <* <[0;0;0;1] <* (rev X)^^(1+a) <{{A}} r
  | PB => 0inf <* (rev Y)^^(1+a) <{{B}} [1;0;1;0] *> r
  | PC => 0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(1+a) <* <[1;1;0;1] {{F}}> r
  | PD => 0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(1+a) <{{A}} [0;1;0;1] *> r
  | PAA => 0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(1+a) <* <[1;1;1;0]^^(1+b)
      <{{A}} [0;1;0;1] *> r
  | PBB => 0inf <* <[0;0;1;1] <* <[0;1;1;1]^^(1+a) <* <[1;1;0;1]^^(1+b)
      <{{B}} [1;0;1;0] *> r
  | PCC => 0inf <* <[1;1;0;1]^^(1+a) <* <[1;1;1;1] <* <[0;1;1;1]^^(1+b)
      <* <[1;1;0;1] {{F}}> r
  | PDD => 0inf <* <[0;1;1;0] <* <[1;1;1;0]^^(1+a) <* <[1;1;1;1]
      <* <[1;0;1;1]^^(1+b) <{{A}} r
  | PM => 0inf <* <[0;0;0;1] <* <[1;0;1;1]^^(1+a) <* <[1;1;1;0]^^(1+b)
      <* <[1;1;1;1] {{D}}> r
  | PE => 0inf <{{B}} [1;0;1;0] *> [1;0;0;0]^^(1+a) *> [1;0;0;1;0;0;0;0] *> r end.

Lemma one p a b r : stage p a b (source p *> source p *> r) -->+
  stage p (a+gain p) b (source p *> r).
Proof.
  destruct p; cbn [stage source gain].
  - applys_eq (growA a r); flia.
  - applys_eq (growB a r); flia.
  - applys_eq (growC a r); flia.
  - applys_eq (growD a r); flia.
  - applys_eq (growAA a b r); flia.
  - applys_eq (growBB a b r); flia.
  - applys_eq (growCC a b r); flia.
  - applys_eq (growDD a b r); flia.
  - applys_eq (growAA_mid a b ([0;1;0;0] *> r)); flia.
  - applys_eq (growE a r); flia.
Qed.

Lemma batch p n a b r : stage p a b (source p^^(1+n) *> r) -->*
  stage p (a+n*gain p) b (source p *> r).
Proof. apply (repeat_grow tm (fun a r => stage p a b r)). intros. apply one. Qed.

Lemma batch_keep p n k a b r : stage p a b (source p^^(1+n+k) *> r) -->*
  stage p (a+n*gain p) b (source p^^(1+k) *> r).
Proof.
  rewrite (lpow_add _ (1+n) k),Str_app_assoc.
  pose proof (batch p n a b (source p^^k *> r)) as H.
  change (stage p a b (source p^^(1+n) *> source p^^k *> r) -->*
    stage p (a+n*gain p) b ((source p++source p^^k) *> r)).
  rewrite Str_app_assoc. exact H.
Qed.

Lemma batch_mid n a b r : stage PM a b (source PM^^n *> r) -->*
  stage PM (a+n*4) b r.
Proof.
  gen a. induction n; intros a.
  - cbn [lpow Nat.mul]. rewrite Nat.add_0_r. constructor.
  - cbn [lpow]. rewrite Str_app_assoc.
    eapply evstep_trans with (c':=stage PM (a+4) b (source PM^^n *> r)).
    + apply progress_evstep. unfold stage,source.
      applys_eq (growAA_mid a b ([0;1;0;0]^^n *> r)); flia.
    + applys_eq (IHn (a+4)); flia.
Qed.
End Sk1Rules.

Module Sk1Program.
Import AffineMachine Sk1Rules.
Definition lit (w:list Sym) : list Sym*Affine.t := (w,Affine.const 1).
Definition succ e := Affine.add (Affine.const 1) e.
Definition frame p a b s :=
  let x:=succ a in let y:=succ b in
  match p with
  | PA => Cfg [([1;1;0;1],x);lit [1;0;0;0]] s A L
  | PB => Cfg [([1;0;1;1],x)] (lit [1;0;1;0]::s) B L
  | PC => Cfg [lit [1;0;1;1];([1;1;1;0],x);lit [1;1;0;0]] s F R
  | PD => Cfg [([0;1;1;1],x);lit [0;1;1;0]] (lit [0;1;0;1]::s) A L
  | PAA => Cfg [([0;1;1;1],y);([1;1;0;1],x);lit [1;0;0;0]]
      (lit [0;1;0;1]::s) A L
  | PBB => Cfg [([1;0;1;1],y);([1;1;1;0],x);lit [1;1;0;0]]
      (lit [1;0;1;0]::s) B L
  | PCC => Cfg [lit [1;0;1;1];([1;1;1;0],y);lit [1;1;1;1];([1;0;1;1],x)] s F R
  | PDD => Cfg [([1;1;0;1],y);lit [1;1;1;1];([0;1;1;1],x);lit [0;1;1;0]] s A L
  | PM => Cfg [lit [1;1;1;1];([0;1;1;1],y);([1;1;0;1],x);lit [1;0;0;0]] s D R
  | PE => Cfg [] (lit [1;0;1;0]::([1;0;0;0],x)::lit [1;0;0;1]::lit [0;0;0;0]::s) B L end.

Lemma frame_spec rho p a b s : denote rho (frame p a b s)=
  stage p (Affine.val rho a) (Affine.val rho b) (AffineRuns.denote rho s).
Proof.
  destruct p; cbn [frame denote left right state direction AffineRuns.denote lit];
    unfold succ; rewrite ?Affine.val_add,?Affine.val_const;
    cbn [stage X Y rev lpow app]; rewrite ?Str_app_assoc; reflexivity.
Qed.

Section Padding.
Variable padding:nat.
Definition keep p : N := match p with PM=>0 | _=>N.of_nat (1+padding) end.
Definition before p a b n s := frame p a b ((source p,Affine.add (Affine.const (keep p)) n)::s).
Definition after p a b n s :=
  frame p (Affine.add a (Affine.scale (N.of_nat (gain p)) n)) b
    (match p with PM=>s | _=>(source p,Affine.const (N.of_nat (1+padding)))::s end).

Lemma effect rho p a b n s : denote rho (before p a b n s) -[tm]->*
  denote rho (after p a b n s).
Proof.
  unfold before,after. rewrite !frame_spec,Affine.val_add,Affine.val_scale,Nat2N.id.
  destruct p; cbn [keep gain AffineRuns.denote];
    rewrite Affine.val_add,?Affine.val_const,?Nat2N.id.
  all: try solve [match goal with |- stage ?p _ _ _ -->* _ =>
    applys_eq (batch_keep p (Affine.val rho n) padding (Affine.val rho a)
      (Affine.val rho b) (AffineRuns.denote rho s)); cbn [gain]; flia end].
  cbn [N.to_nat Nat.add].
  applys_eq (batch_mid (Affine.val rho n) (Affine.val rho a) (Affine.val rho b)
    (AffineRuns.denote rho s)); flia.
Qed.

Definition count_at (i:nat) (s:AffineRuns.t) := snd (nth i s ([],Affine.const 0)).
Definition ai p : nat := match p with PA|PB|PD=>0 | PC|PAA|PBB|PE=>1 | PDD|PM=>2 | PCC=>3 end.
Definition bi p : option nat := match p with PAA|PBB|PDD=>Some 0%nat | PCC|PM=>Some 1%nat | _=>None end.
Definition ctx p : nat := match p with PB|PD|PAA|PBB=>1 | PE=>4 | _=>0 end.
Definition macro_for p c :=
  Affine.sub 1 (count_at (ai p) (match p with PE=>right c | _=>left c end)) &&& fun a =>
  (match bi p with None=>Some (Affine.const 0) | Some i=>Affine.sub 1 (count_at i (left c)) end)
    &&& fun b =>
  let r:=skipn (ctx p) (right c) in
  Affine.sub (keep p) (count_at 0 r) &&& fun n =>
  if (match p with PM=>true | _=>(0<?fst n)%N end) then
    if eqb c (before p a b n (tl r)) then Some (after p a b n (tl r)) else None
  else None.

Lemma macro_for_spec rho p c c' : macro_for p c=Some c' ->
  denote rho c -[tm]->* denote rho c'.
Proof.
  unfold macro_for. destruct (Affine.sub 1 _) as [a|]; cbn [if_Some]; [|discriminate].
  destruct (match bi p with None=>Some (Affine.const 0) | Some i=>Affine.sub 1 (count_at i (left c)) end)
    as [b|]; cbn [if_Some]; [|discriminate].
  destruct (Affine.sub (keep p) _) as [n|]; cbn [if_Some]; [|discriminate].
  destruct (match p with PM=>true | _=>(0<?fst n)%N end); [|discriminate].
  destruct (eqb_spec c (before p a b n (tl (skipn (ctx p) (right c))))) as [E|E];
    [|discriminate].
  intros H; inverts H. rewrite E at 1. apply effect.
Qed.

Fixpoint macros ps c := match ps with
  | []=>None | p::ps=>match macro_for p c with Some c'=>Some c' | None=>macros ps c end end.
Lemma macros_spec rho ps c c' : macros ps c=Some c' -> denote rho c -[tm]->* denote rho c'.
Proof. induction ps; cbn [macros]; [discriminate|].
  destruct (macro_for a c) eqn:E; [intros H; inverts H; apply macro_for_spec with a; exact E|exact IHps]. Qed.

Definition step c := match macros [PM;PE;PA;PB;PC;PD;PAA;PBB;PCC;PDD] c with
  | Some c'=>Some c' | None=>match scan_step tm c with
    | Some c'=>Some c' | None=>block_step tm c end end.
Lemma step_spec rho c c' : step c=Some c' -> denote rho c -[tm]->* denote rho c'.
Proof. unfold step. destruct (macros _ c) eqn:E.
  - intros H; inverts H. eapply macros_spec; exact E.
  - destruct (scan_step tm c) eqn:F.
    + intros H; inverts H. eapply scan_step_spec; exact F.
    + intros H. apply progress_evstep. eapply block_step_spec; exact H.
Qed.

Definition run fuel c target :=
  N_iter_until (fun c=>if eqb c target then inr true else
    match step c with Some c'=>inl c' | None=>inr false end) (inl c) fuel.
Definition check fuel c target := match run fuel c target with inr true=>true | _=>false end.
Lemma run_spec rho fuel c target : match run fuel c target with
  | inl x=>denote rho c -[tm]->* denote rho x
  | inr b=>b=true -> denote rho c -[tm]->* denote rho target end.
Proof.
  unfold run. apply (N_iter_until_spec
    (fun x=>denote rho c -[tm]->* denote rho x)
    (fun b=>b=true -> denote rho c -[tm]->* denote rho target)).
  - intros x H. destruct (eqb_spec x target); subst; [auto|].
    destruct (step x) eqn:E; [eapply evstep_trans; [exact H|eapply step_spec; exact E]|discriminate].
  - constructor.
Qed.
Lemma check_spec rho fuel c target : check fuel c target=true ->
  denote rho c -[tm]->* denote rho target.
Proof. unfold check. pose proof (run_spec rho fuel c target) as H.
  destruct (run fuel c target) as [x|[]]; auto; discriminate. Qed.

Definition check_positive fuel c target := block_step tm c &&& fun c' =>
  Some (check fuel c' target).
Lemma check_positive_spec rho fuel c target : check_positive fuel c target=Some true ->
  denote rho c -[tm]->+ denote rho target.
Proof.
  unfold check_positive. destruct (block_step tm c) eqn:E; cbn [if_Some]; [|discriminate].
  intros H. injection H as H. eapply progress_evstep_trans;
    [eapply block_step_spec; exact E|eapply check_spec; exact H].
Qed.

End Padding.
Definition P n := Cfg [([1;1;1;0],Affine.const 2);lit [1;1;0;0]]
  [lit [1;0;1;0];([0;0;1;0],n);lit [0;0;0;0];([0;0;1;0],Affine.const 28);
   lit [0;0;0;0];lit [1;0;0;0];lit [0;1;0;0]] B L.
Definition Nport n := Cfg [([1;1;0;1],n);lit [1;0;0;0]]
  [([0;0;0;1],Affine.const 28);lit [0;0;1;1];lit [0;0;0;0];lit [1;0;0;0]] A L.
Definition D x b a := Cfg [([1;1;1;0],a);lit [1;1;1;1];([1;0;1;1],b);
  ([1;1;1;0],x);lit [1;1;1;1];([1;0;1;1],Affine.const 17)] [] C R.
Definition p_start := P (1000%N,[1%N]).
Definition p_end := P (296838023%N,[262144%N]).
Definition d_start := D (1000%N,[1%N]) (130%N,[0%N;0%N;1%N]) (30%N,[0%N;1%N]).
Definition d_end := D (1398055900%N,[1048576%N]) (10%N,[0%N;0%N;1%N]) (6%N,[0%N;1%N]).
Definition exit_start := D (349479900%N,[1048576%N]) (130%N,[0%N;1%N]) (Affine.const 13).
Definition exit_end := P (2862942115659%N,[8589934592%N;4%N]).
Definition n_start := Nport (1000%N,[1%N]).
Definition n_end := Nport (295003022%N,[262144%N]).
End Sk1Program.

Module Sk1Shared.
Import AffineMachine Sk1Program.
Open Scope N_scope.
Lemma checked_P : check_positive 31 700000 p_start p_end=Some true.
Proof. native_check_eq. Qed.
Lemma checked_N : check_positive 31 700000 n_start n_end=Some true.
Proof. native_check_eq. Qed.
Lemma checked_D : check_positive 31 700000 d_start d_end=Some true.
Proof. native_check_eq. Qed.
Lemma checked_exit : check_positive 31 700000 exit_start exit_end=Some true.
Proof. native_check_eq. Qed.
Definition initial_A := Cfg [] [] A R.
Definition initial_D := Cfg [] [] BB62.D R.
Definition initial_D_target := D (Affine.const 70691118354036414594808423388)
  (Affine.const 10456559309013950571) (Affine.const 939468133961604901).
Lemma checked_init_A : check 31 1500000 initial_A (Nport (Affine.const 508932094))=true.
Proof. native_check_eq. Qed.

Import AffineMachine Sk1Program Sk1Rules.
Open Scope N_scope.

Definition pc n := denote [] (P (Affine.const n)).
Definition nc n := denote [] (Nport (Affine.const n)).
Definition dc x b a := denote [] (D (Affine.const x) (Affine.const b) (Affine.const a)).
Lemma P_eval rho e : denote rho (P e)=pc (Affine.value rho e).
Proof. unfold pc,P,denote. cbn [left right state direction AffineRuns.denote lit].
  rewrite !Affine.val_const. reflexivity. Qed.
Lemma N_eval rho e : denote rho (Nport e)=nc (Affine.value rho e).
Proof. unfold nc,Nport,denote. cbn [left right state direction AffineRuns.denote lit].
  rewrite !Affine.val_const. reflexivity. Qed.
Lemma D_eval rho x b a : denote rho (D x b a)=dc (Affine.value rho x) (Affine.value rho b) (Affine.value rho a).
Proof. unfold dc,D,denote. cbn [left right state direction AffineRuns.denote lit].
  rewrite !Affine.val_const. reflexivity. Qed.
Lemma N_const_eval rho n : denote rho (Nport (Affine.const n))=nc n.
Proof. rewrite N_eval. unfold Affine.value,Affine.const; cbn [fst snd Affine.dot].
  rewrite N.add_0_r. reflexivity. Qed.
Lemma D_const_eval rho x b a : denote rho (D (Affine.const x) (Affine.const b) (Affine.const a))=dc x b a.
Proof. rewrite D_eval. unfold Affine.value,Affine.const; cbn [fst snd Affine.dot].
  rewrite !N.add_0_r. reflexivity. Qed.
Local Opaque pc nc dc.

Lemma P_cycle n : pc (1000+n) -->+ pc (296838023+262144*n).
Proof.
  pose proof (check_positive_spec 31 [n] _ _ _ checked_P) as H.
  unfold p_start,p_end in H. rewrite !P_eval in H.
  unfold Affine.value in H. cbn [Affine.dot fst snd] in H.
  rewrite ?N.add_0_r,?N.mul_1_l in H. exact H.
Qed.
Lemma N_cycle n : nc (1000+n) -->+ nc (295003022+262144*n).
Proof.
  pose proof (check_positive_spec 31 [n] _ _ _ checked_N) as H.
  unfold n_start,n_end in H. rewrite !N_eval in H.
  unfold Affine.value in H. cbn [Affine.dot fst snd] in H.
  rewrite ?N.add_0_r,?N.mul_1_l in H. exact H.
Qed.
Lemma D_cycle x b a : dc (1000+x) (130+b) (30+a) -->+
  dc (1398055900+1048576*x) (10+b) (6+a).
Proof.
  pose proof (check_positive_spec 31 [x;a;b] _ _ _ checked_D) as H.
  unfold d_start,d_end in H. rewrite !D_eval in H.
  unfold Affine.value in H. cbn [Affine.dot fst snd] in H.
  rewrite ?N.add_0_r,?N.mul_1_l,?N.mul_0_l,?N.add_0_l in H. exact H.
Qed.
Lemma D_exit z y : dc (349479900+1048576*z) (130+y) 13 -->+
  pc (2862942115659+8589934592*z+4*y).
Proof.
  pose proof (check_positive_spec 31 [z;y] _ _ _ checked_exit) as H.
  unfold exit_start,exit_end in H. rewrite !D_eval,!P_eval in H.
  unfold Affine.value in H. cbn [Affine.const Affine.dot fst snd] in H.
  rewrite ?N.add_0_r,?N.mul_1_l,?N.mul_0_l,?N.add_0_l in H.
  applys_eq H; flia.
Qed.

Lemma P_nonhalt n : ~halts tm (pc (1000+n)).
Proof.
  apply (progress_nonhalt_simple tm N (fun n=>pc(1000+n)) n).
  intros k. exists (296837023+262144*k).
  applys_eq (P_cycle k); flia.
Qed.
Lemma N_nonhalt n : ~halts tm (nc (1000+n)).
Proof.
  apply (progress_nonhalt_simple tm N (fun n=>nc(1000+n)) n).
  intros k. exists (295002022+262144*k).
  applys_eq (N_cycle k); flia.
Qed.

Lemma D_many k : forall x b, 1000<=x -> 130<=b ->
  exists z, dc x (b+120*N.succ k) (13+24*N.succ k) -->*
    dc (349479900+1048576*z) b 13.
Proof.
  induction k using N.peano_ind; intros x b Hx Hb.
  - exists x. apply progress_evstep.
    applys_eq (D_cycle (x-1000) (b-10) 7); flia.
  - destruct (IHk (349479900+1048576*x) b) as [z Hz]; try lia.
    exists z. eapply evstep_trans with
      (c':=dc (349479900+1048576*x) (b+120*N.succ k) (13+24*N.succ k)); [|exact Hz].
    apply progress_evstep.
    applys_eq (D_cycle (x-1000) (b+120*N.succ k-10) (7+24*N.succ k)); flia.
Qed.

Lemma blank_A_nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact (check_spec 31 [] _ _ _ checked_init_A)|].
  rewrite N_const_eval. exact (N_nonhalt 508931094).
Qed.

Definition shortcut c :=
  let x:=fst (count_at 3 (left c)) in
  let b:=fst (count_at 2 (left c)) in
  let a:=fst (count_at 0 (left c)) in
  if (1000<=?x) then if (130<=?b) then if (30<=?a) then
  if Eqb.eqb c (D (Affine.const x) (Affine.const b) (Affine.const a)) then
    Some (D (Affine.const (349479900+1048576*x)) (Affine.const (b-120)) (Affine.const (a-24)))
  else None else None else None else None.
Lemma some_inj {T} (x y:T) : Some x=Some y -> x=y.
Proof. congruence. Qed.
Lemma shortcut_spec rho c c' : shortcut c=Some c' -> denote rho c -->* denote rho c'.
Proof.
  unfold shortcut. set (x:=fst (count_at 3 (left c))).
  set (b:=fst (count_at 2 (left c))). set (a:=fst (count_at 0 (left c))).
  clearbody x b a.
  destruct (N.leb_spec 1000 x),(N.leb_spec 130 b),(N.leb_spec 30 a); try discriminate.
  destruct (Eqb.eqb_spec c (D (Affine.const x) (Affine.const b) (Affine.const a))) as [E|E];
    [|discriminate].
  intros G. apply some_inj in G. subst c'. rewrite E at 1. rewrite !D_eval.
  unfold Affine.value,Affine.const; cbn [fst snd Affine.dot]. rewrite !N.add_0_r.
  apply progress_evstep. applys_eq (D_cycle (x-1000) (b-130) (a-30)); flia.
Qed.
Definition init_step c := match shortcut c with Some c'=>Some c' | None=>step 0 c end.
Lemma init_step_spec rho c c' : init_step c=Some c' -> denote rho c -->* denote rho c'.
Proof. unfold init_step. destruct (shortcut c) eqn:E.
  - intros H; inverts H. eapply shortcut_spec; exact E.
  - apply step_spec. Qed.
Definition init_tick c := if Eqb.eqb c initial_D_target then inr true else
  match init_step c with Some c'=>inl c' | None=>inr false end.
Definition init_run := N_iter_until init_tick (inl initial_D) 8000000.
Definition init_check := match init_run with inr true=>true | _=>false end.
Lemma init_run_spec : match init_run with
  | inl x=>denote [] initial_D -->* denote [] x
  | inr b=>b=true -> denote [] initial_D -->* denote [] initial_D_target end.
Proof.
  unfold init_run. apply (N_iter_until_spec
    (fun x=>denote [] initial_D -->* denote [] x)
    (fun b=>b=true -> denote [] initial_D -->* denote [] initial_D_target)).
  - intros x H. unfold init_tick. destruct (Eqb.eqb_spec x initial_D_target); subst; [auto|].
    destruct (init_step x) eqn:E; [eapply evstep_trans; [exact H|eapply init_step_spec; exact E]|discriminate].
  - constructor.
Qed.
Lemma init_check_spec : init_check=true -> denote [] initial_D -->* denote [] initial_D_target.
Proof. unfold init_check. pose proof init_run_spec as H.
  destruct init_run as [x|[]]; auto; discriminate. Qed.
Lemma checked_init_D : init_check=true.
Proof. native_check_eq. Qed.

Lemma blank_D_nonhalt : ~halts tm (denote [] initial_D).
Proof.
  eapply multistep_nonhalt; [exact (init_check_spec checked_init_D)|].
  unfold initial_D_target. rewrite D_const_eval.
  pose proof (D_many 39144505581733536 70691118354036414594808423388 5759218639205926131
    ltac:(apply N.leb_le; reflexivity) ltac:(apply N.leb_le; reflexivity)) as Hmany.
  destruct Hmany as [z Hz].
  eapply multistep_nonhalt; [exact Hz|].
  eapply multistep_nonhalt; [apply progress_evstep; exact (D_exit z 5759218639205926001)|].
  applys_eq (P_nonhalt (2862942114659+8589934592*z+4*5759218639205926001)); flia.
Qed.
End Sk1Shared.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD").
Theorem nonhalt: ~halts tm c0.
Proof. exact Sk1Shared.blank_A_nonhalt. Qed.
End TM25.

Module TM26.
(* Use the mirror, so both machines have the same counter orientation. *)
Definition tm := Eval compute in (TM_from_str "1LB0LC_1RC1LC_1RD0LB_1RA0RE_1RF---_1RC1LA").
Definition rename (q:Q) := match q with
  | A=>BB62.D | B=>A | C=>B | BB62.D=>C | E=>E | F=>F end.
Lemma same_rules : Perm tm Sk1Rules.tm rename.
Proof.
  split.
  - intros [] []; cbn; discriminate || reflexivity.
  - intros [] [] s d q H; cbn in H; inverts H; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  apply (perm_nonhalt tm Sk1Rules.tm rename A _ same_rules).
  exact Sk1Shared.blank_D_nonhalt.
Qed.
End TM26.

From BusyCoq Require Import Eqv_WordPairs.

Module TM23.
Import AffineMachine Sk1Program.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC0LE_1RD1RF_1LE0LB_1RF1LB_0RA---").
Definition initial_E := Cfg [] [] E R.

Lemma checked_init_E : check 31 700000 initial_E (Nport (Affine.const 72180622))=true.
Proof. native_check_eq. Qed.

Lemma blank_E_nonhalt : ~halts Sk1Rules.tm (denote [] initial_E).
Proof.
  eapply multistep_nonhalt; [exact (check_spec 31 [] _ _ _ checked_init_E)|].
  exact (Sk1Shared.N_nonhalt 72179622).
Qed.

(* The already-proved TM24/TM23 equivalence reduces TM23 to the shared table
   starting in E. Only the state map, not a relabelled machine code, is used. *)
Definition rename (q:Q) := match q with
  | A=>E | B=>F | C=>B | BB62.D=>C | E=>BB62.D | F=>A end.
Lemma same_rules : Perm Eqv_WordPairs.TM79.tm Sk1Rules.tm rename.
Proof.
  split.
  - intros [] []; cbn; discriminate || reflexivity.
  - intros [] [] s d q H; cbn in H; inverts H; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  change (~halts Eqv_WordPairs.TM79.tm' c0).
  rewrite <-Eqv_WordPairs.TM79.eqv.
  apply (perm_nonhalt _ Sk1Rules.tm rename A _ same_rules).
  exact blank_E_nonhalt.
Qed.
End TM23.
