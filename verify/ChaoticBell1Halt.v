(* Chaotic bell class 1: certified RLE execution for TM7 and TM13.
   Only repeat counts can be huge; the evaluator never expands them.
   Finite matching budgets cause fallback to the original machine, not halt. *)
From BusyCoq Require Import Individual62 Longitudinal ES_v2 ES_v3 Helper Eqb FastRev.
Require Import List NArith ZifyNat Lia.
Open Scope sym_scope.
Local Notation "x && y" := (if x then y else false) : bool_scope.
Local Notation "x || y" := (if x then true else y) : bool_scope.
Open Scope bool_scope.

Module Runs.
Lemma nil_power {A} n : (@nil A)^^n = [].
Proof. induction n; cbn; assumption || reflexivity. Qed.
Definition t := list (list Sym*N).
Fixpoint denote (xs:t) : side := match xs with
  | [] => 0inf
  | (w,n)::xs => w^^N.to_nat n *> denote xs
  end.

Definition push (w:list Sym) (n:N) (xs:t) : t :=
  match w,n with
  | [],_ | _,N0 => xs
  | _,_ => match xs with
    | (v,m)::ys => if eqb w v then (w,(n+m)%N)::ys else (w,n)::xs
    | [] => [(w,n)] end
  end.

Lemma push_spec w n xs : denote (push w n xs) = w^^N.to_nat n *> denote xs.
Proof.
  destruct w as [|b w].
  - cbn [push]. rewrite nil_power. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    destruct xs as [|[v m] xs]; cbn [push denote]; [reflexivity|].
    destruct (eqb_spec (b::w) v); subst; cbn [denote]; [|reflexivity].
    rewrite N2Nat.inj_add,lpow_add,Str_app_assoc. reflexivity.
Qed.

Fixpoint pop (xs:t) : Sym*t := match xs with
  | [] => (0,[])
  | ([],_)::xs | (_,N0)::xs => pop xs
  | ((b::w),Npos n)::xs =>
    (b,push w 1 (push (b::w) (N.pred (Npos n)) xs))
  end.

Lemma pop_spec xs : denote xs = fst (pop xs) >> denote (snd (pop xs)).
Proof.
  induction xs as [|[[|b w] [|n]] xs IH]; cbn [pop denote].
  - apply const_unfold.
  - exact IH.
  - rewrite nil_power. exact IH.
  - exact IH.
  - cbn [fst snd]. rewrite !push_spec. change (N.to_nat 1) with 1%nat. cbn [lpow app Str_app].
    replace (N.to_nat (Npos n)) with (1+N.to_nat (N.pred (Npos n))) by lia.
    cbn [Nat.add lpow app Str_app]. rewrite app_nil_r,Str_app_assoc. reflexivity.
Qed.

Fixpoint remove (w:list Sym) (xs:t) : option t := match w with
  | [] => Some xs
  | b::w => let '(c,ys) := pop xs in
    if eqb b c then remove w ys else None
  end.

Lemma remove_spec w xs ys : remove w xs=Some ys -> denote xs=w *> denote ys.
Proof.
  gen xs. induction w; intros xs H; cbn [remove] in H.
  - inverts H. reflexivity.
  - pose proof (pop_spec xs) as E. destruct (pop xs) as [b zs]; cbn in E.
    destruct (eqb_spec a b); try discriminate. subst.
    rewrite E,(IHw _ H). reflexivity.
Qed.

Lemma commute_power (x v w:list Sym) a b k :
  x++v^^a=w^^b++x -> x++v^^(k*a)=w^^(k*b)++x.
Proof.
  intros H. induction k.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [Nat.mul]. rewrite !lpow_add,app_assoc,H,<-app_assoc,IHk,app_assoc.
    reflexivity.
Qed.

(* Check one short periodic identity, then move an arbitrary number of
   groups. This also handles rotated and differently sized RLE words. *)
Definition skip_block w limit x v m ys : option (N*t) :=
  let a := N.of_nat (length w) in let b := N.of_nat (length v) in
  let k := N.min (limit/b) (m/a) in
  if (0<?k)%N then
  if (k*b<=?limit)%N then if (k*a<=?m)%N then
  if eqb (x++v^^length w) (w^^length v++x) then
    Some ((k*b)%N,push x 1 (push v (m-k*a) ys))
  else None else None else None else None.

Lemma skip_block_spec w limit x v m ys n zs :
  skip_block w limit x v m ys=Some (n,zs) ->
  (n<=limit)%N /\ x *> v^^N.to_nat m *> denote ys = w^^N.to_nat n *> denote zs.
Proof.
  unfold skip_block.
  generalize (N.min (limit/N.of_nat (length v)) (m/N.of_nat (length w))) as k.
  intros k H. destruct (N.ltb_spec 0 k); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (length v)) limit); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (length w)) m); try discriminate.
  destruct (eqb_spec (x++v^^length w) (w^^length v++x)); inverts H.
  split; [assumption|]. rewrite !push_spec.
  change (N.to_nat 1) with 1%nat. cbn [lpow]. rewrite app_nil_r.
  rewrite N2Nat.inj_mul,Nat2N.id.
  replace (N.to_nat m) with
    (N.to_nat k*length w+N.to_nat (m-k*N.of_nat (length w))) by lia.
  rewrite lpow_add,!Str_app_assoc.
  rewrite <-Str_app_assoc,(commute_power x v w _ _ _ e),!Str_app_assoc.
  reflexivity.
Qed.

Definition skip_periodic w n xs := match xs with
  | (x,Npos xH)::(v,m)::ys => skip_block w n x v m ys
  | (v,m)::ys => skip_block w n [] v m ys
  | [] => None end.

Lemma skip_periodic_spec w n xs k ys : skip_periodic w n xs=Some (k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  unfold skip_periodic. destruct xs as [|[x [|[p|p|]]] xs]; try discriminate;
    try (apply skip_block_spec).
  destruct xs as [|[v m] xs]; [apply skip_block_spec|].
  cbn [denote]. change (N.to_nat 1) with 1%nat.
  cbn [lpow]. rewrite app_nil_r. apply skip_block_spec.
Qed.

(* The common aligned case needs no division or periodic-word comparison. *)
Definition skip w n xs := match xs with
  | (v,m)::ys=>if eqb w v then
      let k:=N.min n m in Some(k,push v (m-k) ys)
    else skip_periodic w n xs
  | []=>None end.
Lemma skip_spec w n xs k ys : skip w n xs=Some(k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  destruct xs as [|[v m] xs]; cbn [skip]; [discriminate|].
  destruct(eqb_spec w v); subst; [|apply skip_periodic_spec].
  intros H; inverts H. split; [apply N.le_min_l|].
  cbn [denote]. rewrite push_spec,<-Str_app_assoc,<-lpow_add.
  f_equal; f_equal; lia.
Qed.

Fixpoint remove_fast fuel w n xs : option t :=
  if (n=?0)%N then Some xs else match fuel with
  | O => None
  | S fuel => match skip w n xs with
    | Some (k,ys) => remove_fast fuel w (n-k)%N ys
    | None => match remove w xs with
      | Some ys => remove_fast fuel w (N.pred n) ys
      | None => None end
    end
  end.

Lemma remove_fast_spec fuel w n xs ys : remove_fast fuel w n xs=Some ys ->
  denote xs=w^^N.to_nat n *> denote ys.
Proof.
  gen n xs ys. induction fuel; intros n xs ys H; cbn [remove_fast] in H;
    destruct (N.eqb_spec n 0); try discriminate; subst; try solve [inverts H; reflexivity].
  destruct (skip w n xs) as [[k zs]|] eqn:E.
  - destruct (skip_spec _ _ _ _ _ E) as [Hk E1].
    rewrite E1,(IHfuel _ _ _ H),<-Str_app_assoc,<-lpow_add.
    f_equal; f_equal; lia.
  - destruct (remove w xs) as [zs|] eqn:E1; try discriminate.
    rewrite (remove_spec _ _ _ E1),(IHfuel _ _ _ H).
    replace (N.to_nat n) with (1+N.to_nat (N.pred n)) by lia.
    cbn [Nat.add lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Fixpoint size (xs:t) : N := match xs with
  | []=>0%N | (w,n)::xs=>(N.of_nat (length w)*n+size xs)%N end.

End Runs.

Module RunMachine.
Record config := Cfg { left : Runs.t; right : Runs.t; state : Q; direction : dir }.
Definition denote c := match direction c with
  | L => Runs.denote (left c) <{{state c}} Runs.denote (right c)
  | R => Runs.denote (left c) {{state c}}> Runs.denote (right c)
  end.

Definition raw tm c : option config :=
  let '(b,l,r) := match direction c with
    | L => let '(b,l) := Runs.pop (left c) in (b,l,right c)
    | R => let '(b,r) := Runs.pop (right c) in (b,left c,r)
    end in
  match tm (state c,b) with
  | None => None
  | Some (b',L,q) => Some (Cfg l (Runs.push [b'] 1 r) q L)
  | Some (b',R,q) => Some (Cfg (Runs.push [b'] 1 l) r q R)
  end.

Lemma raw_spec tm c : match raw tm c with
  | None => halted tm (denote c)
  | Some c' => denote c -[tm]-> denote c'
  end.
Proof.
  destruct c as [l r q []]; unfold raw; cbn [left right state direction denote].
  - pose proof (Runs.pop_spec l) as H. destruct (Runs.pop l) as [b l']; cbn in H.
    rewrite H. destruct (tm (q,b)) as [[[b' []] q']|] eqn:E;
      cbn [denote left right state direction]; try rewrite Runs.push_spec;
      cbn [N.to_nat Pos.to_nat lpow app Str_app];
      first [solve [unfold halted; cbn; exact E] | solve [econstructor; exact E]].
  - pose proof (Runs.pop_spec r) as H. destruct (Runs.pop r) as [b r']; cbn in H.
    rewrite H. destruct (tm (q,b)) as [[[b' []] q']|] eqn:E;
      cbn [denote left right state direction]; try rewrite Runs.push_spec;
      cbn [N.to_nat Pos.to_nat lpow app Str_app];
      first [solve [unfold halted; cbn; exact E] | solve [econstructor; exact E]].
Qed.
End RunMachine.

Module CB1.
Definition D n : list Sym := [1] ++ [1;1]^^n ++ [0;0].
Definition S n : list Sym := [1] ++ [0;1]^^(1+n).
(* The right-going head includes the following 0100, not a left payload. *)
Definition R (l r:side) := l {{A}}> [0;1;0;0] *> r.
Definition L (l r:side) := l <{{B}} [1] *> r.
Definition J (l r:side) := l <{{C}} [1;0;0] *> r.

(* Near-to-far representation of the left P block; its parameter is two
   less than the P subscript in CHAOTIC_BELL_CLASS1_RULES.txt. *)
Definition PL n := <[0;1]^^(n+4) ++ [1;1]^^n ++ S 0 ++ S 0.
Fixpoint tape (v:list nat) (r:side) := match v with
  | [] => r | n::v => D n *> tape v r end.
Fixpoint back (v:list nat) (l:side) := match v with
  | [] => l | n::v => back v (l <* S n) end.
Lemma tape_app u v r : tape (u++v) r = tape u (tape v r).
Proof. induction u; cbn [tape app]; congruence. Qed.
Lemma tape_repeat n k r : tape (repeat n k) r = (D n)^^k *> r.
Proof. induction k; cbn [repeat tape lpow]; [reflexivity|].
  rewrite Str_app_assoc,IHk. reflexivity. Qed.

Record Core (tm:TM) : Prop := {
  moveR : forall l r n, R l (D n *> r) -[tm]->* R (l <* S n) r;
  moveL : forall l r n, L (l <* S n) r -[tm]->* L l (D n *> r);
  emptyR : forall l, R l 0inf -[tm]->* L l (D 0 *> D 0 *> 0inf);
  restartL : forall l r b, L (l <* <[1;1;1] <* <[0;1]^^(1+b)) r -[tm]->*
    R (l <* <[0;1]^^(1+b)) r;
  moveJ : forall l r n, J (l <* S n) r -[tm]->* L l (D (1+n) *> r);
  restartJ : forall l r b, J (l <* <[1;1;1] <* <[0;1]^^b) r -[tm]->*
    R (l <* <[0;1]^^(1+b)) r;
  finishPL : forall l r b, L (l <* S 0 <* <[1;0] <* <[0;1]^^(1+b)) r -[tm]->*
    J l (D (1+b) *> r);
  collide : forall l r, R l ([1;0] *> D 0 *> D 0 *> r) -[tm]->*
    J l (D 2 *> [1;0] *> r);
  pairR : forall l r n, R l ([1;0] *> D (2+n) *> D (2+n) *> r) -[tm]->*
    R (l <* PL n) ([1;0] *> r)
}.

(* Each premise certifies an entire finite right call, including its return.
   No coinductive assumption about an unknown right-hand suffix is used. *)
Definition call tm r s := forall l, R l r -[tm]->* L l s.
Inductive calls tm : nat -> side -> side -> Prop :=
| calls_O r : calls tm 0 r r
| calls_S n r s t : call tm r s -> calls tm n s t -> calls tm (1+n) r t.

Section Higher.
Variable tm : TM.
Variable rules : Core tm.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Lemma right_list l r v : R l (tape v r) -->* R (back v l) r.
Proof. gen l. induction v; intros; cbn [tape back]; [apply evstep_refl|].
  follow (moveR _ rules). apply IHv. Qed.
Lemma left_list l r v : L (back v l) r -->* L l (tape v r).
Proof. gen l r. induction v; intros; cbn [tape back]; [apply evstep_refl|].
  follow IHv. apply (moveL _ rules). Qed.
Lemma call_prefix v r s : call tm r s -> call tm (tape v r) (tape v s).
Proof. intros H l. follow right_list. follow H. apply left_list. Qed.
Lemma call_blank v : call tm (tape v 0inf) (tape v (D 0 *> D 0 *> 0inf)).
Proof. apply call_prefix. exact (emptyR _ rules). Qed.

Lemma calls_blank k v : calls tm k (tape v 0inf) (tape v ((D 0)^^(k*2) *> 0inf)).
Proof.
  gen v. induction k; intros v; [constructor|].
  eapply calls_S; [apply call_blank|].
  specialize (IHk (v++[0%nat;0%nat])).
  rewrite !tape_app in IHk. cbn [tape] in IHk.
  cbn [Nat.mul Nat.add lpow]. rewrite !Str_app_assoc.
  exact IHk.
Qed.

Lemma call_collision v j r : call tm (tape v (D j *> [1;0] *> D 0 *> D 0 *> r))
  (tape v (D (1+j) *> D 2 *> [1;0] *> r)).
Proof.
  apply call_prefix. intros l. follow (moveR _ rules).
  follow (collide _ rules). apply (moveJ _ rules).
Qed.

Lemma calls_collision k v j r : calls tm (1+k)
  (tape v (D j *> [1;0] *> (D 0)^^((1+k)*2) *> r))
  (tape v (D (1+j) *> (D 3)^^k *> D 2 *> [1;0] *> r)).
Proof.
  gen v j. induction k; intros v j; cbn [Nat.mul Nat.add lpow]; rewrite !Str_app_assoc.
  - eapply calls_S; [apply call_collision|constructor].
  - eapply calls_S; [apply call_collision|].
    specialize (IHk (v++[1+j]) 2).
    rewrite !tape_app in IHk. cbn [tape Nat.add] in IHk.
    exact IHk.
Qed.

Lemma pairsR k n l r : R l ([1;0] *> (D (2+n))^^(k*2) *> r) -->*
  R (l <* (PL n)^^k) ([1;0] *> r).
Proof.
  gen l. induction k; intros l; [apply evstep_refl|].
  cbn [Nat.mul Nat.add lpow]. rewrite !Str_app_assoc.
  follow (pairR _ rules). follow IHk. rewrite lpow_shift'. apply evstep_refl.
Qed.

Lemma loopL k r s : calls tm k r s -> forall l b,
  L (l <* <[1;1;1]^^k <* <[0;1]^^(1+b)) r -->*
  L (l <* <[0;1]^^(1+b)) s.
Proof.
  intros H. induction H; intros l b; [apply evstep_refl|].
  cbn [Nat.add lpow]. rewrite !Str_app_assoc.
  follow (restartL _ rules). follow H. apply IHcalls.
Qed.

Lemma loopR k r s : calls tm k r s -> forall l b,
  R (l <* <[1;1;1]^^k <* <[0;1]^^(1+b)) r -->*
  R (l <* <[0;1]^^(1+b)) s.
Proof.
  intros H. induction H; intros l b; [apply evstep_refl|].
  cbn [Nat.add lpow]. rewrite !Str_app_assoc.
  follow H. follow (restartL _ rules). apply IHcalls.
Qed.

(* These are one-block rules parameterized by a proved stream of calls.
   In particular the L output is J, never L. *)
Lemma returnP_L n r s : calls tm (1+n*2) r s -> forall l,
  L (l <* PL (1+n*3)) r -->* J l (D (5+n*3) *> s).
Proof.
  intros H l.
  replace (l <* PL (1+n*3)) with
    (l <* S 0 <* <[1;0] <* <[1;1;1]^^(1+n*2) <* <[0;1]^^(5+n*3)).
  2:{ unfold PL,S. st. simpl_rotate. f_equal; flia. }
  follow (loopL _ _ _ H).
  apply (finishPL _ rules).
Qed.

Lemma loopJ k r s : calls tm (1+k) r s -> forall l b,
  J (l <* <[1;1;1]^^(1+k) <* <[0;1]^^b) r -->*
  L (l <* <[0;1]^^(1+b)) s.
Proof.
  intros H l b. inversion H as [|m r0 u t Hcall Htail]; subst.
  cbn [Nat.add lpow]. rewrite !Str_app_assoc.
  follow (restartJ _ rules). follow Hcall. apply loopL; assumption.
Qed.
Lemma returnP_J n r s : calls tm (1+n*2) r s -> forall l,
  J (l <* PL (1+n*3)) r -->* J l (D (6+n*3) *> s).
Proof.
  intros H l.
  replace (l <* PL (1+n*3)) with
    (l <* S 0 <* <[1;0] <* <[1;1;1]^^(1+n*2) <* <[0;1]^^(5+n*3)).
  2:{ unfold PL,S. st. simpl_rotate. f_equal; flia. }
  follow (loopJ _ _ _ H). apply (finishPL _ rules).
Qed.

Lemma calls_prefix v k r s : calls tm k r s -> calls tm k (tape v r) (tape v s).
Proof. intros H. induction H; [constructor|].
  eapply calls_S; [apply call_prefix,H|assumption]. Qed.
Lemma calls_split a b r s : calls tm (a+b) r s ->
  exists t, calls tm a r t /\ calls tm b t s.
Proof.
  gen r. induction a; intros r H; [exists r; split; [constructor|exact H]|].
  inversion H as [|m r0 t s0 Hcall Htail]; subst.
  destruct (IHa _ Htail) as [u [Hu Hv]].
  exists u. split; [econstructor; eauto|exact Hv].
Qed.

Lemma returnsP_J k n r s : calls tm (k*(1+n*2)) r s -> forall l,
  J (l <* (PL (1+n*3))^^k) r -->* J l ((D (6+n*3))^^k *> s).
Proof.
  gen r s. induction k; intros r s H l.
  - inversion H; subst. apply evstep_refl.
  - destruct (calls_split _ _ _ _ H) as [u [Hu Hv]].
    cbn [lpow]. rewrite !Str_app_assoc.
    follow (returnP_J _ _ _ Hu).
    pose proof (calls_prefix [6+n*3] _ _ _ Hv) as Hrest.
    cbn [tape] in Hrest. follow (IHk _ _ Hrest).
    rewrite lpow_shift'. apply evstep_refl.
Qed.
Lemma returnsP_L k n r s : calls tm ((1+k)*(1+n*2)) r s -> forall l,
  L (l <* (PL (1+n*3))^^(1+k)) r -->*
  J l ((D (6+n*3))^^k *> D (5+n*3) *> s).
Proof.
  intros H l. destruct (calls_split _ _ _ _ H) as [u [Hu Hv]].
  cbn [Nat.add lpow]. rewrite !Str_app_assoc.
  follow (returnP_L _ _ _ Hu).
  apply returnsP_J. apply (calls_prefix [5+n*3] _ _ _ Hv).
Qed.
End Higher.
End CB1.


Module CBExec.
Module RT := Runs.
Module RM := RunMachine.
Import RM.
Local Opaque RT.remove_fast RT.remove RT.push.

Definition orient d c := match d,direction c with
  | L,R => let '(b,r) := RT.pop (right c) in
      Cfg (RT.push [b] 1 (left c)) r (state c) L
  | R,L => let '(b,l) := RT.pop (left c) in
      Cfg l (RT.push [b] 1 (right c)) (state c) R
  | _,_ => c end.
Lemma orient_spec d c : denote (orient d c)=denote c.
Proof.
  destruct c as [l r q []],d; unfold orient; cbn [left right state direction]; try reflexivity.
  - pose proof (RT.pop_spec l) as H. destruct (RT.pop l) as [b l']; cbn in H.
    cbn [denote left right state direction]. rewrite RT.push_spec,H. reflexivity.
  - pose proof (RT.pop_spec r) as H. destruct (RT.pop r) as [b r']; cbn in H.
    cbn [denote left right state direction]. rewrite RT.push_spec,H. reflexivity.
Qed.
Lemma orient_direction d c : direction (orient d c)=d.
Proof. destruct c as [l r q []],d; cbn [orient direction left right state]; try reflexivity;
  first [solve [destruct (RT.pop l); reflexivity] | solve [destruct (RT.pop r); reflexivity]]. Qed.
Lemma orient_state d c : state (orient d c)=state c.
Proof. destruct c as [l r q []],d; cbn [orient direction left right state]; try reflexivity;
  first [solve [destruct (RT.pop l); reflexivity] | solve [destruct (RT.pop r); reflexivity]]. Qed.

Fixpoint zeros (xs:RT.t) := match xs with
  | [] => true
  | (w,_)::xs => if forallb (fun b=>eqb b 0) w then zeros xs else false end.
Lemma zero_word w : forallb (fun b=>eqb b 0) w=true -> w *> 0inf=0inf.
Proof.
  induction w as [|b w IH]; cbn; intros H; [reflexivity|].
  destruct b; cbn in H; try discriminate. rewrite IH by exact H. symmetry; apply const_unfold.
Qed.
Lemma zeros_spec xs : zeros xs=true -> RT.denote xs=0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn [zeros RT.denote]; intros H; [reflexivity|].
  destruct (forallb (fun b=>eqb b 0) w) eqn:E; try discriminate.
  rewrite IH by exact H. apply lpow_all0,zero_word,E.
Qed.

(* Patterns and storage use the same RLE format. No repeat count is expanded
   by the evaluator. plug, in contrast, is only a logical interpretation. *)
Fixpoint plug (xs:RT.t) (r:side) := match xs with
  | [] => r | (w,n)::xs => w^^N.to_nat n *> plug xs r end.
Fixpoint put (xs ys:RT.t) := match xs with
  | [] => ys | (w,n)::xs => RT.push w n (put xs ys) end.
Fixpoint take (xs ys:RT.t) := match xs with
  | [] => Some ys
  | (w,n)::xs => match RT.remove_fast 512 w n ys with
    | Some ys => take xs ys | None => None end end.
Lemma put_spec xs ys : RT.denote (put xs ys)=plug xs (RT.denote ys).
Proof. induction xs as [|[w n] xs IH]; cbn [put plug]; [reflexivity|].
  rewrite RT.push_spec,IH. reflexivity. Qed.
Lemma take_spec xs ys zs : take xs ys=Some zs -> RT.denote ys=plug xs (RT.denote zs).
Proof. gen ys. induction xs as [|[w n] xs IH]; intros ys H; cbn [take plug] in *.
  - inverts H; reflexivity.
  - destruct (RT.remove_fast 512 w n ys) as [ts|] eqn:E; try discriminate.
    rewrite (RT.remove_fast_spec _ _ _ _ _ E),(IH _ H). reflexivity. Qed.
Lemma plug_app xs ys r : plug (xs++ys) r=plug xs (plug ys r).
Proof. induction xs as [|[w n] xs IH]; cbn [app plug]; congruence. Qed.

Inductive mode := MR | ML | MJ | MA | MB | MC.
Definition mq h := match h with MR|MA=>A | ML|MB=>B | MJ|MC=>C end.
Definition md h := match h with MR|MA=>R | _=>L end.
Definition payload h : list Sym := match h with
  | MR=>[0;1;0;0] | ML=>[1] | MJ=>[1;0;0] | _=>[] end.
Definition hat h (l r:side) := match h with
  | MR=>CB1.R l r | ML=>CB1.L l r | MJ=>CB1.J l r
  | MA=>l {{A}}> r | MB=>l <{{B}} r | MC=>l <{{C}} r end.
Definition rp h (r:RT.t) := (payload h,1%N)::r.
Record recipe := Rule {
  hi : mode; li : RT.t; ri : RT.t;
  ho : mode; lo : RT.t; ro : RT.t;
  zl : bool; zr : bool }.
Definition valid tm p := forall l r,
  (zl p=true -> l=0inf) -> (zr p=true -> r=0inf) ->
  hat (hi p) (plug (li p) l) (plug (ri p) r) -[tm]->*
  hat (ho p) (plug (lo p) l) (plug (ro p) r).
Definition use p c : option config :=
  if eqb (state c) (mq (hi p)) then
  let c:=orient (md (hi p)) c in
  match take (li p) (left c),take (rp (hi p) (ri p)) (right c) with
  | Some l,Some r =>
    if (if zl p then zeros l else true) then
    if (if zr p then zeros r else true) then
      Some (Cfg (put (lo p) l) (put (rp (ho p) (ro p)) r) (mq (ho p)) (md (ho p)))
    else None else None
  | _,_=>None end else None.

Lemma use_spec tm p c c' : valid tm p -> use p c=Some c' ->
  denote c -[tm]->* denote c'.
Proof.
  intros H. unfold use. destruct (eqb_spec (state c) (mq (hi p))); try discriminate.
  pose proof (orient_direction (md (hi p)) c) as Hd.
  pose proof (orient_state (md (hi p)) c) as Hq.
  rewrite <-(orient_spec (md (hi p)) c).
  remember (orient (md (hi p)) c) as z.
  destruct z as [ls rs q d]; cbn [left right state direction] in *; subst.
  destruct (take (li p) ls) as [l|] eqn:El; try discriminate.
  destruct (take (rp (hi p) (ri p)) rs) as [r|] eqn:Er; try discriminate.
  destruct (if zl p then zeros l else true) eqn:Zl; try discriminate.
  destruct (if zr p then zeros r else true) eqn:Zr; intros E; inverts E.
  assert (Hl: zl p=true -> RT.denote l=0inf).
  { intros E; rewrite E in Zl; apply zeros_spec,Zl. }
  assert (Hr: zr p=true -> RT.denote r=0inf).
  { intros E; rewrite E in Zr; apply zeros_spec,Zr. }
  specialize (H _ _ Hl Hr).
  rewrite e. destruct (hi p), (ho p);
    cbn [denote md mq left right state direction];
    rewrite ?RT.push_spec,!put_spec,(take_spec _ _ _ El),(take_spec _ _ _ Er); exact H.
Qed.

End CBExec.

Import CBExec.
Module CBMacros.
Definition word (w:list Sym) : RT.t := [(w,1%N)].
Definition power (w:list Sym) n : RT.t := [(w,N.of_nat n)].
Definition dn n := word (CB1.D n).
Definition sn n := word (CB1.S n).
Definition imm := word [1;0].
Definition rule h l r h' l' r' := Rule h l r h' l' r' false false.
Definition leftzero h l r h' l' r' := Rule h l r h' l' r' true false.
Lemma plug_word w r : plug (word w) r=w *> r.
Proof. change ((w++[]) *> r=w *> r). rewrite app_nil_r. reflexivity. Qed.
Lemma plug_power w n r : plug (power w n) r=w^^n *> r.
Proof. cbn [plug power]. rewrite Nat2N.id. reflexivity. Qed.
Lemma plug_run w n r : plug [(w,n)] r=w^^N.to_nat n *> r.
Proof. reflexivity. Qed.

Inductive basic :=
| ScanR (k:N) | ScanB (k:N) | ScanC (k:N) | ScanPair (k:N) | Ones (k:N)
| Blank | Even (n:nat) | Restart (b:nat) | Over2 (b:nat) | Over1 (b n:nat)
| Collision | LeftJ (n:nat) | TurnB (n:nat) | TurnJ (b:nat)
| Defect0 (m:nat) | Defect1 (m:nat) | Defect2 (n m:nat)
| DefectBlank0 | DefectBlankS (n:nat) | Paired (k:N) (n:nat).

Definition basic_rule t := match t with
| ScanR k => rule MA [] (word [0;1]++[([1;1],k)])
    MA [([1;0],k)] (word [0;1])
| ScanB k => rule MB [([0;1],k)] [] MB [] [([1;1],k)]
| ScanC k => rule MC [([1;0],k)] [] MC [] [([1;1],k)]
| ScanPair k => rule MA [] (word [0;1]++[([0;1;0;1],k)])
    MA [([1;1;0;1],k)] (word [0;1])
| Ones k => rule MA [] [([1],k)] MA [([1],k)] []
| Blank => rule MR [] (word [0;0;0]) ML [] (dn 0++dn 0)
| Even n => rule MR [] (power [1;1] (1+n)++word [0;0]) ML [] (dn (1+n)++imm)
| Restart b => rule ML (power [1;0] (1+b)++word [1;1;1]) []
    MR (power [1;0] (1+b)) []
| Over2 b => leftzero ML (power [1;0] (1+b)++word [1;1]) []
    MR (power [1;0] 2++power [1;1] (1+b)) (word [1])
| Over1 b n => leftzero ML (power [1;0] (1+b)++word [1]) (dn n)
    MR (power [1;0] (n+2)++power [1;1] b) imm
| Collision => rule ML (word [0;0;1;1;0;1]) [] MJ [] (word [1;1;1;1])
| LeftJ n => rule MJ (sn n) [] ML [] (dn (1+n))
| TurnB n => rule ML (word [1;1]) (dn n) MR (power [1;0] (1+n)) []
| TurnJ b => rule MJ (power [1;0] b++word [1;1;1]) []
    MR (power [1;0] (1+b)) []
| Defect0 m => rule MR [] (imm++dn 0++word [1]++power [1;1] m++word [0])
    MJ [] (word [1;1;1;1]++dn m++word [1])
| Defect1 m => rule MR [] (imm++dn 1++word [1]++power [1;1] m++word [0])
    ML [] (dn 0++dn 0++dn (1+m)++word [1])
| Defect2 n m => rule MR [] (imm++dn (2+n)++word [1]++power [1;1] m++word [0])
    MR (power [1;0] (2+m)++power [1;1] n++sn 0++sn 0) (word [1])
| DefectBlank0 => rule MR [] (imm++dn 0++word [0;0])
    MR (word [1;0;0;1]++sn 0) []
| DefectBlankS n => rule MR [] (imm++dn (1+n)++word [0;0])
    MR (word [1;0]++power [1;1] n++word [1]++sn 0++sn 0) []
| Paired k n => rule MR [] ([([1;0],(k*2)%N)]++dn n)
    MR (power [1;0] n++[([1;1;0;1],k)]++sn 0) []
end.

Ltac basic_start :=
  intros t; destruct t; unfold valid,basic_rule,rule,leftzero;
  cbn [hi li ri ho lo ro zl zr]; intros l r Hl Hr;
  try (specialize (Hl eq_refl); subst l);
  unfold dn,sn,imm;
  rewrite ?plug_app,?plug_word,?plug_power,?plug_run,?N2Nat.inj_mul;
  change (N.to_nat 2) with 2%nat in *;
  cbn [hat plug].

Definition digits := list (nat*N).
Definition ds (v:digits) : RT.t := map (fun '(n,k)=>(CB1.D n,k)) v.
Definition ss (v:digits) : RT.t := fast_rev (map (fun '(n,k)=>(CB1.S n,k)) v).
Fixpoint expand (v:digits) : list nat := match v with
  | []=>[] | (n,k)::v=>repeat n (N.to_nat k)++expand v end.
Lemma ds_spec v r : plug (ds v) r=CB1.tape (expand v) r.
Proof. induction v as [|[n k] v IH]; cbn [ds map plug expand] in *; [reflexivity|].
  rewrite CB1.tape_app,CB1.tape_repeat. f_equal. exact IH. Qed.
Lemma back_app u v l : CB1.back (u++v) l=CB1.back v (CB1.back u l).
Proof. gen l. induction u; intros; cbn [app CB1.back]; auto. Qed.
Lemma back_repeat n k l : CB1.back (repeat n k) l=l <* (CB1.S n)^^k.
Proof. gen l. induction k; intros; cbn [repeat CB1.back lpow]; [reflexivity|].
  rewrite IHk,Str_app_assoc,lpow_shift'. reflexivity. Qed.
Lemma ss_spec v l : plug (ss v) l=CB1.back (expand v) l.
Proof.
  unfold ss; rewrite fast_rev_spec. gen l.
  induction v as [|[n k] v IH]; intros; cbn [map rev expand]; [reflexivity|].
  rewrite plug_app,IH,back_app,back_repeat. reflexivity.
Qed.

Inductive tail := TBlank (v:digits) | TCollision (v:digits) (j:nat).
Definition tail_zero t := match t with TBlank _=>true | _=>false end.
Definition before (h:N) t := match t with
  | TBlank v=>ds v
  | TCollision v j=>ds v++dn j++imm++[(CB1.D 0,(h*2)%N)] end.
Definition after (h:N) t := match t with
  | TBlank v=>ds v++[(CB1.D 0,(h*2)%N)]
  | TCollision v j=>ds v++dn (1+j)++[(CB1.D 3,(h-1)%N)]++dn 2++imm end.

Section Higher.
Variable tm : TM.
Variable core : CB1.Core tm.
Lemma tail_spec h t r : (0<h)%N -> (tail_zero t=true -> r=0inf) ->
  CB1.calls tm (N.to_nat h) (plug (before h t) r) (plug (after h t) r).
Proof.
  intros H Hr. destruct t as [v|v j]; cbn [before after tail_zero] in *.
  - specialize (Hr eq_refl); subst r. rewrite plug_app,!ds_spec,plug_run,N2Nat.inj_mul.
    apply CB1.calls_blank,core.
  - unfold dn,imm. rewrite !plug_app,!plug_word,!plug_run,!ds_spec,N2Nat.inj_mul.
    change (N.to_nat 2) with 2%nat.
    replace (N.to_nat h) with (1+N.to_nat (h-1)) by lia.
    apply CB1.calls_collision,core.
Qed.

Inductive high :=
| RightList (v:digits) | LeftList (v:digits) | CallBlank (v:digits)
| Pairs (n:nat) (k:N)
| Loops (fromR:bool) (k:N) (b:nat) (t:tail)
| Returns (fromJ:bool) (n:nat) (k:N) (t:tail).
Definition high_rule x := match x with
| RightList v => rule MR [] (ds v) MR (ss v) []
| LeftList v => rule ML (ss v) [] ML [] (ds v)
| CallBlank v => Rule MR [] (ds v) ML [] (ds v++[(CB1.D 0,2%N)]) false true
| Pairs n k => rule MR [] (imm++[(CB1.D (2+n),(k*2)%N)])
    MR [(CB1.PL n,k)] imm
| Loops fromR k b t =>
    let h := (1+k)%N in let head:=if fromR then MR else ML in
    Rule head (power [1;0] (1+b)++[([1;1;1],h)]) (before h t)
      head (power [1;0] (1+b)) (after h t) false (tail_zero t)
| Returns fromJ n k t =>
    let count:=(1+k)%N in let h:=(count*N.of_nat (1+n*2))%N in
    Rule (if fromJ then MJ else ML) [(CB1.PL (1+n*3),count)] (before h t)
      MJ [] ((if fromJ then [(CB1.D (6+n*3),count)]
        else [(CB1.D (6+n*3),k)]++dn (5+n*3))++after h t)
      false (tail_zero t)
end.

Lemma high_spec x : valid tm (high_rule x).
Proof.
  destruct x; unfold valid,high_rule,rule; cbn [hi li ri ho lo ro zl zr]; intros l r Hl Hr.
  - cbn [hat plug]. rewrite ds_spec,ss_spec. apply CB1.right_list,core.
  - cbn [hat plug]. rewrite ds_spec,ss_spec. apply CB1.left_list,core.
  - specialize (Hr eq_refl); subst r.
    rewrite plug_app,!ds_spec,plug_run. cbn [hat plug].
    exact (CB1.call_blank tm core (expand v) l).
  - unfold imm. rewrite plug_app,!plug_run,!plug_word,N2Nat.inj_mul.
    cbn [hat plug]. apply CB1.pairsR,core.
  - rewrite plug_app,plug_power,plug_run,plug_power.
    pose proof (tail_spec (1+k)%N t r ltac:(lia) Hr) as H.
    destruct fromR; cbn [hat];
      first [apply CB1.loopR | apply CB1.loopL]; assumption.
  - rewrite plug_app,plug_run.
    pose proof (tail_spec ((1+k)*N.of_nat (1+n*2))%N t r ltac:(lia) Hr) as H.
    rewrite N2Nat.inj_mul,Nat2N.id in H.
    destruct fromJ; cbn [hat]; rewrite ?plug_app,?plug_run.
    + apply CB1.returnsP_J; assumption.
    + unfold dn. rewrite plug_word.
      rewrite N2Nat.inj_add in H |- *. change (N.to_nat 1) with 1%nat in *.
      apply CB1.returnsP_L; assumption.
Qed.
End Higher.
End CBMacros.

Import CBExec CBMacros RunMachine.
Module CBSim.
Notation "'let?' x ':=' y 'in' z" :=
  (match y with Some x => z | None => None end)
  (at level 200, x pattern, y at level 100, z at level 200).
Definition otherwise {T} (x:option T) (y:unit->option T) :=
  match x with Some x=>Some x | None=>y tt end.
Definition instruction := (basic+high)%type.
Definition bi b : option instruction := Some (inl b).
Definition hi b : option instruction := Some (inr b).
Definition recipe_of x := match x with inl b=>basic_rule b | inr h=>high_rule h end.

(* Heuristics propose parameters only; [use] checks the complete rule instance.
   Budgets may undercount or miss a macro, but never certify a false step. *)
Fixpoint copies fuel w xs : N*RT.t := match fuel with
  | O => (0%N,xs)
  | S f => match RT.skip w (N.shiftl 1 80) xs with
    | Some (k,ys) => if (0<?k)%N then
        let '(m,zs):=copies f w ys in ((k+m)%N,zs) else (0%N,xs)
    | None => match RT.remove w xs with
      | Some ys=>let '(m,zs):=copies f w ys in ((1+m)%N,zs)
      | None=>(0%N,xs) end end end.
Definition scan := copies 512.
Definition small n := if (n<=?512)%N then Some (N.to_nat n) else None.
Definition word_digit (leftward:bool) (w:list Sym) :=
  let len:=length w in let n:=Nat.div (len-3) 2 in
  if Nat.leb 3 len then if Nat.leb len 1027 then
    if eqb w (if leftward then CB1.S n else CB1.D n) then Some n else None
  else None else None.
Definition readD xs :=
  let '(a,ys):=scan [1] xs in
  if N.odd a then let? zs:=RT.remove [0;0] ys in
    let? n:=small ((a-1)/2)%N in Some (n,zs) else None.
Definition readS xs :=
  let? ys:=RT.remove [1] xs in
  let '(k,zs):=scan [0;1] ys in
  if (0<?k)%N then let? n:=small (k-1)%N in Some(n,zs) else None.
Definition read_run leftward xs :=
  otherwise (match xs with
    | (w,k)::ys=>let? n:=word_digit leftward w in Some(n,k,ys)
    | []=>None end)
    (fun _=>let? (n,_):=(if leftward then readS xs else readD xs) in
      let '(k,ys):=scan (if leftward then CB1.S n else CB1.D n) xs in Some(n,k,ys)).
Fixpoint normal fuel (leftward:bool) xs acc : digits*RT.t := match fuel with
  | O=>(fast_rev acc,xs)
  | S f=>match read_run leftward xs with
    | None=>(fast_rev acc,xs)
    | Some(n,k,ys)=>
      if (0<?k)%N then normal f leftward ys ((n,k)::acc) else (fast_rev acc,xs)
    end end.
Definition normalR xs := normal 512 false xs [].
Definition normalL xs := let '(v,r):=normal 512 true xs [] in (fast_rev v,r).
Definition shape xs :=
  let '(b,ys):=scan [1;0] xs in let '(a,zs):=scan [1] ys in
  let z:=zeros zs in
  if z then if (a=?0)%N then if (0<?b)%N then (1%N,(b-1)%N,true)
    else (a,b,z) else (a,b,z) else (a,b,z).
Fixpoint last_digit (v:digits) : option(digits*nat) := match v with
  | []=>None
  | [(n,k)]=>if (0<?k)%N then Some ([(n,(k-1)%N)],n) else None
  | x::v=>let? (v,n):=last_digit v in Some(x::v,n) end.
Definition collision_tail v rs :=
  let? (v,j):=last_digit v in let? rs:=RT.remove [1;0] rs in
  let '(z,_):=scan (CB1.D 0) rs in Some (TCollision v j,z).

Definition returnP c :=
  let fromJ:=eqb (state c) C in
  if fromJ || eqb (state c) B then
  match left c with
  | (w,k)::ls=>
    let len:=length w in let n:=Nat.div (len-18) 12 in
    if eqb w (CB1.PL (1+n*3)) then if (0<?k)%N then
      let? rs:=RT.remove (if fromJ then [1;0;0] else [1]) (right c) in
      let '(v,rs):=normalR rs in
      if zeros rs then hi (Returns fromJ n (k-1)%N (TBlank v)) else
      let? (t,z):=collision_tail v rs in
      let k:=N.min k (z/(N.of_nat (1+n*2)*2))%N in
      if (0<?k)%N then hi (Returns fromJ n (k-1)%N t) else None
    else None else None
  | _=>None end else None.

Definition paired rs :=
  let '(k,ys):=scan [1;0] rs in
  if (2<=?k)%N then if negb (N.odd k) then
    let? (n,_):=readD ys in bi (Paired (k/2)%N n)
  else None else None.
Definition defect rs :=
  let? ys:=RT.remove [1;0] rs in let? (n,zs):=readD ys in
  let '(k,_):=scan (CB1.D n) ys in
  if ((2<=?N.of_nat n)%N && (2<=?k)%N) then hi (Pairs (n-2) (k/2)%N)
  else let '(a,ts):=scan [1] zs in
    if N.odd a then let? _:=RT.remove [0] ts in let? m:=small ((a-1)/2)%N in
      bi (match n with O=>Defect0 m | S O=>Defect1 m | S(S n)=>Defect2 n m end)
    else let? _:=RT.remove [0;0] zs in
      bi (match n with O=>DefectBlank0 | S n=>DefectBlankS n end).
Definition right_payload c rs :=
  let '(v,ts):=normalR rs in
  let '(a,b,_):=shape (left c) in
  if zeros ts then
    if ((3<=?a)%N && (0<?b)%N) then
      let? b:=small (b-1)%N in hi (Loops true (a/3-1)%N b (TBlank v))
    else hi (CallBlank v)
  else match v with
  | _::_ =>
    otherwise
      (if ((3<=?a)%N && (0<?b)%N) then
         let? (t,z):=collision_tail v ts in let k:=N.min (a/3)%N (z/2)%N in
         if (0<?k)%N then let? b:=small (b-1)%N in hi (Loops true (k-1)%N b t)
         else None
       else None)
      (fun _=>hi (RightList v))
  | [] => otherwise (paired rs) (fun _=>otherwise (defect rs) (fun _=>
    let '(a,ys):=scan [1] rs in
    if ((2<=?a)%N && negb (N.odd a)) then
      let? _:=RT.remove [0;0] ys in let? n:=small (a/2-1)%N in bi (Even n)
    else None)) end.
Definition right_plain c :=
  otherwise
    (let? rs:=RT.remove [0;1] (right c) in
     let '(a,_):=scan [1] rs in
     if (2<=?a)%N then bi (ScanR (a/2)%N) else
     let '(k,_):=scan [0;1;0;1] rs in if (0<?k)%N then bi (ScanPair k) else None)
    (fun _=>let '(k,_):=scan [1] (right c) in if (0<?k)%N then bi (Ones k) else None).
Definition left_payload c rs :=
  otherwise (let? _:=RT.remove [0;0;1;1;0;1] (left c) in bi Collision) (fun _=>
    let '(a,b,z):=shape (left c) in
    otherwise
      (if ((3<=?a)%N && (0<?b)%N) then let? b:=small (b-1)%N in bi (Restart b)
       else if z then if (0<?b)%N then let? b:=small (b-1)%N in
         if (a=?2)%N then bi (Over2 b) else if (a=?1)%N then
           let? (n,_):=readD rs in bi (Over1 b n) else None
       else None else None)
      (fun _=>otherwise
        (let? _:=RT.remove [1;1] (left c) in let? (n,_):=readD rs in bi (TurnB n))
        (fun _=>let '(v,_):=normalL (left c) in
          match v with []=>None | _=>hi (LeftList v) end))).

Definition choose c := otherwise (returnP c) (fun _=>match state c with
  | A=>otherwise (let? rs:=RT.remove [0;1;0;0] (right c) in right_payload c rs)
       (fun _=>right_plain c)
  | B=>otherwise (let? rs:=RT.remove [1] (right c) in left_payload c rs)
       (fun _=>let '(k,_):=scan [0;1] (left c) in if (0<?k)%N then bi (ScanB k) else None)
  | C=>otherwise
       (let? _:=RT.remove [1;0;0] (right c) in let '(a,b,_):=shape (left c) in
        if (3<=?a)%N then let? b:=small b in bi (TurnJ b) else None)
       (fun _=>let '(k,_):=scan [1;0] (left c) in if (0<?k)%N then bi (ScanC k) else None)
  | _=>None end).
Definition align c := match state c with A=>orient R c | B|C=>orient L c | _=>c end.
Definition tick tm c : config+unit :=
  let c:=align c in
  match (let? i:=choose c in use (recipe_of i) c) with
  | Some c'=>inl c'
  | None=>match raw tm c with Some c'=>inl c' | None=>inr tt end end.
Definition initial := Cfg [] [] A R.
Definition run tm fuel := N_iter_until (tick tm) (inl initial) fuel.
Definition check tm fuel := match run tm fuel with inr _=>true | _=>false end.

Lemma align_spec c : denote (align c)=denote c.
Proof. unfold align. destruct (state c); apply orient_spec || reflexivity. Qed.
Local Opaque choose use raw.
Section Sound.
Variable tm : TM.
Hypothesis certified : forall i, valid tm (recipe_of i).
Lemma tick_spec c : match tick tm c with
  | inl c'=>denote c -[tm]->* denote c'
  | inr _=>halts tm (denote c) end.
Proof.
  unfold tick. rewrite <-(align_spec c).
  generalize (align c). intros d.
  destruct (choose d) as [i|] eqn:E; cbn.
  - destruct (use (recipe_of i) d) as [c'|] eqn:F.
    + apply (use_spec _ _ _ _ (certified i) F).
    + pose proof (raw_spec tm d) as H. destruct (raw tm d).
      * apply evstep_one,H.
      * apply halted_halts,H.
  - pose proof (raw_spec tm d) as H. destruct (raw tm d).
    + apply evstep_one,H.
    + apply halted_halts,H.
Qed.
Lemma check_spec fuel : check tm fuel=true -> halts tm c0.
Proof.
  pose proof (@N_iter_until_spec config unit (tick tm) (inl initial) fuel
    (fun c=>c0 -[tm]->* denote c) (fun _=>halts tm c0)) as H.
  assert (Step:forall c,c0 -[tm]->* denote c -> match tick tm c with
    | inl d=>c0 -[tm]->* denote d | inr _=>halts tm c0 end).
  { intros c E. pose proof (tick_spec c) as Hc. destruct (tick tm c).
    - eapply evstep_trans; eauto.
    - eapply halts_evstep; eauto. }
  specialize (H Step (evstep_refl _ _)).
  unfold check,run. destruct (N_iter_until (tick tm) (inl initial) fuel);
    [discriminate|intros _; exact H].
Qed.
End Sound.

End CBSim.

Require Import String.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB1LF_1RC---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma scanR l r n :
  l {{A}}> [0;1] *> [1;1]^^n *> r -->*
  l <* <[0;1]^^n {{A}}> [0;1] *> r.
Proof. gen l. induction n; intros l; [finish|]. simpl_tape.
  do 6 step. follow IHn. simpl_rotate. finish. Qed.
Lemma scanB l r n :
  l <* <[1;0]^^n <{{B}} r -->* l <{{B}} [1;1]^^n *> r.
Proof. shift_rule; steps. Qed.
Lemma scanC l r n :
  l <* <[0;1]^^n <{{C}} r -->* l <{{C}} [1;1]^^n *> r.
Proof. shift_rule; steps. Qed.

Lemma scanPair l r n :
  l {{A}}> [0;1] *> [0;1;0;1]^^n *> r -->*
  l <* <[1;0;1;1]^^n {{A}}> [0;1] *> r.
Proof. gen l. induction n; intros l; [finish|]. simpl_tape.
  do 4 step. follow IHn. simpl_rotate. finish. Qed.
Lemma ones l r n : l {{A}}> [1]^^n *> r -->* l <* [1]^^n {{A}}> r.
Proof. shift_rule; steps. Qed.

(* Stop the carry at A>01; the generic scanner chooses the interior D phase. *)
Ltac ecb := intros; st; repeat (simpl_rotate; cbn;
  first [apply evstep_refl |
    match goal with
    | |- (A,(?l,0,1 >> [1;1]^^?n *> ?r)) -->* _ => follow (scanR l r n)
    | |- (A,(?l,0,1 >> [0;1;0;1]^^?n *> ?r)) -->* _ => follow (scanPair l r n)
    end | sr_l | sr_r | step1]).

Lemma right l r n : CB1.R l (CB1.D n *> r) -->* CB1.R (l <* CB1.S n) r.
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.
Lemma left l r n : CB1.L (l <* CB1.S n) r -->* CB1.L l (CB1.D n *> r).
Proof. unfold CB1.L, CB1.D, CB1.S. es. Qed.
Lemma blank l r : CB1.R l ([0;0;0] *> r) -->* CB1.L l (CB1.D 0 *> CB1.D 0 *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. es' & l r. Qed.
Lemma even l r n : CB1.R l ([1;1]^^(1+n) *> [0;0] *> r) -->*
  CB1.L l (CB1.D (1+n) *> [1;0] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.

Lemma restart l r b : CB1.L (l <* <[1;1;1] <* <[0;1]^^(1+b)) r -->*
  CB1.R (l <* <[0;1]^^(1+b)) r.
Proof.
  replace (l <* <[1;1;1] <* <[0;1]^^(1+b)) with (l <* <[1;1] <* CB1.S b)
    by (unfold CB1.S; simpl_rotate; reflexivity).
  follow left. unfold CB1.R, CB1.L, CB1.D. simpl_tape.
  do 5 step. follow scanR. simpl_rotate. finish.
Qed.
Lemma overflow2 r b : CB1.L (0inf <* <[1;1] <* <[0;1]^^(1+b)) r -->*
  CB1.R (0inf <* <[1;1]^^(1+b) <* <[0;1]^^2) ([1] *> r).
Proof. unfold CB1.R, CB1.L. es. Qed.
Lemma overflow1 r b n : CB1.L (0inf <* <[1] <* <[0;1]^^(1+b)) (CB1.D n *> r) -->*
  CB1.R (0inf <* <[1;1]^^b <* <[0;1]^^(n+2)) ([1;0] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.

Lemma collision l r : CB1.L (l <* <[1;0;1;1;0;0]) r -->* CB1.J l ([1;1;1;1] *> r).
Proof. unfold CB1.L, CB1.J. es' & l r. Qed.
Lemma collision_tail l r :
  l <* <[1;0;1;1;0] <{{C}} r -->* CB1.J l ([1;1] *> r).
Proof. unfold CB1.J. es' & l r. Qed.

Lemma leftJ l r n : CB1.J (l <* CB1.S n) r -->* CB1.L l (CB1.D (1+n) *> r).
Proof. unfold CB1.J, CB1.L, CB1.D, CB1.S. ecb. Qed.
Lemma turnB l r n : CB1.L (l <* <[1;1]) (CB1.D n *> r) -->*
  CB1.R (l <* <[0;1]^^(1+n)) r.
Proof. unfold CB1.L, CB1.R, CB1.D. ecb. Qed.
Lemma turnJ l r b : CB1.J (l <* <[1;1;1] <* <[0;1]^^b) r -->*
  CB1.R (l <* <[0;1]^^(1+b)) r.
Proof. unfold CB1.J, CB1.R. ecb. Qed.
Lemma finishP l r b : CB1.L (l <* CB1.S 0 <* <[1;0] <* <[0;1]^^(1+b)) r -->*
  CB1.J l (CB1.D (1+b) *> r).
Proof. unfold CB1.L, CB1.J, CB1.S, CB1.D. ecb. Qed.

Lemma defect0 l r m : CB1.R l ([1;0] *> CB1.D 0 *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.J l ([1;1;1;1] *> CB1.D m *> [1] *> r).
Proof. unfold CB1.R, CB1.J, CB1.D. ecb. Qed.
Lemma defect1 l r m : CB1.R l ([1;0] *> CB1.D 1 *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.L l (CB1.D 0 *> CB1.D 0 *> CB1.D (1+m) *> [1] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.
Lemma defect2 l r n m : CB1.R l ([1;0] *> CB1.D (2+n) *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* CB1.S 0 <* [1;1]^^n <* <[0;1]^^(2+m)) ([1] *> r).
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.
Lemma defect_blank0 l r : CB1.R l ([1;0] *> CB1.D 0 *> [0;0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* <[1;0;0;1]) r.
Proof. unfold CB1.R, CB1.S, CB1.D. ecb. Qed.
Lemma defect_blankS l r n : CB1.R l ([1;0] *> CB1.D (1+n) *> [0;0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* CB1.S 0 <* [1] <* [1;1]^^n <* <[0;1]) r.
Proof. unfold CB1.R, CB1.S, CB1.D. ecb. Qed.

Lemma paired l r k n : CB1.R l ([1;0]^^(k*2) *> CB1.D n *> r) -->*
  CB1.R (l <* CB1.S 0 <* <[1;0;1;1]^^k <* <[0;1]^^n) r.
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.

Lemma halt_window l r : halts tm (l <* <[1;1;1;0;0] <{{B}} r).
Proof. esx. Qed.

Lemma core : CB1.Core tm.
Proof.
  constructor; intros; try solve [eauto using right,left,restart,leftJ,turnJ,finishP].
  - unfold CB1.R,CB1.L,CB1.D. esx.
  - unfold CB1.R,CB1.J,CB1.D. ecb.
  - unfold CB1.R,CB1.D,CB1.PL,CB1.S. ecb.
Qed.


Lemma basic_valid : forall t, valid tm (basic_rule t).
Proof.
  basic_start; first [apply scanR | apply scanB | apply scanC |
    apply scanPair | apply ones | apply blank | apply even |
    apply restart | apply overflow2 | apply overflow1 |
    apply collision | apply leftJ | apply turnB | apply turnJ |
    apply defect0 | apply defect1 | apply defect2 |
    apply defect_blank0 | apply defect_blankS | apply paired].
Qed.
Lemma certified i : valid tm (CBSim.recipe_of i).
Proof. destruct i; cbn [CBSim.recipe_of]; [apply basic_valid|apply high_spec,core]. Qed.

Theorem halt: halts tm c0.
Proof. apply (CBSim.check_spec tm certified 100000%N). native_check_eq. Qed.
End TM7.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma scanR l r n :
  l {{A}}> [0;1] *> [1;1]^^n *> r -->*
  l <* <[0;1]^^n {{A}}> [0;1] *> r.
Proof. gen l. induction n; intros l; [finish|]. simpl_tape.
  do 6 step. follow IHn. simpl_rotate. finish. Qed.
Lemma scanB l r n :
  l <* <[1;0]^^n <{{B}} r -->* l <{{B}} [1;1]^^n *> r.
Proof. shift_rule; steps. Qed.
Lemma scanC l r n :
  l <* <[0;1]^^n <{{C}} r -->* l <{{C}} [1;1]^^n *> r.
Proof. shift_rule; steps. Qed.

Lemma scanPair l r n :
  l {{A}}> [0;1] *> [0;1;0;1]^^n *> r -->*
  l <* <[1;0;1;1]^^n {{A}}> [0;1] *> r.
Proof. gen l. induction n; intros l; [finish|]. simpl_tape.
  do 4 step. follow IHn. simpl_rotate. finish. Qed.
Lemma ones l r n : l {{A}}> [1]^^n *> r -->* l <* [1]^^n {{A}}> r.
Proof. shift_rule; steps. Qed.

(* Stop the carry at A>01; the generic scanner chooses the interior D phase. *)
Ltac ecb := intros; st; repeat (simpl_rotate; cbn;
  first [apply evstep_refl |
    match goal with
    | |- (A,(?l,0,1 >> [1;1]^^?n *> ?r)) -->* _ => follow (scanR l r n)
    | |- (A,(?l,0,1 >> [0;1;0;1]^^?n *> ?r)) -->* _ => follow (scanPair l r n)
    end | sr_l | sr_r | step1]).

Lemma right l r n : CB1.R l (CB1.D n *> r) -->* CB1.R (l <* CB1.S n) r.
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.
Lemma left l r n : CB1.L (l <* CB1.S n) r -->* CB1.L l (CB1.D n *> r).
Proof. unfold CB1.L, CB1.D, CB1.S. es. Qed.
Lemma blank l r : CB1.R l ([0;0;0] *> r) -->* CB1.L l (CB1.D 0 *> CB1.D 0 *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. es' & l r. Qed.
Lemma even l r n : CB1.R l ([1;1]^^(1+n) *> [0;0] *> r) -->*
  CB1.L l (CB1.D (1+n) *> [1;0] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.

Lemma restart l r b : CB1.L (l <* <[1;1;1] <* <[0;1]^^(1+b)) r -->*
  CB1.R (l <* <[0;1]^^(1+b)) r.
Proof.
  replace (l <* <[1;1;1] <* <[0;1]^^(1+b)) with (l <* <[1;1] <* CB1.S b)
    by (unfold CB1.S; simpl_rotate; reflexivity).
  follow left. unfold CB1.R, CB1.L, CB1.D. simpl_tape.
  do 5 step. follow scanR. simpl_rotate. finish.
Qed.
Lemma overflow2 r b : CB1.L (0inf <* <[1;1] <* <[0;1]^^(1+b)) r -->*
  CB1.R (0inf <* <[1;1]^^(1+b) <* <[0;1]^^2) ([1] *> r).
Proof. unfold CB1.R, CB1.L. es. Qed.
Lemma overflow1 r b n : CB1.L (0inf <* <[1] <* <[0;1]^^(1+b)) (CB1.D n *> r) -->*
  CB1.R (0inf <* <[1;1]^^b <* <[0;1]^^(n+2)) ([1;0] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.

Lemma collision l r : CB1.L (l <* <[1;0;1;1;0;0]) r -->* CB1.J l ([1;1;1;1] *> r).
Proof. unfold CB1.L, CB1.J. es' & l r. Qed.
Lemma collision_tail l r :
  l <* <[1;0;1;1;0] <{{C}} r -->* CB1.J l ([1;1] *> r).
Proof. unfold CB1.J. es' & l r. Qed.

Lemma leftJ l r n : CB1.J (l <* CB1.S n) r -->* CB1.L l (CB1.D (1+n) *> r).
Proof. unfold CB1.J, CB1.L, CB1.D, CB1.S. ecb. Qed.
Lemma turnB l r n : CB1.L (l <* <[1;1]) (CB1.D n *> r) -->*
  CB1.R (l <* <[0;1]^^(1+n)) r.
Proof. unfold CB1.L, CB1.R, CB1.D. ecb. Qed.
Lemma turnJ l r b : CB1.J (l <* <[1;1;1] <* <[0;1]^^b) r -->*
  CB1.R (l <* <[0;1]^^(1+b)) r.
Proof. unfold CB1.J, CB1.R. ecb. Qed.
Lemma finishP l r b : CB1.L (l <* CB1.S 0 <* <[1;0] <* <[0;1]^^(1+b)) r -->*
  CB1.J l (CB1.D (1+b) *> r).
Proof. unfold CB1.L, CB1.J, CB1.S, CB1.D. ecb. Qed.

Lemma defect0 l r m : CB1.R l ([1;0] *> CB1.D 0 *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.J l ([1;1;1;1] *> CB1.D m *> [1] *> r).
Proof. unfold CB1.R, CB1.J, CB1.D. ecb. Qed.
Lemma defect1 l r m : CB1.R l ([1;0] *> CB1.D 1 *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.L l (CB1.D 0 *> CB1.D 0 *> CB1.D (1+m) *> [1] *> r).
Proof. unfold CB1.R, CB1.L, CB1.D. ecb. Qed.
Lemma defect2 l r n m : CB1.R l ([1;0] *> CB1.D (2+n) *> [1] *> [1;1]^^m *> [0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* CB1.S 0 <* [1;1]^^n <* <[0;1]^^(2+m)) ([1] *> r).
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.
Lemma defect_blank0 l r : CB1.R l ([1;0] *> CB1.D 0 *> [0;0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* <[1;0;0;1]) r.
Proof. unfold CB1.R, CB1.S, CB1.D. ecb. Qed.
Lemma defect_blankS l r n : CB1.R l ([1;0] *> CB1.D (1+n) *> [0;0] *> r) -->*
  CB1.R (l <* CB1.S 0 <* CB1.S 0 <* [1] <* [1;1]^^n <* <[0;1]) r.
Proof. unfold CB1.R, CB1.S, CB1.D. ecb. Qed.

Lemma paired l r k n : CB1.R l ([1;0]^^(k*2) *> CB1.D n *> r) -->*
  CB1.R (l <* CB1.S 0 <* <[1;0;1;1]^^k <* <[0;1]^^n) r.
Proof. unfold CB1.R, CB1.D, CB1.S. ecb. Qed.

Lemma halt_window l r : halts tm (l <* <[1;1;1;0;0] <{{B}} r).
Proof. esx. Qed.

Lemma core : CB1.Core tm.
Proof.
  constructor; intros; try solve [eauto using right,left,restart,leftJ,turnJ,finishP].
  - unfold CB1.R,CB1.L,CB1.D. esx.
  - unfold CB1.R,CB1.J,CB1.D. ecb.
  - unfold CB1.R,CB1.D,CB1.PL,CB1.S. ecb.
Qed.


Lemma basic_valid : forall t, valid tm (basic_rule t).
Proof.
  basic_start; first [apply scanR | apply scanB | apply scanC |
    apply scanPair | apply ones | apply blank | apply even |
    apply restart | apply overflow2 | apply overflow1 |
    apply collision | apply leftJ | apply turnB | apply turnJ |
    apply defect0 | apply defect1 | apply defect2 |
    apply defect_blank0 | apply defect_blankS | apply paired].
Qed.
Lemma certified i : valid tm (CBSim.recipe_of i).
Proof. destruct i; cbn [CBSim.recipe_of]; [apply basic_valid|apply high_spec,core]. Qed.

Theorem halt: halts tm c0.
Proof. apply (CBSim.check_spec tm certified 100000%N). native_check_eq. Qed.
End TM13.
