From BusyCoq Require Import Individual62 SimplTape ES_v2 ES_v3
  Longitudinal LongitudinalHalt Eqb Helper.
Require Import List String NArith Lia ZifyNat ZifyN.
Import ListNotations.
Open Scope sym.

(* Shared word/signal checker for SOC31/Long57, SOC33/Long51 and SOC34/N79.
   All machine-specific rules, native seeds and final halting theorems are
   contained in TM1/TM2/TM3 below.  No local library dependency is needed. *)

Module BinaryHaltRules.
Inductive signal := H | K | J | U | V | W | X.
Inductive word := T | D0 | D1 | W00 | W0010 | W10 | W1 | W0.

Definition bits w : list Sym :=
  match w with
  | T => [1;0;1;0] | D0 => [0;0;0] | D1 => [1;0;0]
  | W00 => [0;0] | W0010 => [0;0;1;0] | W10 => [1;0]
  | W1 => [1] | W0 => [0]
  end.
Definition cells ws := List.concat (map bits ws).

(* Signals on the output are in execution order, NOT spatial order. *)
Definition f1_57 s w : option (list word * list signal) :=
  match s,w with
  | H,T => Some ([T],[H;H])
  | H,D0 => Some ([D1],[])
  | H,D1 => Some ([D0],[H])
  | H,W10 => Some ([],[J])
  | H,W1 => Some ([],[K])
  | K,T => Some ([D0],[J])
  | K,D0 => Some ([D0;W1],[])
  | K,D1 => Some ([],[V])
  | K,W10 => Some ([],[U])
  | K,W1 => Some ([],[X])
  | J,T => Some ([T],[J;H])
  | J,D0 => Some ([D0;W10],[])
  | J,D1 => Some ([T],[K])
  | J,W10 => Some ([T],[H;H])
  | J,W1 => Some ([],[W])
  | U,T => Some ([D0;T],[H;H])
  | U,D0 => Some ([D0],[W])
  | U,D1 => Some ([D0;D0],[H])
  | U,W10 => Some ([D0],[J])
  | U,W1 => Some ([D0],[K])
  | V,T => Some ([D0],[U;J])
  | V,D0 => Some ([D0;T],[H;H])
  | V,D1 => Some ([D0],[J;J])
  | V,W10 => Some ([D0],[K;J])
  | V,W1 => Some ([D0],[H;H;J])
  | W,T => Some ([D0;T],[])
  | W,D0 => Some ([T],[J])
  | W,D1 => Some ([D0;D1],[])
  | W,W10 => Some ([D0;W10],[])
  | W,W1 => Some ([D0;W1],[])
  | X,D0 => Some ([D0],[H;J])
  | _,_ => None
  end.

Definition f0_57 s : list word :=
  match s with
  | H => [D1] | K | J => [D0;D1]
  | U | V | X => [D0;T;D0;D1]
  | W => [T;D0;D1]
  end.

(* Long51 and N79 share the table, including the protected V/W00 rule. *)
Definition f1_51 s w : option (list word * list signal) :=
  match s,w with
  | H,T => Some ([T],[H;H])
  | H,D0 => Some ([D1],[])
  | H,D1 => Some ([D0],[H])
  | H,W0010 => Some ([T],[])
  | H,W00 => Some ([W10],[])
  | H,W10 => Some ([],[J])
  | H,W0 => Some ([W1],[])
  | H,W1 => Some ([],[K])
  | J,T => Some ([T],[J;H])
  | J,D1 => Some ([T],[K])
  | J,D0 => Some ([D0;W10],[])
  | J,W10 => Some ([T],[H;H])
  | J,W1 => Some ([],[W])
  | K,T => Some ([D1;W00],[])
  | K,D1 => Some ([],[V])
  | K,D0 => Some ([D0;W1],[])
  | K,W00 => Some ([D0],[H])
  | K,W10 => Some ([],[U])
  | K,W0010 => Some ([D0],[J])
  | K,W1 => Some ([],[X])
  | V,D0 => Some ([D1;W0010],[])
  | V,T => Some ([D1;W00],[U])
  | V,D1 => Some ([D1;W00],[J])
  | V,W10 => Some ([D1;W00],[K])
  | V,W1 => Some ([D1;W00],[H;H])
  | V,W00 => Some ([D1;W00;W1],[])
  | U,D1 => Some ([D1;D0],[])
  | U,D0 => Some ([D1;W00;W1],[])
  | U,T => Some ([D1;W0010],[])
  | W,D0 => Some ([T],[J])
  | W,D1 => Some ([D0;D1],[])
  | W,T => Some ([D0;T],[])
  | W,W10 => Some ([D0;W10],[])
  | X,D0 => Some ([D1;W00],[H])
  | _,_ => None
  end.

Definition f0_51 s : list word :=
  match s with
  | H => [D1] | K | J => [D0;D1]
  | U | V | X => [D1;W0010]
  | W => [T;D0;D1]
  end.
Definition halt_cell s w :=
  match s,w with X,T => true | _,_ => false end.

Definition lh := 0inf <* <[1].
End BinaryHaltRules.

Import BinaryHaltRules.

(* Explicit continuations retain the word produced by a caller until all its
   right-side signals have finished.  Neither a missing rule nor exhausted
   fuel is a halting certificate. *)
Module WordHalt.
Section Engine.
Context {Head Word : Type}.
Variable tm : TM.
Variable head : Head -> DH0 * DH0.
Variable bits : Word -> list Sym.

Definition cells ws := List.concat (map bits ws).
Definition tape ws := cells ws *> 0inf.
Definition signals h n := [head h]^^(N.to_nat n).
Fixpoint streams ps :=
  match ps with
  | [] => []
  | (h,n)::ps => signals h n ++ streams ps
  end.

Definition flow hs r (P : side -> Prop) :=
  sideRLs_halt tm hs r \/ exists s, sideRLs tm hs r s /\ P s.

Lemma flow_mono hs r (P Q : side -> Prop) :
  (forall s, P s -> Q s) -> flow hs r P -> flow hs r Q.
Proof. intros HP [HH|[s [HS H]]]; [left; exact HH|right; eauto]. Qed.

Lemma flow_nil r (P : side -> Prop) : P r -> flow [] r P.
Proof. intro H; right; exists r; split; [constructor|exact H]. Qed.

Lemma flow_app hs1 hs2 r (P : side -> Prop) :
  flow hs1 r (fun s => flow hs2 s P) -> flow (hs1++hs2) r P.
Proof.
  intros [HH|[s [HS [HH|[t [HT HP]]]]]].
  - left; apply sideRLs_halt_app_left,HH.
  - left; eapply sideRLs_halt_app_right; eauto.
  - right; exists t; split; [eapply sideRLs_trans; eauto|exact HP].
Qed.

Lemma flow_seg hs hs' w w' r (P : side -> Prop) :
  segRLs tm hs hs' w w' ->
  flow hs' r (fun s => P (w' *> s)) -> flow hs (w *> r) P.
Proof.
  intros HW [HH|[s [HS HP]]].
  - left; eapply segRLs_sideRLs_halt_concat; eauto.
  - right; exists (w' *> s); split.
    + eapply segRLs_sideRLs_concat; eauto.
    + exact HP.
Qed.

Inductive task := Call (h : Head) (n : N) | Put (ws : list Word).
Definition state := (list task * list Word)%type.
Fixpoint pending ks (r : side) : Prop :=
  match ks with
  | [] => False
  | Put ws::ks => pending ks (cells ws *> r)
  | Call h n::ks => flow (signals h n) r (pending ks)
  end.
Definition valid '(ks,ws) := pending ks (tape ws).
Lemma cells_app a b : cells (a++b) = cells a ++ cells b.
Proof. unfold cells; rewrite map_app,concat_app; reflexivity. Qed.

Lemma tape_cons w ws : tape (w::ws) = bits w *> tape ws.
Proof. unfold tape,cells; cbn; apply Str_app_assoc. Qed.

Lemma signals_add h a b : signals h (a+b) = signals h a ++ signals h b.
Proof. unfold signals; rewrite N2Nat.inj_add,lpow_add; reflexivity. Qed.

Lemma split_calls h n used ks r :
  (used<=n)%N ->
  flow (signals h used) r (pending (Call h (n-used)::ks)) ->
  pending (Call h n::ks) r.
Proof.
  intros Hle H; cbn [pending] in *.
  replace n with (used+(n-used))%N at 1 by lia.
  rewrite signals_add; apply flow_app,H.
Qed.

Theorem initial_spec h n ws :
  valid ([Call h n],ws) -> sideRLs_halt tm (signals h n) (tape ws).
Proof. intros [H|[s [_ H]]]; [exact H|contradiction]. Qed.
End Engine.
End WordHalt.

Module BinaryHaltCompute.

Definition singles hs : list (signal*N) := map (fun h => (h,1%N)) hs.
Definition digit (b:bool) := if b then D1 else D0.

Definition transfer (f1:signal->word->option(list word*list signal)) s n w
    : option (N * list (signal*N) * list word) :=
  match n with
  | N0 => None
  | Npos _ =>
    match s,w with
    | H,T => Some (n,[(H,(2*n)%N)],[T])
    | H,D0 => Some (n,[(H,N.div2 n)],[digit (N.odd n)])
    | H,D1 => Some (n,[(H,N.div2 (n+1))],[digit (N.odd (n+1))])
    | _,_ => match f1 s w with
             | Some(out,hs) => Some(1%N,singles hs,out)
             | None => None
             end
    end
  end.

Section TransferSound.
Variable tm : TM.
Variable head : signal -> DH0*DH0.
Variable f1 : signal -> word -> option(list word*list signal).
Hypothesis kernels : forall s w out hs, f1 s w=Some(out,hs) ->
  segRLs tm [head s] (map head hs) (bits w) (cells out).
Hypothesis H_T : segRLs tm [head H] [head H;head H] (bits T) (bits T).
Hypothesis H_0 : segRLs tm [head H] [] (bits D0) (bits D1).
Hypothesis H_1 : segRLs tm [head H] [head H] (bits D1) (bits D0).

Lemma streams_singles hs : WordHalt.streams head (singles hs)=map head hs.
Proof.
  induction hs as [|h hs IH]; [reflexivity|].
  change (head h::WordHalt.streams head (singles hs)=head h::map head hs).
  now rewrite IH.
Qed.

Lemma H_cycle b : segRLs tm ([head H]^^2) [head H]
  (bits(digit b)) (bits(digit b)).
Proof.
  destruct b.
  - change (segRLs tm ([head H]++[head H]) ([head H]++[]) (bits D1) (bits D1)).
    eapply segRLs_trans; [exact H_1|exact H_0].
  - change (segRLs tm ([head H]++[head H]) ([]++[head H]) (bits D0) (bits D0)).
    eapply segRLs_trans; [exact H_0|exact H_1].
Qed.

Lemma H_even b q : segRLs tm ([head H]^^(q*2)) ([head H]^^q)
  (bits(digit b)) (bits(digit b)).
Proof.
  pose proof (segRLs_addmul_v2 2 1 q 0 0 tm [head H]
    (bits(digit b)) (bits(digit b))) as E.
  replace (q*2+0)%nat with (q*2)%nat in E by lia.
  replace (q*1+0)%nat with q in E by lia.
  apply E; [constructor|apply H_cycle].
Qed.

Lemma H_odd (b:bool) q : segRLs tm ([head H]^^(q*2+1))
  ([head H]^^(q+(if b then 1 else 0)))
  (bits(digit b)) (bits(digit (negb b))).
Proof.
  rewrite lpow_add; change ([head H]^^1) with [head H].
  destruct b; cbn [digit negb].
  - rewrite lpow_add; change ([head H]^^1) with [head H].
    eapply segRLs_trans; [apply (H_even true)|exact H_1].
  - replace (q+0)%nat with q by lia.
    replace ([head H]^^q) with (([head H]^^q)++[]) by apply app_nil_r.
    eapply segRLs_trans; [apply (H_even false)|exact H_0].
Qed.

Lemma H_batch_T n : segRLs tm (WordHalt.signals head H n)
  (WordHalt.signals head H (2*n)) (bits T) (bits T).
Proof.
  unfold WordHalt.signals.
  pose proof (segRLs_addmul_v2 1 2 (N.to_nat n) 0 0 tm [head H]
    (bits T) (bits T)) as E.
  replace (N.to_nat n*1+0)%nat with (N.to_nat n) in E by lia.
  replace (N.to_nat n*2+0)%nat with (N.to_nat (2*n)) in E by lia.
  apply E; [constructor|exact H_T].
Qed.

Lemma H_batch_digit b n : segRLs tm (WordHalt.signals head H n)
  (WordHalt.signals head H (N.div2 (n+N.b2n b)))
  (bits(digit b)) (bits(digit (N.odd (n+N.b2n b)))).
Proof.
  unfold WordHalt.signals.
  pose proof (N.div2_odd n) as E.
  pose proof (N.div2_odd (n+N.b2n b)) as F.
  destruct b; cbn [N.b2n] in F |- *.
  - rewrite N.odd_add in F |- *.
    destruct (N.odd n); cbn [N.b2n N.odd xorb digit] in E,F |- *.
    + applys_eq (H_odd true (N.to_nat (N.div2 n))); f_equal; lia.
    + applys_eq (H_even true (N.to_nat (N.div2 n))); f_equal; lia.
  - rewrite N.add_0_r in F |- *.
    destruct (N.odd n); cbn [N.b2n N.odd xorb digit] in E,F |- *.
    + applys_eq (H_odd false (N.to_nat (N.div2 n))); f_equal; lia.
    + applys_eq (H_even false (N.to_nat (N.div2 n))); f_equal; lia.
Qed.

Lemma transfer_spec s n w used ps out :
  transfer f1 s n w=Some(used,ps,out) -> (used<=n)%N /\
  segRLs tm (WordHalt.signals head s used) (WordHalt.streams head ps)
    (bits w) (WordHalt.cells bits out).
Proof.
  destruct n as [|p]; [discriminate|].
  destruct s,w; cbn [transfer];
    try match goal with
        | |- context[f1 ?s ?w] => destruct (f1 s w) as [[outs hs]|] eqn:E;
            [|discriminate]
        end;
    intro E0; inversion E0; subst; split; try lia.
  all: try solve [rewrite streams_singles; apply kernels; exact E].
  - cbn [WordHalt.streams WordHalt.cells map List.concat].
    rewrite app_nil_r,app_nil_r; apply H_batch_T.
  - cbn [WordHalt.streams WordHalt.cells map List.concat].
    rewrite app_nil_r,app_nil_r.
    pose proof (H_batch_digit false (N.pos p)) as HH.
    cbn [N.b2n] in HH; rewrite N.add_0_r in HH; exact HH.
  - cbn [WordHalt.streams WordHalt.cells map List.concat].
    rewrite app_nil_r,app_nil_r; exact (H_batch_digit true (N.pos p)).
Qed.
End TransferSound.

Definition initial n seed : @WordHalt.state signal word :=
  ([WordHalt.Call J n],seed).

Lemma source_halts tm (h:DH0*DH0) l :
  (forall r, l {{{(snd h,L)}}} r -[tm]->+ l {{{(fst h,R)}}} r) ->
  forall n r, sideRLs_halt tm ([h]^^n) r ->
  halts tm (l {{{(fst h,R)}}} r).
Proof.
  destruct h as [hR hL]; cbn [fst snd]; intro Source.
  induction n; intros r HH; cbn [lpow] in HH; [inversion HH|].
  inversion HH as [a b hs r0 HHalt | a b hs r0 r' Hret Hrest]; subst.
  - apply HHalt.
  - eapply halts_evstep; [apply IHn,Hrest|].
    apply progress_evstep; eapply progress_trans; [apply Hret|apply Source].
Qed.

End BinaryHaltCompute.

(* Smart continuations: move a LATER H batch across an owned normal prefix.
   Its emitted carry remains AFTER all earlier child calls.  No signal
   commutation and no prediction of a child's eventual return is used. *)
Module BinaryHaltSmart.
Notation task := (@WordHalt.task signal word).
Notation state := (@WordHalt.state signal word).
Notation Call := WordHalt.Call.
Notation Put := WordHalt.Put.

Definition signal_eqb a b :=
  match a,b with H,H | K,K | J,J | U,U | V,V | W,W | X,X => true | _,_ => false end.
Lemma signal_eqb_spec a b : signal_eqb a b=true -> a=b.
Proof. destruct a,b; cbn; congruence. Qed.

Definition push_call h n (ks:list task) :=
  match n with
  | N0 => ks
  | _ => match ks with
         | Call h' m::ks' => if signal_eqb h h' then Call h (n+m)::ks' else Call h n::ks
         | _ => Call h n::ks
         end
  end.

Definition normal_cell n w :=
  match w with
  | T => Some ((2*n)%N,T)
  | D0 => Some (N.div2 n,BinaryHaltCompute.digit (N.odd n))
  | D1 => Some (N.div2 (n+1),BinaryHaltCompute.digit (N.odd (n+1)))
  | _ => None
  end.
Fixpoint normal n ws : option (N*list word) :=
  match ws with
  | [] => Some (n,[])
  | w::ws => match normal_cell n w with
             | Some (n',w') => match normal n' ws with
                              | Some (n'',out) => Some (n'',w'::out)
                              | None => None
                              end
             | None => None
             end
  end.
Definition push_put out ks :=
  match out with
  | [] => ks
  | _ => match ks with
         | Call H n::ks' => match normal n out with
                           | Some (n',out') => push_call H n' (Put out'::ks')
                           | None => Put out::ks
                           end
         | _ => Put out::ks
         end
  end.
Fixpoint push_calls ps ks :=
  match ps with [] => ks | (h,n)::ps => push_call h n (push_calls ps ks) end.

(* Do not traverse a large binary budget merely to compute n-n. *)
Definition leftover h n w used :=
  match h,w with H,T | H,D0 | H,D1 => 0%N | _,_ => (n-used)%N end.
Lemma leftover_spec f1 h n w used ps out :
  BinaryHaltCompute.transfer f1 h n w=Some(used,ps,out) ->
  leftover h n w used=(n-used)%N.
Proof.
  destruct n as [|p]; [discriminate|].
  destruct h,w; cbn [leftover BinaryHaltCompute.transfer];
    intro E; try reflexivity; inversion E; subst; lia.
Qed.

Definition advance f1 f0 (c:state) : option (option state) :=
  let '(ks,ws):=c in
  match ks with
  | [] => None
  | Put out::ks => Some (Some (ks,out++ws))
  | Call h N0::ks => Some (Some (ks,ws))
  | Call h (Npos p)::ks =>
    match ws with
    | [] => Some (Some (push_call h (N.pred (Npos p)) ks,f0 h))
    | w::ws => if halt_cell h w then Some None else
      match BinaryHaltCompute.transfer f1 h (Npos p) w with
      | None => None
      | Some (used,ps,out) =>
        Some (Some (push_calls ps (push_put out (push_call h (leftover h (Npos p) w used) ks)),ws))
      end
    end
  end.
Definition tick f1 f0 c : state+bool :=
  match advance f1 f0 c with
  | None => inr false | Some None => inr true | Some (Some c') => inl c'
  end.
Definition run f1 f0 fuel c := N_iter_until (tick f1 f0) (inl c) fuel.
Definition check f1 f0 fuel c :=
  match run f1 f0 fuel c with inr b => b | _ => false end.

Section Sound.
Variable tm : TM.
Variable head : signal -> DH0*DH0.
Variable f1 : signal -> word -> option(list word*list signal).
Variable f0 : signal -> list word.
Hypothesis kernels : forall s w out hs, f1 s w=Some(out,hs) ->
  segRLs tm [head s] (map head hs) (bits w) (cells out).
Hypothesis H_T : segRLs tm [head H] [head H;head H] (bits T) (bits T).
Hypothesis H_0 : segRLs tm [head H] [] (bits D0) (bits D1).
Hypothesis H_1 : segRLs tm [head H] [head H] (bits D1) (bits D0).
Hypothesis blank : forall s, sideRLs tm [head s] 0inf (cells(f0 s)*>0inf).
Hypothesis halt_kernel : forall s w, halt_cell s w=true -> forall l r,
  halts tm (l {{{(fst(head s),R)}}} (bits w*>r)).

Local Notation pending := (WordHalt.pending tm head bits).
Local Notation valid := (WordHalt.valid tm head bits).
Local Notation flow := (WordHalt.flow tm).
Local Notation signals := (WordHalt.signals head).

Lemma flow_split hs1 hs2 r P : flow (hs1++hs2) r P ->
  flow hs1 r (fun s => flow hs2 s P).
Proof.
  intros [HH|[s [HS HP]]].
  - destruct (sideRLs_halt_split _ _ _ _ HH) as [HH'|[t [HT HH']]].
    + left; exact HH'.
    + right; exists t; split; [exact HT|left; exact HH'].
  - apply sideRLs_split in HS; destruct HS as [t [HT HS]].
    right; exists t; split; [exact HT|right; exists s; auto].
Qed.

Lemma push_call_spec h n ks r : pending (push_call h n ks) r -> pending (Call h n::ks) r.
Proof.
  destruct n as [|p]; cbn [push_call pending signals WordHalt.signals].
  - apply WordHalt.flow_nil.
  - destruct ks as [|[h' m|out] ks]; try trivial.
    destruct (signal_eqb h h') eqn:E; [|trivial].
    apply signal_eqb_spec in E; subst h'.
    change (flow (signals h (N.pos p+m)) r (pending ks) ->
      flow (signals h (N.pos p)) r (fun s => flow (signals h m) s (pending ks))).
    rewrite WordHalt.signals_add; apply flow_split.
Qed.

Lemma normal_cell_spec n w n' w' : normal_cell n w=Some(n',w') ->
  segRLs tm (signals H n) (signals H n') (bits w) (bits w').
Proof.
  destruct w; cbn [normal_cell]; intro E; try discriminate; inversion E; subst.
  - apply BinaryHaltCompute.H_batch_T,H_T.
  - pose proof (BinaryHaltCompute.H_batch_digit tm head H_0 H_1 false n) as HH.
    cbn [N.b2n] in HH; rewrite N.add_0_r in HH; exact HH.
  - exact (BinaryHaltCompute.H_batch_digit tm head H_0 H_1 true n).
Qed.

Lemma normal_spec ws n n' out : normal n ws=Some(n',out) ->
  segRLs tm (signals H n) (signals H n') (cells ws) (cells out).
Proof.
  revert n n' out; induction ws as [|w ws IH]; intros n n' out; cbn [normal].
  - intro E; inversion E; subst; apply segRLs_nil.
  - destruct (normal_cell n w) as [[m w']|] eqn:EC; [|discriminate].
    destruct (normal m ws) as [[m' out']|] eqn:ER; [|discriminate].
    intro E; inversion E; subst.
    change (segRLs tm (signals H n) (signals H n')
      (bits w++cells ws) (bits w'++cells out')).
    eapply segRLs_concat; [eapply normal_cell_spec; exact EC|eapply IH; exact ER].
Qed.

Lemma push_put_spec out ks r : pending (push_put out ks) r -> pending ks (cells out*>r).
Proof.
  destruct out as [|w out]; [trivial|].
  destruct ks as [|[h n|p] ks]; cbn [push_put]; try trivial.
  destruct h; try trivial.
  destruct (normal n (w::out)) as [[n' out']|] eqn:E; [|trivial].
  intro HP; apply push_call_spec in HP.
  cbn [pending] in HP |- *.
  eapply WordHalt.flow_seg; [eapply normal_spec; exact E|exact HP].
Qed.

Lemma push_calls_spec ps ks r : pending (push_calls ps ks) r ->
  flow (WordHalt.streams head ps) r (pending ks).
Proof.
  revert r; induction ps as [|[h n] ps IH]; intros r; cbn [push_calls WordHalt.streams].
  - apply WordHalt.flow_nil.
  - intro HP; apply push_call_spec in HP.
    apply WordHalt.flow_app; eapply WordHalt.flow_mono; [exact IH|exact HP].
Qed.

Lemma advance_spec c z : advance f1 f0 c=Some z ->
  match z with None => True | Some c' => valid c' end -> valid c.
Proof.
  destruct c as [ks ws]; destruct ks as [|[h n|out] ks]; cbn [advance]; try discriminate.
  - destruct n as [|p].
    + intro E; inversion E; subst; cbn [WordHalt.valid pending signals WordHalt.signals].
      apply WordHalt.flow_nil.
    + destruct ws as [|w ws].
      * intro E; inversion E; subst; cbn [WordHalt.valid].
        intro HP; apply push_call_spec in HP.
        apply WordHalt.split_calls with (used:=1%N); [lia|].
        right; exists (cells(f0 h)*>0inf); split; [apply blank|].
        replace (N.pos p-1)%N with (N.pred (N.pos p)) by lia; exact HP.
      * destruct (halt_cell h w) eqn:EH.
        -- intros E _; inversion E; subst; cbn [WordHalt.valid pending].
           left; destruct (head h) as [hR hL] eqn:ER.
           assert (EP : N.to_nat (N.pos p) = S (N.to_nat (N.pred (N.pos p)))) by lia.
           unfold WordHalt.signals; rewrite ER,EP; cbn [lpow]; constructor.
           intros l; rewrite WordHalt.tape_cons.
           pose proof (halt_kernel _ _ EH l (WordHalt.tape bits ws)) as HH.
           rewrite ER in HH; exact HH.
        -- destruct (BinaryHaltCompute.transfer f1 h (N.pos p) w)
             as [[[used ps] out']|] eqn:ET; [|discriminate].
           intro E; inversion E; subst; cbn [WordHalt.valid]; intro HP.
           rewrite (leftover_spec _ _ _ _ _ _ _ ET) in HP.
           destruct (BinaryHaltCompute.transfer_spec tm head f1 kernels H_T H_0 H_1
             _ _ _ _ _ _ ET) as [Hle HW].
           rewrite WordHalt.tape_cons; apply WordHalt.split_calls with (used:=used); [exact Hle|].
           eapply WordHalt.flow_seg; [exact HW|].
           apply push_calls_spec in HP; eapply WordHalt.flow_mono; [|exact HP].
           intros r Hr; apply push_put_spec in Hr; apply push_call_spec in Hr; exact Hr.
  - intro E; inversion E; subst.
    change (pending ks (WordHalt.tape bits (out++ws)) ->
      pending ks (WordHalt.cells bits out*>WordHalt.tape bits ws)).
    unfold WordHalt.tape; rewrite WordHalt.cells_app,Str_app_assoc; trivial.
Qed.

Lemma tick_spec c :
  match tick f1 f0 c with inl c' => valid c' | inr b => b=true end -> valid c.
Proof.
  unfold tick; destruct (advance f1 f0 c) as [[c'|]|] eqn:E; try discriminate.
  - apply (advance_spec _ _ E).
  - intros _; apply (advance_spec _ _ E); trivial.
Qed.

Lemma check_spec fuel c : check f1 f0 fuel c=true -> valid c.
Proof.
  assert (ER:match run f1 f0 fuel c with
    | inl c' => valid c' -> valid c | inr b => b=true -> valid c end).
  { unfold run; apply N_iter_until_spec.
    - intros x HX; pose proof (tick_spec x) as HS.
      destruct (tick f1 f0 x); intro Hy; apply HX,HS,Hy.
    - trivial. }
  unfold check; destruct (run f1 f0 fuel c); [discriminate|exact ER].
Qed.

Theorem checker_halts seed :
  (forall r, lh {{{(snd(head J),L)}}} r -[tm]->+ lh {{{(fst(head J),R)}}} r) ->
  c0 -[tm]->* lh {{{(fst(head J),R)}}} (cells seed*>0inf) ->
  forall n fuel, check f1 f0 fuel (BinaryHaltCompute.initial n seed)=true -> halts tm c0.
Proof.
  intros Source Init n fuel EC.
  apply check_spec in EC; apply WordHalt.initial_spec in EC.
  eapply halts_evstep; [|exact Init].
  eapply (BinaryHaltCompute.source_halts tm (head J) lh Source); exact EC.
Qed.
End Sound.
End BinaryHaltSmart.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LC_0RD0LE_1LE1RF_0LB0RC_0RE1RA").
Definition head s : DH0 * DH0 :=
  match s with
  | H => ((D,<[0]),(B,[0]))
  | K => ((F,<[0;1]),(B,[0]))
  | J => ((E,<[0;1;0]),(B,[0]))
  | U => ((B,<[0;1;1;1]),(B,[0]))
  | V => ((C,<[0;1;1;1;1]),(B,[0]))
  | W => ((C,<[0;1;0;0]),(B,[0]))
  | X => ((A,<[0;1;1]),(B,[0]))
  end.
Definition hR s := fst (head s).
Definition hL := snd (head H).
Definition f1 := f1_57.
Definition f0 := f0_57.
Definition seed := [D1;D1].

Lemma kernels s w out hs : f1 s w=Some(out,hs) ->
  segRLs tm [head s] (map head hs) (bits w) (cells out).
Proof.
  destruct s,w; cbn [f1 f1_57]; intro E; try discriminate;
    inversion E; subst; clear E;
    apply BoundedConfig.segRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma blank s : sideRLs tm [head s] 0inf (cells(f0 s)*>0inf).
Proof.
  change (sideRLs tm [head s] ([]*>0inf) (cells(f0 s)*>0inf)).
  destruct s; apply BoundedConfig.sideRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma halt_kernel s w : halt_cell s w=true -> forall l r,
  halts tm (l {{{(hR s,R)}}} (bits w*>r)).
Proof.
  destruct s,w; cbn [halt_cell]; intro E; try discriminate; intros l r.
  unfold halts, halts_in; exists 0%nat; eexists; split;
    [constructor|reflexivity].
Qed.

Lemma source r :
  lh {{{(hL,L)}}} r -[tm]->+ lh {{{(hR J,R)}}} r.
Proof. unfold lh, hL, hR, head, to_DH_config; es. Qed.

Lemma init : c0 -[tm]->*
  lh {{{(hR J,R)}}} (cells seed*>0inf).
Proof. unfold lh, hR, head, to_DH_config, cells, seed, bits; es. Qed.

Theorem halt : halts tm c0.
Proof.
  eapply BinaryHaltSmart.checker_halts with
    (head:=head) (f1:=f1)
    (f0:=f0) (seed:=seed)
    (n:=2199%N) (fuel:=330000000%N).
  - exact kernels.
  - exact (kernels H T [T] [H;H] eq_refl).
  - exact (kernels H D0 [D1] [] eq_refl).
  - exact (kernels H D1 [D0] [H] eq_refl).
  - exact blank.
  - exact halt_kernel.
  - exact source.
  - exact init.
  - native_check_eq.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RA---").
Definition head s : DH0 * DH0 :=
  match s with
  | H => ((C,<[0]),(A,[0]))
  | K => ((E,<[0;1]),(A,[0]))
  | J => ((D,<[0;1;0]),(A,[0]))
  | U => ((A,<[0;1;0;1]),(A,[0]))
  | V => ((B,<[0;1;0;1;1]),(A,[0]))
  | W => ((B,<[0;1;0;0]),(A,[0]))
  | X => ((F,<[0;1;0]),(A,[0]))
  end.
Definition hR s := fst (head s).
Definition hL := snd (head H).
Definition f1 := f1_51.
Definition f0 := f0_51.
Definition seed := [D1].

Lemma kernels s w out hs : f1 s w=Some(out,hs) ->
  segRLs tm [head s] (map head hs) (bits w) (cells out).
Proof.
  destruct s,w; cbn [f1 f1_51]; intro E; try discriminate;
    inversion E; subst; clear E;
    apply BoundedConfig.segRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma blank s : sideRLs tm [head s] 0inf (cells(f0 s)*>0inf).
Proof.
  change (sideRLs tm [head s] ([]*>0inf) (cells(f0 s)*>0inf)).
  destruct s; apply BoundedConfig.sideRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma halt_kernel s w : halt_cell s w=true -> forall l r,
  halts tm (l {{{(hR s,R)}}} (bits w*>r)).
Proof.
  destruct s,w; cbn [halt_cell]; intro E; try discriminate; intros l r.
  unfold halts, halts_in; exists 0%nat; eexists; split;
    [constructor|reflexivity].
Qed.

Lemma source r :
  lh {{{(hL,L)}}} r -[tm]->+ lh {{{(hR J,R)}}} r.
Proof. unfold lh, hL, hR, head, to_DH_config; es. Qed.

Lemma init : c0 -[tm]->*
  lh {{{(hR J,R)}}} (cells seed*>0inf).
Proof. unfold lh, hR, head, to_DH_config, cells, seed, bits; es. Qed.

Theorem halt : halts tm c0.
Proof.
  eapply BinaryHaltSmart.checker_halts with
    (head:=head) (f1:=f1)
    (f0:=f0) (seed:=seed)
    (n:=3116%N) (fuel:=80000000%N).
  - exact kernels.
  - exact (kernels H T [T] [H;H] eq_refl).
  - exact (kernels H D0 [D1] [] eq_refl).
  - exact (kernels H D1 [D0] [H] eq_refl).
  - exact blank.
  - exact halt_kernel.
  - exact source.
  - exact init.
  - native_check_eq.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LC_0RD0LE_1LE1RF_0LB0RC_0RE0RA").
Definition head s : DH0 * DH0 :=
  match s with
  | H => ((D,<[0]),(B,[0]))
  | K => ((F,<[0;1]),(B,[0]))
  | J => ((E,<[0;1;0]),(B,[0]))
  | U => ((B,<[0;1;0;1]),(B,[0]))
  | V => ((C,<[0;1;0;1;1]),(B,[0]))
  | W => ((C,<[0;1;0;0]),(B,[0]))
  | X => ((A,<[0;1;0]),(B,[0]))
  end.
Definition hR s := fst (head s).
Definition hL := snd (head H).
Definition f1 := f1_51.
Definition f0 := f0_51.
Definition seed := [D1;D1].

Lemma kernels s w out hs : f1 s w=Some(out,hs) ->
  segRLs tm [head s] (map head hs) (bits w) (cells out).
Proof.
  destruct s,w; cbn [f1 f1_51]; intro E; try discriminate;
    inversion E; subst; clear E;
    apply BoundedConfig.segRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma blank s : sideRLs tm [head s] 0inf (cells(f0 s)*>0inf).
Proof.
  change (sideRLs tm [head s] ([]*>0inf) (cells(f0 s)*>0inf)).
  destruct s; apply BoundedConfig.sideRLs_c_spec with (T:=1000%nat);
    vm_compute; reflexivity.
Qed.

Lemma halt_kernel s w : halt_cell s w=true -> forall l r,
  halts tm (l {{{(hR s,R)}}} (bits w*>r)).
Proof.
  destruct s,w; cbn [halt_cell]; intro E; try discriminate; intros l r.
  unfold halts, halts_in; exists 0%nat; eexists; split;
    [constructor|reflexivity].
Qed.

Lemma source r :
  lh {{{(hL,L)}}} r -[tm]->+ lh {{{(hR J,R)}}} r.
Proof. unfold lh, hL, hR, head, to_DH_config; es. Qed.

Lemma init : c0 -[tm]->*
  lh {{{(hR J,R)}}} (cells seed*>0inf).
Proof. unfold lh, hR, head, to_DH_config, cells, seed, bits; es. Qed.

Theorem halt : halts tm c0.
Proof.
  eapply BinaryHaltSmart.checker_halts with
    (head:=head) (f1:=f1)
    (f0:=f0) (seed:=seed)
    (n:=1092%N) (fuel:=10000000%N).
  - exact kernels.
  - exact (kernels H T [T] [H;H] eq_refl).
  - exact (kernels H D0 [D1] [] eq_refl).
  - exact (kernels H D1 [D0] [H] eq_refl).
  - exact blank.
  - exact halt_kernel.
  - exact source.
  - exact init.
  - native_check_eq.
Qed.
End TM3.
