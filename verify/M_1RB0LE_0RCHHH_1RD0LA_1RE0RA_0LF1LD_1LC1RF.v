(* 1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF halts from the blank tape, in state B reading 1
   (Skelet 1-like Class 1). No execution trace, rule list or certificate is stored in this file.

   The proof uses the longitudinal segment rules of Individual.v (segRLs/sideRLs), as Sk1Machines.v
   does for TM17 and TM94, with counts in binary N.
   - Right of the left wall 10101011111 0101 the tape is W^k0 w1 W^n1 w2 W^n2 ... wm W^nm t 0inf,
     with W = 001001100110: short cell words wi separated by runs of W, and a last word t before
     the blanks. The wall keeps its pattern but moves left: the tape grows by about 4 cells per
     signal.
   - Each excursion of the head is one signal: it leaves the wall in state B with 0101 on its left
     (hR), passes runs of W unchanged (wall, wallF), and at each cell is either sent back (the head
     returns left in state E, hE, or in state F with 00 on its right, hF) or passed on to the next
     cell. Doing so a cell takes a few W from the run on its right and gives a few W to the run on
     its left.
   - Every cell word runs into one of six cycles of rules. Per period (W given, W taken, signals
     passed on): one of period 4 (2, 1, 1), three of period 6 (3, 1, 0), two of period 12 (6, 3, 3).
     Cycles of period 4 and 12 pass on a quarter of the signals they receive, so between events the
     counts nk change linearly, 4 times slower at each cell to the right; [fwalk] and [batch] apply
     t signals to all cells at once in closed form.
   - Events are followed one signal at a time ([call]): a run used up (its two cells merge), a
     cell answering in F (the F signal returns to the wall, which starts a new cell, [emitF]),
     and in the end the halt.
   The machine-specific lemmas (the shift rules for W, the wall, the start) are proved by es/esx.
   Before its cycle a cell word may follow up to 38 other rules, and merged words bring more, so the
   rules are not listed here. The rule of a cell word is proposed by a short local run and accepted
   only through the proved specs of busycoq's checkers BoundedConfig.segRLs_c / sideRLs_c; accepted
   rules are kept in a trie. From the blank tape the checker makes 2632 rounds (a batch, then one
   signal followed cell by cell), accepts 343 cell rules and 29 rules of the last word, and never
   has more than 27 cells.
   Not covered by the theorem, from the same model run in Python: 50107690372337959 signals,
   21258455156613008579829807130432544 steps before the halting step. *)
From BusyCoq Require Import Individual62 Helper Eqb.
Require Import NArith PeanoNat ZifyNat Lia String List.
Import Eqb.
Open Scope sym_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC---_1RD0LA_1RE0RA_0LF1LD_1LC1RF"%string).

(* the table, spelled out: the theorem below is about exactly this machine *)
Lemma table :
  tm (A, S0) = Some (S1, R, B) /\ tm (A, S1) = Some (S0, L, E) /\
  tm (B, S0) = Some (S0, R, C) /\ tm (B, S1) = None /\
  tm (C, S0) = Some (S1, R, D) /\ tm (C, S1) = Some (S0, L, A) /\
  tm (D, S0) = Some (S1, R, E) /\ tm (D, S1) = Some (S0, R, A) /\
  tm (E, S0) = Some (S0, L, F) /\ tm (E, S1) = Some (S1, L, D) /\
  tm (F, S0) = Some (S1, L, C) /\ tm (F, S1) = Some (S1, R, F).
Proof. repeat split. Qed.

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Module BC := BoundedConfig.

(* ---------- signals and the shift rules for W ---------- *)
Definition W : list Sym := [0;0;1;0;0;1;1;0;0;1;1;0].
Definition hR : DH0 := (B,[1;0;1;0]).
Definition hE : DH0 := (E,[]).
Definition hF : DH0 := (F,[0;0]).
Definition hret (f:bool) : DH0 := if f then hF else hE.
Definition h : list (DH0*DH0) := [(hR,hE)].

Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. unfold h,hR,hE,W. esx. Qed.
Lemma wallF n : segRLs tm [(hR,hF)] [(hR,hF)] (W^^n) (W^^n).
Proof. unfold hR,hF,W. esx. Qed.
Lemma walls f n : segRLs tm [(hR,hret f)] [(hR,hret f)] (W^^n) (W^^n).
Proof. destruct f; [apply wallF|apply wall]. Qed.
Lemma passW n l r : l <* [1;0;1;0] {{B}}> W^^n *> r -->*
  l <* [1;1;1;1;1;0;1;0;1;0;1;0]^^n <* [1;0;1;0] {{B}}> r.
Proof. unfold W. es. Qed.

(* ---------- composing cell rules ---------- *)
Lemma comp_seg a b c1 c2 w u1 g1 w1 u2 g2 w2 :
  segRLs tm (h^^a) (h^^c1) (w ++ W^^u1) (W^^g1 ++ w1) ->
  segRLs tm (h^^b) (h^^c2) (w1 ++ W^^u2) (W^^g2 ++ w2) ->
  segRLs tm (h^^(a+b)) (h^^(c1+c2)) (w ++ W^^(u1+u2)) (W^^(g1+g2) ++ w2).
Proof.
  intros H1 H2. rewrite !lpow_add.
  pose proof (segRLs_concat H1 (segRLs_wall'' (n:=c1) (wall u2))) as I1.
  pose proof (segRLs_concat (segRLs_wall'' (n:=b) (wall g1)) H2) as I2.
  rewrite <-!app_assoc in I1.
  pose proof (segRLs_trans I1 I2) as I3.
  rewrite <-!app_assoc. exact I3.
Qed.
Lemma comp_tail a b w g1 w1 g2 w2 :
  sideRLs tm (h^^a) (w *> 0inf) ((W^^g1 ++ w1) *> 0inf) ->
  sideRLs tm (h^^b) (w1 *> 0inf) ((W^^g2 ++ w2) *> 0inf) ->
  sideRLs tm (h^^(a+b)) (w *> 0inf) ((W^^(g1+g2) ++ w2) *> 0inf).
Proof.
  intros H1 H2. rewrite !lpow_add.
  pose proof (segRLs_sideRLs_concat (segRLs_wall'' (n:=b) (wall g1)) H2) as I2.
  rewrite Str_app_assoc in H1.
  pose proof (sideRLs_trans H1 I2) as I3.
  rewrite <-app_assoc,Str_app_assoc. exact I3.
Qed.

(* ---------- checked cell rules, kept in a trie ---------- *)
Definition T0 := 3000%nat.
Definition entry := (N * list Sym * N * N)%type.  (* W given left, next word, W taken right, signals passed *)
Inductive trie := TL | TN (v:option entry) (t0 t1:trie).
Fixpoint lookup (w:list Sym) (t:trie) : option entry := match t with TL => None | TN v t0 t1 =>
  match w with [] => v | S0::w => lookup w t0 | S1::w => lookup w t1 end end.
Fixpoint tset (w:list Sym) (e:entry) (t:trie) : trie := match w,t with
  | [],TL => TN (Some e) TL TL | [],TN _ t0 t1 => TN (Some e) t0 t1
  | S0::w,TL => TN None (tset w e TL) TL | S0::w,TN v t0 t1 => TN v (tset w e t0) t1
  | S1::w,TL => TN None TL (tset w e TL) | S1::w,TN v t0 t1 => TN v t0 (tset w e t1) end.
Lemma lookup_tset w v e t : lookup w (tset v e t) = if eqb w v then Some e else lookup w t.
Proof.
  destruct (eqb_spec w v) as [->|Hne].
  - gen t. induction v as [|[] v IH]; intros [|x t0 t1]; cbn [tset lookup]; auto.
  - gen w t. induction v as [|[] v IH]; intros [|[] w] Hne [|x t0 t1]; cbn [tset lookup];
      try reflexivity; try congruence; try (destruct w; reflexivity);
      rewrite IH by congruence; try reflexivity; destruct w; reflexivity.
Qed.

Definition tinv (P:list Sym -> entry -> Prop) t := forall w e, lookup w t = Some e -> P w e.
Lemma tinv_TL P : tinv P TL.
Proof. intros w e H. destruct w; discriminate. Qed.
Lemma tinv_tset P t w e : tinv P t -> P w e -> tinv P (tset w e t).
Proof. intros H He v x. rewrite lookup_tset. destruct (eqb_spec v w); [congruence|apply H]. Qed.

Definition seg_ok w (e:entry) := let '(g,v,u,c):=e in
  segRLs tm (h^^1) (h^^N.to_nat c) (w ++ W^^N.to_nat u) (W^^N.to_nat g ++ v).
Definition tail_ok w (e:entry) := let '(g,v,u,c):=e in
  sideRLs tm (h^^1) (w *> 0inf) ((W^^N.to_nat g ++ v) *> 0inf).
Definition check_seg w (e:entry) := let '(g,v,u,c):=e in
  ((c =? 0)%N || (c =? 1)%N) && BC.segRLs_c tm h (h^^N.to_nat c) (w ++ W^^N.to_nat u) (W^^N.to_nat g ++ v) T0.
Definition check_tail w (e:entry) := let '(g,v,u,c):=e in BC.sideRLs_c tm h w (W^^N.to_nat g ++ v) T0.
Lemma check_seg_spec w e : check_seg w e = true -> seg_ok w e.
Proof.
  destruct e as [[[g v] u] c]. unfold check_seg,seg_ok. intros H.
  apply andb_prop in H as [_ H]. apply BC.segRLs_c_spec in H. exact H.
Qed.
Lemma check_tail_spec w e : check_tail w e = true -> tail_ok w e.
Proof.
  destruct e as [[[g v] u] c]. unfold check_tail,tail_ok. intros H.
  apply BC.sideRLs_c_spec in H. exact H.
Qed.

(* ---------- following the rules of one cell for n signals, with the cycle shortcut ---------- *)
Definition eff := (list Sym * N * N * N)%type.
Fixpoint walk t (w:list Sym) (n:nat) : option eff := match n with
  | O => Some (w,0,0,0)%N
  | S n => match lookup w t with None => None | Some (g,v,u,c) =>
      match walk t v n with None => None | Some (w',g',u',c') => Some (w',g+g',u+u',c+c')%N end end end.
Definition fwalk t w (n:N) (pre per:nat) : option eff :=
  if (n <=? N.of_nat (pre+per))%N then walk t w (N.to_nat n) else
  match walk t w pre with None => None | Some (w1,g1,u1,c1) =>
  match walk t w1 per with None => None | Some (w2,g2,u2,c2) =>
  if eqb w2 w1 then
    let m := (n - N.of_nat pre)%N in let k := (m / N.of_nat per)%N in
    match walk t w1 (N.to_nat (m mod N.of_nat per)) with None => None | Some (w3,g3,u3,c3) =>
      Some (w3,g1+k*g2+g3,u1+k*u2+u3,c1+k*c2+c3)%N end
  else None end end.

Section Walk.
Variable P : list Sym -> entry -> Prop.
Variable Sem : nat -> list Sym -> N -> N -> N -> list Sym -> Prop.
Hypothesis Sem0 : forall w, Sem 0 w 0 0 0 w.
Hypothesis Sem1 : forall w g v u c, P w (g,v,u,c) -> Sem 1 w g u c v.
Hypothesis SemC : forall a b w g1 u1 c1 w1 g2 u2 c2 w2, Sem a w g1 u1 c1 w1 -> Sem b w1 g2 u2 c2 w2 ->
  Sem (a+b) w (g1+g2) (u1+u2) (c1+c2) w2.
Variable t : trie.
Hypothesis Ht : tinv P t.

Lemma walk_spec n w w' g u c : walk t w n = Some (w',g,u,c) -> Sem n w g u c w'.
Proof.
  gen w w' g u c. induction n; intros w w' g u c H; cbn [walk] in H.
  - inverts H. apply Sem0.
  - destruct (lookup w t) as [[[[g1 v] u1] c1]|] eqn:E; try discriminate.
    destruct (walk t v n) as [[[[w2 g2] u2] c2]|] eqn:E2; inverts H.
    change (S n) with (1+n). eapply SemC; [apply Sem1,Ht,E|apply IHn,E2].
Qed.
Lemma cyc_spec k p w g u c : Sem p w g u c w ->
  Sem (k*p) w (N.of_nat k*g) (N.of_nat k*u) (N.of_nat k*c) w.
Proof.
  intros H. induction k.
  - apply Sem0.
  - replace (S k*p) with (p+k*p) by lia.
    replace (N.of_nat (S k)*g)%N with (g+N.of_nat k*g)%N by lia.
    replace (N.of_nat (S k)*u)%N with (u+N.of_nat k*u)%N by lia.
    replace (N.of_nat (S k)*c)%N with (c+N.of_nat k*c)%N by lia.
    eapply SemC; eauto.
Qed.
Lemma fwalk_spec n pre per w w' g u c : fwalk t w n pre per = Some (w',g,u,c) ->
  Sem (N.to_nat n) w g u c w'.
Proof.
  unfold fwalk. destruct (N.leb_spec n (N.of_nat (pre+per))); [apply walk_spec|].
  destruct (walk t w pre) as [[[[w1 g1] u1] c1]|] eqn:E1; try discriminate.
  destruct (walk t w1 per) as [[[[w2 g2] u2] c2]|] eqn:E2; try discriminate.
  destruct (eqb_spec w2 w1) as [->|]; try discriminate.
  destruct (walk t w1 (N.to_nat ((n-N.of_nat pre) mod N.of_nat per)))
    as [[[[w3 g3] u3] c3]|] eqn:E3; intros G; inverts G.
  apply walk_spec in E1,E2,E3.
  set (m:=(n-N.of_nat pre)%N) in *. set (k:=(m/N.of_nat per)%N) in *.
  assert (Hm:m=(N.of_nat per*k+m mod N.of_nat per)%N).
  { destruct per as [|per]; [subst k; cbn; destruct m; reflexivity|apply N.div_mod; lia]. }
  pose proof (cyc_spec (N.to_nat k) _ _ _ _ _ E2) as Ec. rewrite N2Nat.id in Ec.
  pose proof (SemC _ _ _ _ _ _ _ _ _ _ _ (SemC _ _ _ _ _ _ _ _ _ _ _ E1 Ec) E3) as F.
  replace (N.to_nat n) with (pre+N.to_nat k*per+N.to_nat (m mod N.of_nat per))%nat by lia.
  exact F.
Qed.
End Walk.

Definition SemS n w (g u c:N) w' := segRLs tm (h^^n) (h^^N.to_nat c) (w ++ W^^N.to_nat u) (W^^N.to_nat g ++ w').
Definition SemT n w (g u c:N) w' := sideRLs tm (h^^n) (w *> 0inf) ((W^^N.to_nat g ++ w') *> 0inf).
Lemma SemS0 w : SemS 0 w 0 0 0 w.
Proof. unfold SemS. cbn. rewrite app_nil_r. constructor. Qed.
Lemma SemS1 w g v u c : seg_ok w (g,v,u,c) -> SemS 1 w g u c v.
Proof. exact id. Qed.
Lemma SemSC a b w g1 u1 c1 w1 g2 u2 c2 w2 : SemS a w g1 u1 c1 w1 -> SemS b w1 g2 u2 c2 w2 ->
  SemS (a+b) w (g1+g2) (u1+u2) (c1+c2) w2.
Proof. unfold SemS. rewrite !N2Nat.inj_add. apply comp_seg. Qed.
Lemma SemT0 w : SemT 0 w 0 0 0 w.
Proof. unfold SemT. constructor. Qed.
Lemma SemT1 w g v u c : tail_ok w (g,v,u,c) -> SemT 1 w g u c v.
Proof. exact id. Qed.
Lemma SemTC a b w g1 u1 c1 w1 g2 u2 c2 w2 : SemT a w g1 u1 c1 w1 -> SemT b w1 g2 u2 c2 w2 ->
  SemT (a+b) w (g1+g2) (u1+u2) (c1+c2) w2.
Proof. unfold SemT. rewrite !N2Nat.inj_add. apply comp_tail. Qed.

(* ---------- t signals on the whole tape at once ---------- *)
Definition cells := list (list Sym * N).
Fixpoint cside (cs:cells) (tw:list Sym) : side := match cs with
  | [] => tw *> 0inf | (w,n)::cs => w *> W^^N.to_nat n *> cside cs tw end.
Fixpoint batch tbl ttbl (info:list (nat*nat)) (t:N) (cs:cells) (tw:list Sym) {struct cs} :
  option (N*cells*list Sym) :=
  match cs,info with
  | [],_ => if (t =? 0)%N then Some (0%N,[],tw) else
      if (t <=? 64)%N then match walk ttbl tw (N.to_nat t) with
        | Some (tw',g,_,_) => Some (g,[],tw') | None => None end else None
  | (w,n)::cs,(pre,per)::info => match fwalk tbl w t pre per with None => None | Some (w',g,u,c) =>
      if (u <=? n)%N then match batch tbl ttbl info c cs tw with None => None
        | Some (e,cs',tw') => Some (g,(w',n-u+e)%N::cs',tw') end else None end
  | _,_ => None end.

Lemma batch_spec tbl ttbl info t cs tw e cs' tw' : tinv seg_ok tbl -> tinv tail_ok ttbl ->
  batch tbl ttbl info t cs tw = Some (e,cs',tw') ->
  sideRLs tm (h^^N.to_nat t) (cside cs tw) (W^^N.to_nat e *> cside cs' tw').
Proof.
  intros Ht Htt. gen info t e cs'. induction cs as [|[w n] cs IH]; intros info t e cs' H.
  - simpl in H. destruct (t =? 0)%N eqn:Et.
    + apply N.eqb_eq in Et. subst t. injection H as <- <- <-. constructor.
    + destruct (t <=? 64)%N; [|discriminate].
      destruct (walk ttbl tw (N.to_nat t)) as [[[[w' g] u] c]|] eqn:E; [|discriminate].
      injection H as <- <- <-.
      pose proof (walk_spec tail_ok SemT SemT0 SemT1 SemTC ttbl Htt _ _ _ _ _ _ E) as I.
      unfold SemT in I. rewrite Str_app_assoc in I. exact I.
  - destruct info as [|[pre per] info]; cbn [batch] in H; try discriminate.
    destruct (fwalk tbl w t pre per) as [[[[w' g] u] c]|] eqn:E; try discriminate.
    destruct (N.leb_spec u n) as [Hun|Hun]; try discriminate.
    destruct (batch tbl ttbl info c cs tw) as [[[e' cs''] tw'']|] eqn:E2; inverts H.
    pose proof (fwalk_spec seg_ok SemS SemS0 SemS1 SemSC tbl Ht _ _ _ _ _ _ _ _ E) as I.
    unfold SemS in I. specialize (IH _ _ _ _ E2).
    pose proof (segRLs_sideRLs_concat (segRLs_concat I
      (segRLs_wall'' (n:=N.to_nat c) (wall (N.to_nat (n-u))))) IH) as J.
    cbn [cside]. replace (N.to_nat n) with (N.to_nat u+N.to_nat (n-u))%nat by lia.
    replace (N.to_nat (n-u+e')) with (N.to_nat (n-u)+N.to_nat e')%nat by lia.
    rewrite !lpow_add. repeat rewrite <-app_assoc in J. repeat rewrite Str_app_assoc in *. exact J.
Qed.

(* ---------- local runs: they only propose; every use below is checked ---------- *)
Inductive res := RLeft (f:bool) (s:list Sym) | RRight (x:list Sym) | RMore | RHalt | RFail.
Definition classify (x:BC.T) : res :=
  match x with
  | BC.Build_T l [] q L => if eqb q E then RLeft false l else
      if eqb q F then match l with 0::0::s => RLeft true s | _ => RFail end else RFail
  | BC.Build_T l [] q R => if eqb q B then
      match l with 1::0::1::0::x => RRight x | _ => RMore end else RMore
  | BC.Build_T l (m::_) q _ => match tm (q,m) with None => RHalt | Some _ => RFail end
  end.
Definition runR s := match BC.steps tm T0 (BC.Build_T [1;0;1;0] s B R) with
  | Some x => classify x | None => RFail end.
Definition runL (f:bool) x := match BC.steps tm T0 (BC.Build_T (if f then [0;0] else []) x (if f then F else E) L) with
  | Some x => classify x | None => RFail end.
Definition runT s := match BC.steps_r0inf tm T0 (BC.Build_T [1;0;1;0] s B R) with
  | Some x => classify x | None => RFail end.

Lemma classify_right x y : classify x = RRight y -> x = BC.Build_T (1::0::1::0::y) [] B R.
Proof.
  destruct x as [l [|m r] q []]; cbn [classify].
  - destruct (eqb q E); [discriminate|]. destruct (eqb q F); [|discriminate].
    destruct l as [|[] [|[] l]]; discriminate.
  - destruct (eqb_spec q B); [subst|discriminate].
    destruct l as [|[] [|[] [|[] [|[] l]]]]; intros H; inverts H; reflexivity.
  - destruct (tm (q,m)); discriminate.
  - destruct (tm (q,m)); discriminate.
Qed.
Lemma classify_halt x : classify x = RHalt -> forall l0 r0, halted tm (BC.to_config x l0 r0).
Proof.
  destruct x as [l [|m r] q []]; cbn [classify].
  - destruct (eqb q E); [discriminate|]. destruct (eqb q F); [|discriminate].
    destruct l as [|[] [|[] l]]; discriminate.
  - destruct (eqb q B); [|discriminate]. destruct l as [|[] [|[] [|[] [|[] l]]]]; discriminate.
  - destruct (tm (q,m)) eqn:E; [discriminate|]. intros _ l0 r0. exact E.
  - destruct (tm (q,m)) eqn:E; [discriminate|]. intros _ l0 r0. exact E.
Qed.
Lemma runR_right s y : runR s = RRight y ->
  forall l r, l <* [1;0;1;0] {{B}}> s *> r -->* l <* y <* [1;0;1;0] {{B}}> r.
Proof.
  unfold runR. pose proof (BC.steps_spec tm T0 (BC.Build_T [1;0;1;0] s B R)) as I.
  destruct (BC.steps tm T0 _) as [x|]; [|discriminate].
  intros E. apply classify_right in E. subst x. intros l r. exact (I l r).
Qed.
Lemma runR_halt s : runR s = RHalt -> forall l r, halts tm (l <* [1;0;1;0] {{B}}> s *> r).
Proof.
  unfold runR. pose proof (BC.steps_spec tm T0 (BC.Build_T [1;0;1;0] s B R)) as I.
  destruct (BC.steps tm T0 _) as [x|]; [|discriminate].
  intros E l r. eapply halts_evstep; [apply halted_halts,(classify_halt _ E l r)|exact (I l r)].
Qed.
Lemma runT_halt s : runT s = RHalt -> forall l, halts tm (l <* [1;0;1;0] {{B}}> s *> 0inf).
Proof.
  unfold runT. pose proof (BC.steps_r0inf_spec tm T0 (BC.Build_T [1;0;1;0] s B R)) as I.
  destruct (BC.steps_r0inf tm T0 _) as [x|]; [|discriminate].
  intros E l. eapply halts_evstep; [apply halted_halts,(classify_halt _ E l (const s0))|exact (I l)].
Qed.

(* ---------- finding the rule of a cell word ---------- *)
Fixpoint lead (u:list Sym) (fuel:nat) (s:list Sym) : N * list Sym := match fuel with
  | O => (0%N,s)
  | S fuel => if eqb (firstn 12 s) u then let '(g,c):=lead u fuel (skipn 12 s) in ((1+g)%N,c) else (0%N,s) end.
Definition split3 (s:list Sym) : N * list Sym * N :=
  let '(g,c):=lead W (length s) s in let '(b,c'):=lead (rev W) (length c) (rev c) in (g,rev c',b).
Fixpoint strip0 (s:list Sym) := match s with
  | [] => [] | b::s => match strip0 s with [] => if eqb b 0 then [] else [b] | s' => b::s' end end.
Fixpoint mk_seg (w:list Sym) (j fuel:nat) : option entry := match fuel with O => None | S fuel =>
  match runR (w ++ W^^j) with
  | RMore => mk_seg w (S j) fuel
  | RLeft false s => let '(g,c,b):=split3 s in Some (g,c,(N.of_nat j-b)%N,0%N)
  | RRight x => match runL false x with
      | RLeft false s => let '(g,c,b):=split3 s in Some (g,c,(N.of_nat j-b)%N,1%N)
      | _ => mk_seg w (S j) fuel end
  | _ => None end end.
Definition mk_tail w : option entry := match runT w with
  | RLeft false s => let '(g,c,b):=split3 (strip0 s) in Some (g,c,0%N,0%N)
  | _ => None end.
Definition okP (tail:bool) := if tail then tail_ok else seg_ok.
Definition get_rule (tail:bool) (t:trie) w : option entry * trie :=
  match lookup w t with Some e => (Some e,t) | None =>
    match (if tail then mk_tail w else mk_seg w 0 13) with
    | Some e => if (if tail then check_tail w e else check_seg w e) then (Some e,tset w e t) else (None,t)
    | None => (None,t) end end.
Lemma get_rule_inv tail t w : tinv (okP tail) t -> tinv (okP tail) (snd (get_rule tail t w)).
Proof.
  intros H. unfold get_rule. destruct (lookup w t); [exact H|].
  destruct (if tail then mk_tail w else mk_seg w 0 13) as [e|]; [|exact H].
  destruct (if tail then check_tail w e else check_seg w e) eqn:C; [|exact H].
  apply tinv_tset; [exact H|]. destruct tail; [apply check_tail_spec|apply check_seg_spec]; exact C.
Qed.

(* the orbit of a cell word under its rules, up to the first repeated word *)
Fixpoint index_of (w:list Sym) (l:list (list Sym)) (i:nat) : option nat := match l with
  | [] => None | v::l => if eqb w v then Some i else index_of w l (S i) end.
Fixpoint rho_go tail t (w:list Sym) (seen:list (list Sym)) (acc:list entry) (fuel:nat) :
  list entry * option nat * trie := match fuel with O => (rev acc,None,t) | S fuel =>
  match index_of w seen 0 with Some i => (rev acc,Some i,t) | None =>
  let '(oe,t):=get_rule tail t w in
  match oe with None => (rev acc,None,t) | Some e => let '(_,v,_,_):=e in
    rho_go tail t v (seen ++ [w]) (e::acc) fuel end end end.
Lemma rho_go_inv tail t w seen acc fuel : tinv (okP tail) t ->
  tinv (okP tail) (snd (rho_go tail t w seen acc fuel)).
Proof.
  gen t w seen acc. induction fuel; intros t w seen acc H; cbn [rho_go]; [exact H|].
  destruct (index_of w seen 0); [exact H|].
  pose proof (get_rule_inv tail t w H) as G. destruct (get_rule tail t w) as [[[[[g v] u] c]|] t'];
    [apply IHfuel,G|exact G].
Qed.

(* the largest batch that keeps every cell inside its known orbit (a proposal, not trusted) *)
Definition fld (k:nat) (e:entry) : N := let '(g,_,u,c):=e in match k with O => g | 1%nat => u | _ => c end.
Fixpoint pref_max k (l:list entry) (s B t:N) : N * N * bool := match l with
  | [] => (t,s,true)
  | e::l => if (s + fld k e <=? B)%N then pref_max k l (s + fld k e) B (t+1) else (t,s,false) end.
Definition maxT k (seq:list entry) (back:option nat) (B:N) : N :=
  match back with
  | None => let '(t,_,_):=pref_max k seq 0 B 0 in t
  | Some bk => let '(t,s,full):=pref_max k (firstn bk seq) 0 B 0 in
      if negb full then t else
      let cyc := skipn bk seq in
      let Fc := fold_left (fun a e => a + fld k e)%N cyc 0%N in
      if (Fc =? 0)%N then (2^200)%N else
      let q := ((B - s) / Fc)%N in
      let '(r,_,_):=pref_max k cyc 0 (B - s - q*Fc) 0 in
      (N.of_nat bk + q*N.of_nat (length cyc) + r)%N end.
Fixpoint prop_go tbl ttbl (cs:cells) (tw:list Sym) : N * list (nat*nat) * trie * trie :=
  match cs with
  | [] => let '(seq,bk,ttbl):=rho_go true ttbl tw [] [] 64 in (N.min 64 (maxT 3 seq bk 0),[],tbl,ttbl)
  | (w,n)::cs => let '(cap,info,tbl,ttbl):=prop_go tbl ttbl cs tw in
      let '(seq,bk,tbl):=rho_go false tbl w [] [] 64 in
      let pp := match bk with Some b => (b,(length seq - b)%nat) | None => (length seq,1%nat) end in
      (N.min (maxT 1 seq bk n) (maxT 3 seq bk cap),pp::info,tbl,ttbl) end.
Lemma prop_go_inv tbl ttbl cs tw : tinv seg_ok tbl -> tinv tail_ok ttbl ->
  let '(_,_,tbl',ttbl'):=prop_go tbl ttbl cs tw in tinv seg_ok tbl' /\ tinv tail_ok ttbl'.
Proof.
  intros H1 H2. induction cs as [|[w n] cs IH]; cbn [prop_go].
  - pose proof (rho_go_inv true ttbl tw [] [] 64 H2) as G.
    destruct (rho_go true ttbl tw [] [] 64) as [[seq bk] t']. auto.
  - destruct (prop_go tbl ttbl cs tw) as [[[cap info] t1] t2]. destruct IH as [G1 G2].
    pose proof (rho_go_inv false t1 w [] [] 64 G1) as G.
    destruct (rho_go false t1 w [] [] 64) as [[seq bk] t']. auto.
Qed.

(* ---------- one signal followed through the tape, cell by cell ---------- *)
Inductive outcome := Stuck | Back (f:bool) (a:N) (cs:cells) (tw:list Sym) | Halted.
Fixpoint call (fuel:nat) (cs:cells) (tw:list Sym) : outcome := match fuel with O => Stuck | S fuel =>
  match cs with
  | [] => match runT tw with
      | RLeft f s => let '(g,c,_):=split3 (strip0 s) in
          if BC.sideRLs_c tm [(hR,hret f)] tw (W^^N.to_nat g ++ c) T0 then Back f g [] c else Stuck
      | RHalt => Halted
      | _ => Stuck end
  | (w,n)::rest =>
      let j := N.min n 12 in let s := w ++ W^^N.to_nat j in
      match runR s with
      | RLeft f s2 => let '(g,c,b):=split3 s2 in
          if BC.segRLs_c tm [(hR,hret f)] [] s (W^^N.to_nat g ++ c ++ W^^N.to_nat b) T0
          then Back f g ((c,b+(n-j))%N::rest) tw else Stuck
      | RRight x => match call fuel rest tw with
          | Back f' a rest' tw' => match runL f' x with
              | RLeft f s2 => let '(g,c,b):=split3 s2 in
                  if BC.segRLs_c tm [(hR,hret f)] [(hR,hret f')] s (W^^N.to_nat g ++ c ++ W^^N.to_nat b) T0
                  then Back f g ((c,b+(n-j)+a)%N::rest') tw' else Stuck
              | _ => Stuck end
          | Halted => Halted
          | Stuck => Stuck end
      | RMore => if (n <=? 12)%N then match rest with
          | (w2,n2)::rest2 => call fuel ((w ++ W^^N.to_nat n ++ w2,n2)::rest2) tw
          | [] => call fuel [] (w ++ W^^N.to_nat n ++ tw) end else Stuck
      | RHalt => Halted
      | RFail => Stuck end end end.

Lemma sideRLs_one a b r r' : sideRLs tm [(a,b)] r r' -> sideRL tm a b r r'.
Proof.
  intros H. inversion H as [|? ? ? r2 ? ? H1 H2]; subst.
  inversion H2; subst. exact H1.
Qed.

Lemma call_spec fuel cs tw : match call fuel cs tw with
  | Back f a cs' tw' => sideRL tm hR (hret f) (cside cs tw) (W^^N.to_nat a *> cside cs' tw')
  | Halted => forall l, halts tm (l <* [1;0;1;0] {{B}}> cside cs tw)
  | Stuck => True end.
Proof.
  gen cs tw. induction fuel as [|fuel IH]; intros cs tw; [exact I|]. cbn [call].
  destruct cs as [|[w n] rest].
  - destruct (runT tw) as [f s|x| | |] eqn:E; try exact I.
    + destruct (split3 (strip0 s)) as [[g c] b].
      destruct (BC.sideRLs_c tm [(hR,hret f)] tw (W^^N.to_nat g ++ c) T0) eqn:C; [|exact I].
      apply BC.sideRLs_c_spec,sideRLs_one in C. cbn [cside]. rewrite <-Str_app_assoc. exact C.
    + intros l. exact (runT_halt _ E l).
  - assert (Es:forall X, (w ++ W^^N.to_nat (N.min n 12)) *> W^^N.to_nat (n-N.min n 12) *> X =
      w *> W^^N.to_nat n *> X).
    { intros X. rewrite Str_app_assoc,<-(Str_app_assoc (W^^_)),<-lpow_add.
      do 3 f_equal. lia. }
    destruct (runR (w ++ W^^N.to_nat (N.min n 12))) as [f s2|x| | |] eqn:E; try exact I.
    + destruct (split3 s2) as [[g c] b].
      destruct (BC.segRLs_c _ _ _ _ _ _) eqn:C; [|exact I].
      apply BC.segRLs_c_spec in C.
      pose proof (segRLs_sideRLs_concat C (sideRLseq_O tm (W^^N.to_nat (n-N.min n 12) *> cside rest tw))) as K.
      apply sideRLs_one in K. cbn [cside]. rewrite <-Es,N2Nat.inj_add,lpow_add.
      repeat rewrite Str_app_assoc in *. exact K.
    + pose proof (IH rest tw) as Hc. destruct (call fuel rest tw) as [|f' a rest' tw'|]; try exact Hc.
      * destruct (runL f' x) as [f s2| | | |]; try exact I.
        destruct (split3 s2) as [[g c] b].
        destruct (BC.segRLs_c _ _ _ _ _ _) eqn:C; [|exact I].
        apply BC.segRLs_c_spec in C.
        pose proof (segRLs_concat C (walls f' (N.to_nat (n-N.min n 12)))) as J.
        pose proof (segRLs_sideRLs_concat J (sideRL_1 _ _ _ _ _ Hc)) as K.
        apply sideRLs_one in K. cbn [cside]. rewrite <-Es,!N2Nat.inj_add,!lpow_add.
        repeat rewrite Str_app_assoc in *. exact K.
      * intros l. cbn [cside]. rewrite <-Es. eapply halts_evstep; [|apply (runR_right _ _ E)].
        eapply halts_evstep; [apply Hc|apply passW].
    + destruct (N.leb_spec n 12); [|exact I]. destruct rest as [|[w2 n2] rest2].
      * pose proof (IH [] (w ++ W^^N.to_nat n ++ tw)) as Hc.
        destruct (call fuel [] _); cbn [cside] in *; rewrite ?Str_app_assoc in Hc; exact Hc.
      * pose proof (IH ((w ++ W^^N.to_nat n ++ w2,n2)::rest2) tw) as Hc.
        destruct (call fuel _ tw); cbn [cside] in *; rewrite ?Str_app_assoc in Hc; exact Hc.
    + intros l. cbn [cside]. rewrite <-Es. apply (runR_halt _ E).
Qed.

(* ---------- the left wall ---------- *)
Definition wl : side := 0inf <* <[1;0;1;0;1;0;1;1;1;1;1].
Definition start (r:side) := wl <* [1;0;1;0] {{B}}> r.
Definition newcell : list Sym := [0;0;1;0;0;1;1;1;0].
Lemma emitE r : wl <{{E}} r -->* start r.
Proof. unfold wl,start. es. Qed.
Lemma emitF r : wl <{{F}} [0;0] *> r -->* start (newcell *> r).
Proof. unfold wl,start,newcell. es. Qed.
Lemma init : c0 -->* start 0inf.
Proof. unfold start,wl. solve_init. Qed.
Lemma calls t r r' : sideRLs tm (h^^t) r r' -> start r -->* start r'.
Proof.
  gen r. induction t as [|t IH]; intros r H; cbn [lpow h app] in H.
  - inverts H. constructor.
  - inversion H as [|? ? ? r2 ? ? H1 H2]; subst.
    eapply evstep_trans; [|exact (IH _ H2)].
    apply progress_evstep. eapply progress_evstep_trans; [exact (H1 wl)|apply emitE].
Qed.

(* ---------- the checker: a batch, then one signal followed explicitly, until the halt ---------- *)
Record rstate := St { sk:N; scs:cells; stw:list Sym; stb:trie; stt:trie }.
Definition conf (x:rstate) := start (W^^N.to_nat (sk x) *> cside (scs x) (stw x)).
Definition tries_ok (x:rstate) := tinv seg_ok (stb x) /\ tinv tail_ok (stt x).
Definition bstep (x:rstate) : rstate :=
  let '(St k cs tw tbl ttbl):=x in
  let '(t,info,tbl,ttbl):=prop_go tbl ttbl cs tw in
  if (0 <? t)%N then match batch tbl ttbl info t cs tw with
    | Some (e,cs',tw') => St (k+e) cs' tw' tbl ttbl | None => St k cs tw tbl ttbl end
  else St k cs tw tbl ttbl.
Definition estep (x:rstate) : rstate + bool :=
  let '(St k cs tw tbl ttbl):=x in
  match call 200 cs tw with
  | Back false a cs' tw' => inl (St (k+a) cs' tw' tbl ttbl)
  | Back true a cs' tw' => inl (St 0 ((newcell,k+a)%N::cs') tw' tbl ttbl)
  | Halted => inr true
  | Stuck => inr false end.

Lemma bstep_spec x : tries_ok x -> tries_ok (bstep x) /\ conf x -->* conf (bstep x).
Proof.
  destruct x as [k cs tw tbl ttbl]. intros [H1 H2]. unfold bstep.
  pose proof (prop_go_inv tbl ttbl cs tw H1 H2) as G.
  destruct (prop_go tbl ttbl cs tw) as [[[t info] tbl'] ttbl']. destruct G as [G1 G2].
  destruct (0 <? t)%N; [|split; [split; assumption|constructor]].
  destruct (batch tbl' ttbl' info t cs tw) as [[[e cs'] tw']|] eqn:E;
    [|split; [split; assumption|constructor]].
  split; [split; assumption|]. unfold conf; cbn [sk scs stw].
  pose proof (segRLs_sideRLs_concat (segRLs_wall'' (n:=N.to_nat t) (wall (N.to_nat k)))
    (batch_spec _ _ _ _ _ _ _ _ _ G1 G2 E)) as I.
  apply calls in I. rewrite N2Nat.inj_add,lpow_add,Str_app_assoc. exact I.
Qed.

Lemma estep_spec x : match estep x with
  | inl y => (tries_ok x -> tries_ok y) /\ conf x -->* conf y
  | inr b => b = true -> halts tm (conf x) end.
Proof.
  destruct x as [k cs tw tbl ttbl]. unfold estep.
  pose proof (call_spec 200 cs tw) as C.
  destruct (call 200 cs tw) as [|[] a cs' tw'|]; unfold conf; cbn [sk scs stw].
  - discriminate.
  - split; [exact id|].
    pose proof (segRLs_sideRLs_concat (wallF (N.to_nat k)) (sideRL_1 _ _ _ _ _ C)) as I.
    apply sideRLs_one in I. specialize (I wl).
    eapply evstep_trans; [apply progress_evstep,I|].
    cbn [cside]. rewrite N2Nat.inj_add,lpow_add,Str_app_assoc. apply emitF.
  - split; [exact id|].
    pose proof (segRLs_sideRLs_concat (wall (N.to_nat k)) (sideRL_1 _ _ _ _ _ C)) as I.
    apply (calls 1). rewrite N2Nat.inj_add,lpow_add,Str_app_assoc. exact I.
  - intros _. eapply halts_evstep; [apply C|apply passW].
Qed.

Definition round x := estep (bstep x).
Definition run (n:N) := N_iter_until round (inl (St 0 [] [] TL TL)) n.
Lemma run_spec n : match run n with inl _ => True | inr b => b = true -> halts tm c0 end.
Proof.
  unfold run.
  pose proof (N_iter_until_spec (f:=round) (x:=inl (St 0 [] [] TL TL)) (T:=n)
    (fun x => tries_ok x /\ c0 -->* conf x) (fun b => b = true -> halts tm c0)) as H.
  destruct (N_iter_until round _ n) as [z|bz]; [trivial|]. apply H.
  - intros x [Hi Hc]. pose proof (bstep_spec x Hi) as [Hi' Hc']. unfold round.
    pose proof (estep_spec (bstep x)) as E. destruct (estep (bstep x)) as [y|b].
    + destruct E as [E1 E2].
      split; [apply E1,Hi'|eapply evstep_trans; [exact Hc|eapply evstep_trans; eauto]].
    + intros Hb. eapply halts_evstep; [apply E,Hb|eapply evstep_trans; eauto].
  - split; [split; apply tinv_TL|exact init].
Qed.

Lemma check : run 4000 = inr true.
Proof. native_check_eq. Qed.

Theorem halt : halts tm c0.
Proof. pose proof (run_spec 4000) as H. rewrite check in H. apply H; reflexivity. Qed.
End TM1.

Print Assumptions TM1.halt.
