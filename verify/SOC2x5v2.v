(* BB(2,5): five nonhalting counter machines, consolidated 2026-11-01.
   Each concrete machine keeps its own module; no development-file imports. *)

(* Machine 28. *)
From BusyCoq Require Import Individual25.
From Coq Require Import String List NArith ZArith Lia QArith Lqa Arith.Wf_nat.
Import ListNotations.
Close Scope Q_scope.
Open Scope sym_scope.

(* Source: the two-epoch argument in the local Lean package 10. This port
   uses BusyCoq configurations directly; no copied machine semantics. *)
Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB3LA3LA0RB2LB_2LA4LA4RA2RA---").
Notation "c -->* d" := (c -[tm]->* d) (at level 40).
Notation "c -->+ d" := (c -[tm]->+ d) (at level 40).

Inductive tok := F | C | P.
Definition tc t : list Sym := match t with F=>[2;0] | C=>[2;1] | P=>[4;0] end.
Definition left w := flat_map tc w *> [2;1] *> 0inf.
Definition lt w (r:side) := left w <{{A}} r.
Definition gt w (r:side) := left w {{A}}> r.
Ltac token_run := unfold lt,gt,left; cbn[flat_map tc]; execute.

Lemma left_P w r : lt (P::w) r -->+ lt w ([2;2]*>r).
Proof. token_run. Qed.
Lemma left_F w r : lt (F::w) r -->+ gt (C::w) r.
Proof. token_run. Qed.
Lemma left_C_token w r : lt (C::w) r -->+ lt w ([3;3]*>r).
Proof. token_run. Qed.
Lemma left_nil r : lt [] r -->+ gt [] (3>>r).
Proof. token_run. Qed.
Lemma right_33 w r : gt w ([3;3]*>r) -->+ gt (F::w) r.
Proof. token_run. Qed.
Lemma right_32 w r : gt w ([3;2]*>r) -->+ gt (P::w) r.
Proof. token_run. Qed.
Lemma right_2 w r : gt w (2>>r) -->+ lt w (3>>r).
Proof. token_run. Qed.
Lemma right_nil w : gt w 0inf -->+ lt w ([3;2]*>0inf).
Proof. token_run. Qed.
Lemma right_3 w : gt w (3>>0inf) -->+ lt w ([4;2;3;2]*>0inf).
Proof. token_run. Qed.
Lemma right_F4 w r : gt (F::w) (4>>r) -->+ lt w ([2;2;3]*>r).
Proof. token_run. Qed.

(* d counts short structural material blocks, while capacities use binary N. *)
Fixpoint carry (d:nat) (w:list tok) {struct w} : option (list tok) :=
  match w with
  | []=>None
  | P::w=>option_map (cons P) (carry (S d) w)
  | C::w=>match d with O=>option_map (cons F) (carry O w)
                      | S d=>option_map (cons C) (carry d w) end
  | F::w=>match d with O=>Some(C::w)
                      | S d=>option_map (cons F) (carry d w) end end.
Definition obind {X Y} (v:option X) (f:X->option Y) :=
  match v with None=>None | Some x=>f x end.
Lemma carry_length w : forall d v, carry d w=Some v -> length v=length w.
Proof.
  induction w as [|t w IH]; intros d v H; [discriminate|].
  destruct t,d; cbn[carry] in H;
    try (destruct (carry _ w) as [u|] eqn:E; [|discriminate]);
    inversion H; subst; cbn; eauto.
Qed.
Lemma carry_double w : forall d, carry (S d) w=obind (carry d w) (carry d).
Proof.
  induction w as [|t w IH]; intro d; [reflexivity|].
  destruct t.
  - destruct d; [reflexivity|]. cbn[carry]. rewrite(IH d).
    destruct(carry d w) as [u|]; cbn[obind option_map carry];
      [destruct(carry d u)|]; reflexivity.
  - destruct d.
    + cbn[carry]. destruct(carry O w); reflexivity.
    + cbn[carry]. rewrite(IH d).
      destruct(carry d w) as [u|]; cbn[obind option_map carry];
        [destruct(carry d u)|]; reflexivity.
  - cbn[carry]. rewrite(IH (S d)).
    destruct(carry (S d) w) as [u|]; cbn[obind option_map carry];
      [destruct(carry (S d) u)|]; reflexivity.
Qed.

(* A successful unit carry is a real left excursion. The P case invokes
   the strictly shorter word twice, using the proved carry-doubling law. *)
Lemma carry_run w : forall v, carry O w=Some v -> forall r, lt w r -->+ gt v r.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length tok))).
  destruct w as [|t w]; [intros; discriminate|].
  intros v E r. destruct t.
  - cbn[carry] in E; inversion E; subst; apply left_F.
  - cbn[carry] in E; destruct(carry O w) as [u|] eqn:EU; [|discriminate].
    inversion E; subst. eapply progress_trans; [apply left_C_token|].
    eapply progress_trans; [|apply right_33].
    apply IH; [unfold ltof; cbn; lia|exact EU].
  - cbn[carry] in E; rewrite(carry_double w O) in E.
    destruct(carry O w) as [u|] eqn:EU; cbn[obind] in E; [|discriminate].
    destruct(carry O u) as [v'|] eqn:EV; [|discriminate].
    inversion E; subst. pose proof(carry_length w O u EU) as HL.
    eapply progress_trans; [apply left_P|].
    eapply progress_trans; [apply IH; [unfold ltof; cbn; lia|exact EU]|].
    eapply progress_trans; [apply right_2|].
    eapply progress_trans; [|apply right_32].
    apply IH; [unfold ltof; cbn; lia|exact EV].
Qed.
Lemma cascade_pass w v : carry O w=Some v ->
  lt w ([3;2]*>0inf) -->+ lt (P::v) ([3;2]*>0inf).
Proof.
  intro H; eapply progress_trans; [apply carry_run; exact H|].
  eapply progress_trans; [apply right_32|apply right_nil].
Qed.
Lemma material_carry_run w v : carry (S O) w=Some v -> forall r,
  lt w ([2;2]*>r) -->+ gt (P::v) r.
Proof.
  rewrite carry_double; unfold obind.
  destruct(carry O w) as [u|] eqn:EU; [|discriminate].
  intros EV r. eapply progress_trans; [apply carry_run; exact EU|].
  eapply progress_trans; [apply right_2|].
  eapply progress_trans; [apply carry_run; exact EV|apply right_32].
Qed.

Open Scope N_scope.
Fixpoint cap w : N := match w with
| []=>0 | F::w=>2*cap w+1 | C::w=>2*cap w | P::w=>cap w/2 end.
Fixpoint pow2 (n:nat) : N := match n with O=>1 | S n=>2*pow2 n end.
Lemma pow2_pos n : 0<pow2 n.
Proof. induction n; cbn[pow2]; lia. Qed.
Ltac div2 :=
  repeat match goal with
  | |- context [?x / 2] =>
    let E:=fresh "Ediv" in let R:=fresh "Rdiv" in
    let q:=fresh "quo" in let r:=fresh "rem" in
    assert(E:x=2*(x/2)+x mod 2) by (apply N.div_mod; discriminate);
    assert(R:x mod 2<2) by (apply N.mod_lt; discriminate);
    set(q:=x/2) in *; set(r:=x mod 2) in *; clearbody q r
  | H:context [?x / 2] |- _ =>
    let E:=fresh "Ediv" in let R:=fresh "Rdiv" in
    let q:=fresh "quo" in let r:=fresh "rem" in
    assert(E:x=2*(x/2)+x mod 2) by (apply N.div_mod; discriminate);
    assert(R:x mod 2<2) by (apply N.mod_lt; discriminate);
    set(q:=x/2) in *; set(r:=x mod 2) in *; clearbody q r
  end; nia.
Lemma carry_capacity w : forall d,
  match carry d w with
  | None=>cap w<pow2 d
  | Some v=>cap w=cap v+pow2 d end.
Proof.
  induction w as [|t w IH]; intro d.
  - cbn[carry cap]; apply pow2_pos.
  - destruct t.
    + destruct d; [cbn[carry cap pow2]; lia|].
      specialize(IH d); cbn[carry cap pow2].
      destruct(carry d w) as [v|]; cbn[option_map cap] in *; lia.
    + destruct d.
      * specialize(IH O); cbn[carry cap pow2].
        destruct(carry O w) as [v|]; cbn[option_map cap pow2] in *; lia.
      * specialize(IH d); cbn[carry cap pow2].
        destruct(carry d w) as [v|]; cbn[option_map cap] in *; lia.
    + specialize(IH (S d)); cbn[carry cap pow2].
      destruct(carry (S d) w) as [v|]; cbn[option_map cap pow2] in *; div2.
Qed.
Lemma carry_exists w d : pow2 d<=cap w -> exists v, carry d w=Some v.
Proof.
  pose proof(carry_capacity w d) as H; destruct(carry d w) as [v|].
  - intro; eauto.
  - cbn in H; lia.
Qed.

Inductive chunk := M | Sg | Bk.
Definition cc b : list Sym := match b with
| M=>[S3;S3] | Sg=>[S3;S2] | Bk=>[S2;S2] end.
Definition cells := flat_map cc.
Fixpoint decor w := match w with
| []=>[] | F::w | C::w=>decor w++[M]
| P::w=>decor w++[if N.odd(cap w) then Sg else Bk] end.
Lemma cells_app u v : cells(u++v)=cells u++cells v.
Proof. apply flat_map_app. Qed.
Lemma carry_decor w : forall d v, carry d w=Some v -> decor v=decor w.
Proof.
  induction w as [|t w IH]; intros d v E; [discriminate|].
  destruct t.
  - destruct d; cbn[carry] in E.
    + inversion E; reflexivity.
    + destruct(carry d w) as [u|] eqn:EU; [|discriminate].
      inversion E; subst; cbn[decor]; rewrite(IH d u EU); reflexivity.
  - destruct d; cbn[carry] in E;
      destruct(carry _ w) as [u|] eqn:EU; [|discriminate| |discriminate];
      inversion E; subst; cbn[decor]; f_equal; eapply IH; exact EU.
  - cbn[carry] in E; destruct(carry (S d) w) as [u|] eqn:EU; [|discriminate].
    inversion E; subst; cbn[decor]; rewrite(IH (S d) u EU).
    pose proof(carry_capacity w (S d)) as HC; rewrite EU in HC; cbn[pow2] in HC.
    rewrite HC,N.odd_add,N.odd_mul; cbn; rewrite Bool.xorb_false_r; reflexivity.
Qed.

Lemma tail_run w : 3<=cap w -> exists v,
  cap v=cap w-3 /\ decor v=decor w /\
  lt (C::w) ([S4;S2;S3;S2]*>0inf) -->+
    lt (P::P::P::v) ([S3;S2]*>0inf).
Proof.
  intro HC. destruct(carry_exists w O ltac:(cbn[pow2]; lia)) as [u EU].
  pose proof(carry_capacity w O) as HU; rewrite EU in HU; cbn[pow2] in HU.
  destruct(carry_exists u (S O) ltac:(cbn[pow2]; lia)) as [v EV].
  pose proof(carry_capacity u (S O)) as HV; rewrite EV in HV; cbn[pow2] in HV.
  exists v; split; [lia|]; split.
  - rewrite (carry_decor u (S O) v EV); apply carry_decor with(d:=O); exact EU.
  - eapply progress_trans; [apply left_C_token|].
    eapply progress_trans; [apply carry_run; exact EU|].
    eapply progress_trans; [apply right_33|].
    eapply progress_trans; [apply right_F4|].
    eapply progress_trans; [apply material_carry_run; exact EV|].
    eapply progress_trans; [apply right_32|].
    eapply progress_trans; [apply right_32|apply right_nil].
Qed.

(* At capacity zero the decoration is exactly the material spilled by the
   real machine. No fuel-based spill evaluator or copied certificate is used. *)
Lemma overflow_run w : cap w=0 -> forall r,
  lt w r -->+ gt [] (S3 >> cells(decor w)*>r).
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length tok))).
  destruct w as [|t w].
  - intros _ r; apply left_nil.
  - intro HC; destruct t; intro r.
    + cbn[cap] in HC; lia.
    + assert(HW:cap w=0) by (cbn[cap] in HC; lia).
      cbn[decor]; rewrite cells_app; cbn[cells flat_map cc]; simpl_tape.
      eapply progress_trans; [apply left_C_token|].
      apply IH; [unfold ltof; cbn; lia|exact HW].
    + assert(HW:cap w=0 \/ cap w=1) by (cbn[cap] in HC; div2).
      destruct HW as [HW|HW].
      * cbn[decor]; rewrite HW; cbn[N.odd].
        rewrite cells_app; cbn[cells flat_map cc]; simpl_tape.
        eapply progress_trans; [apply left_P|].
        apply IH; [unfold ltof; cbn; lia|exact HW].
      * destruct(carry_exists w O ltac:(cbn[pow2]; lia)) as [u EU].
        pose proof(carry_capacity w O) as HU; rewrite EU in HU; cbn[pow2] in HU.
        pose proof(carry_length w O u EU) as HL.
        cbn[decor]; rewrite HW; cbn[N.odd].
        rewrite cells_app; cbn[cells flat_map cc]; simpl_tape.
        rewrite <- (carry_decor w O u EU).
        eapply progress_trans; [apply left_P|].
        eapply progress_trans; [apply carry_run; exact EU|].
        eapply progress_trans; [apply right_2|].
        apply IH; [unfold ltof; cbn; lia|lia].
Qed.
Definition stepT b (r:N) := match b with M=>2*r+1 | Sg=>2*r | Bk=>r/2-1 end.
Definition stepC b (r:N) := match b with
| Bk=>if r/2=?0 then None else Some(r/2-1)
| _=>Some(stepT b r) end.
Fixpoint foldT r w := match w with []=>r | b::w=>foldT (stepT b r) w end.
Fixpoint foldC r w := match w with []=>Some r | b::w=>
  match stepC b r with None=>None | Some r'=>foldC r' w end end.
Definition label b r := match b with Bk=>if N.odd r then Sg else Bk | _=>M end.
Definition conversion b r : N := match b with Bk=>if N.odd r then 1 else 0 | _=>0 end.
Fixpoint emitW r w := match w with
| []=>[] | b::w=>label b r::emitW (stepT b r) w end.
Fixpoint conv r w := match w with
| []=>0 | b::w=>conversion b r+conv (stepT b r) w end.
Lemma foldT_app u v r : foldT r (u++v)=foldT (foldT r u) v.
Proof. revert r; induction u; cbn; auto. Qed.
Lemma emitW_app u v r : emitW r (u++v)=emitW r u++emitW (foldT r u) v.
Proof. revert r; induction u; cbn; intro; [reflexivity|now rewrite IHu]. Qed.
Lemma conv_app u v r : conv r (u++v)=conv r u+conv (foldT r u) v.
Proof. revert r; induction u; cbn; intro; [reflexivity|rewrite IHu; lia]. Qed.
Lemma foldC_total w : forall r v, foldC r w=Some v -> foldT r w=v.
Proof.
  induction w as [|b w IH]; cbn[foldC foldT]; intros r v H.
  - now inversion H.
  - destruct b; cbn[stepC] in H; try (apply IH; exact H).
    destruct(r/2=?0); [discriminate|]; apply IH; exact H.
Qed.

Lemma rebuild_S w r : gt w (S3>>S3>>S2>>r) -->+ gt (C::w) (S3>>r).
Proof. token_run. Qed.
Lemma rebuild cs : forall w v r, foldC (cap w) cs=Some v ->
  exists u, cap u=v /\ decor u=decor w++emitW (cap w) cs /\
    gt w (S3>>cells cs*>r) -->* gt u (S3>>r).
Proof.
  induction cs as [|b cs IH]; intros w v r H.
  - cbn[foldC] in H; inversion H; subst. exists w.
    repeat split; try reflexivity; [rewrite app_nil_r; reflexivity|apply evstep_refl].
  - destruct b; cbn[foldC stepC stepT] in H.
    + destruct(IH (F::w) v r H) as [u [HC [HD HR]]]. exists u.
      split; [exact HC|]; split.
      * rewrite HD; cbn[decor cap emitW label stepT]; rewrite <-app_assoc; reflexivity.
      * change (gt w (S3>>S3>>S3>>cells cs*>r) -->* gt u (S3>>r)).
        apply progress_evstep; eapply progress_evstep_trans; [apply right_33|exact HR].
    + destruct(IH (C::w) v r H) as [u [HC [HD HR]]]. exists u.
      split; [exact HC|]; split.
      * rewrite HD; cbn[decor cap emitW label stepT]; rewrite <-app_assoc; reflexivity.
      * change (gt w (S3>>S3>>S2>>cells cs*>r) -->* gt u (S3>>r)).
        apply progress_evstep; eapply progress_evstep_trans; [apply rebuild_S|exact HR].
    + destruct(cap w/2=?0) eqn:EQ; [discriminate|].
      apply N.eqb_neq in EQ.
      destruct(carry_exists (P::w) O ltac:(cbn[pow2 cap]; lia)) as [u0 EU].
      pose proof(carry_capacity (P::w) O) as HU; rewrite EU in HU; cbn[pow2 cap] in HU.
      assert(HC0:cap u0=cap w/2-1) by lia.
      assert(HD0:decor u0=decor(P::w)) by (apply carry_decor with(d:=O); exact EU).
      destruct(IH u0 v r ltac:(rewrite HC0; exact H)) as [u [HC [HD HR]]].
      exists u; split; [exact HC|]; split.
      * rewrite HD,HD0,HC0; cbn[decor emitW label stepT]; rewrite <-app_assoc; reflexivity.
      * change (gt w (S3>>S2>>S2>>cells cs*>r) -->* gt u (S3>>r)).
        apply progress_evstep; eapply progress_trans; [apply right_32|].
        eapply progress_trans; [apply right_2|].
        eapply progress_evstep_trans; [apply carry_run; exact EU|exact HR].
Qed.

Lemma overflow_rebuild w v : cap w=0 -> foldC 0 (decor w)=Some v ->
  exists u, cap u=v /\ decor u=emitW 0 (decor w) /\
    lt w ([S3;S2]*>0inf) -->+ lt (C::u) ([S4;S2;S3;S2]*>0inf).
Proof.
  intros HC HF.
  destruct(rebuild (decor w) [] v ([S3;S2]*>0inf) HF) as [u [HU [HD HR]]].
  exists u; split; [exact HU|]; split; [exact HD|].
  eapply progress_trans; [apply overflow_run; exact HC|].
  eapply evstep_progress_trans; [exact HR|].
  eapply progress_trans; [apply rebuild_S|apply right_3].
Qed.

(* Compact generated entry, rather than an expanded long trajectory. *)
Definition seed5 := repeat P 6 ++ [F;P] ++ repeat C 3 ++ repeat P 3 ++
  repeat C 3 ++ repeat F 3 ++ [C].
Lemma initial_overflow : c0 -->* lt seed5 ([S3;S2]*>0inf).
Proof. apply evstep_c_spec; exists 4011%nat; vm_compute; reflexivity. Qed.
Lemma seed5_zero : cap seed5=0.
Proof. vm_compute; reflexivity. Qed.

Fixpoint bits (n:nat) (v:N) : list chunk := match n with
| O=>[] | S n=>(if N.odd v then Sg else Bk)::bits n (v/2) end.
Fixpoint halves (n:nat) (v:N) : N := match n with O=>v | S n=>halves n (v/2) end.
Lemma push_P n w :
  cap(repeat P n++w)=halves n(cap w) /\
  decor(repeat P n++w)=decor w++bits n(cap w).
Proof.
  revert w; induction n as [|n IH]; intro w; [cbn; now rewrite app_nil_r|].
  replace(repeat P(S n)++w) with (repeat P n++P::w).
  2:{ cbn[repeat]; rewrite repeat_cons; rewrite <-app_assoc; reflexivity. }
  destruct(IH(P::w)) as [HC HD]. split; [exact HC|].
  rewrite HD; cbn[decor cap bits]; rewrite <-app_assoc; reflexivity.
Qed.
Lemma overflow_tail w v : cap w=0 -> foldC 0(decor w)=Some v -> 3<=v ->
  exists u, cap u=halves 3(v-3) /\
    decor u=emitW 0(decor w)++bits 3(v-3) /\
    lt w ([S3;S2]*>0inf) -->+ lt u ([S3;S2]*>0inf).
Proof.
  intros HC HF HV.
  destruct(overflow_rebuild w v HC HF) as [u [HU [HD HR]]].
  destruct(tail_run u ltac:(lia)) as [z [HZ [DZ RZ]]].
  destruct(push_P 3 z) as [HP DP]. exists(P::P::P::z).
  split; [cbn[repeat app] in HP; rewrite HP,HZ,HU; reflexivity|].
  split; [cbn[repeat app] in DP; rewrite DP,DZ,HD,HZ,HU; reflexivity|].
  eapply progress_trans; eassumption.
Qed.

(* The finite number of ordinary passes is bounded by a binary-capacity
   bit length. This sound drain does not inspect individual TM steps. *)
Fixpoint drainbits (fuel:nat) (v:N) := match fuel with
| O=>[] | S n=>if v=?0 then [] else
  (if N.odd(v-1) then Sg else Bk)::drainbits n ((v-1)/2) end.
Lemma drain_run n : forall w, cap w<pow2 n -> exists u,
  cap u=0 /\ decor u=decor w++drainbits n(cap w) /\
    lt w ([S3;S2]*>0inf) -->* lt u ([S3;S2]*>0inf).
Proof.
  induction n as [|n IH]; intros w HC.
  - cbn[pow2] in HC; exists w. repeat split; try lia.
    + cbn[drainbits]; now rewrite app_nil_r.
    + apply evstep_refl.
  - destruct(cap w=?0) eqn:E.
    + apply N.eqb_eq in E; exists w; repeat split; try exact E.
      * cbn[drainbits]; rewrite E; cbn; now rewrite app_nil_r.
      * apply evstep_refl.
    + apply N.eqb_neq in E.
      destruct(carry_exists w O ltac:(cbn[pow2]; lia)) as [v EV].
      pose proof(carry_capacity w O) as HV; rewrite EV in HV; cbn[pow2] in HV.
      assert(HP:cap(P::v)<pow2 n) by (cbn[cap pow2] in *; div2).
      destruct(IH(P::v) HP) as [u [HU [HD HR]]].
      exists u; split; [exact HU|]; split.
      * rewrite HD; cbn[drainbits decor cap].
        assert(EN:(cap w=?0)=false) by (apply N.eqb_neq; exact E).
        rewrite EN,(carry_decor w O v EV).
        replace(cap w-1) with (cap v) by lia.
        rewrite <-app_assoc; reflexivity.
      * apply progress_evstep; eapply progress_evstep_trans; [apply cascade_pass; exact EV|exact HR].
Qed.
Definition epoch w :=
  let v:=foldT 0 w+5 in emitW 0 w++bits (N.to_nat(N.log2 v)) v.
Fixpoint epochs (n:nat) w := match n with O=>w | S n=>epochs n (epoch w) end.
Fixpoint ok_epochs (n:nat) w := match n with
| O=>true | S n=>match foldC 0 w with
  | None=>false | Some v=> (3<=?v) && ok_epochs n (epoch w) end end.
Definition base12 := epochs 7 (decor seed5).
Lemma ok_to_12 : ok_epochs 7 (decor seed5)=true.
Proof. vm_compute; reflexivity. Qed.

(* The exact price at height zero. Normalizing the starting height removes
   all integer powers from the two-emission contraction argument. *)
Open Scope Q_scope.
Fixpoint rho w : QArith_base.Q := match w with
| []=>0 | M::w=>rho w/2 | Sg::w=>(1+rho w)/2 | Bk::w=>2*(1+rho w) end.
Fixpoint scale w : QArith_base.Q := match w with
| []=>1 | M::w | Sg::w=>scale w/2 | Bk::w=>2*scale w end.
Definition Phi w := rho w+scale w.
Definition Good w := Phi w<=1/8192 /\
  (exists p, w=p++repeat Sg 12) /\ (8<=conv 0 w)%N.

Ltac qlin := unfold Qdiv,Qinv in *; cbn[Qnum Qden] in *; Lqa.lra.
Lemma rho_nonneg w : 0<=rho w.
Proof. induction w as [|b w IH]; [cbn[rho]; qlin|destruct b; cbn[rho]; qlin]. Qed.
Lemma scale_pos w : 0<scale w.
Proof. induction w as [|b w IH]; [cbn[scale]; qlin|destruct b; cbn[scale]; qlin]. Qed.

Definition nq (n:N) := inject_Z (Z.of_N n).
Lemma nq_add a b : nq(a+b)==nq a+nq b.
Proof. unfold nq; rewrite N2Z.inj_add,inject_Z_plus; reflexivity. Qed.
Lemma nq_mul a b : nq(a*b)==nq a*nq b.
Proof. unfold nq; rewrite N2Z.inj_mul,inject_Z_mult; reflexivity. Qed.
Lemma nq_le a b : (a<=b)%N -> nq a<=nq b.
Proof. unfold nq; rewrite <-Zle_Qle; lia. Qed.
Lemma nq_nonneg a : 0<=nq a.
Proof. change(nq 0<=nq a); apply nq_le; lia. Qed.

(* Price below available normalized capacity prevents failure. Both
   quantitative bounds are retained for the later terminal estimates. *)
Lemma safe_scan cs : forall r, rho cs<nq r+1 -> exists v,
  foldC r cs=Some v /\
  nq r+1-rho cs<=(nq v+1)*scale cs /\
  (nq v+1)*scale cs<=nq r+1.
Proof.
  induction cs as [|b cs IH]; intros r H.
  - exists r; cbn[foldC rho scale]; split; [reflexivity|split; qlin].
  - destruct b; cbn[rho] in H.
    + assert(HE:nq(2*r+1)==2*nq r+1).
      { rewrite nq_add,nq_mul; change(nq 2) with 2; change(nq 1) with 1; reflexivity. }
      destruct(IH (2*r+1)%N ltac:(rewrite HE; qlin)) as [v [HF [HL HU]]].
      exists v; split; [exact HF|]. cbn[rho scale]; rewrite HE in HL,HU; split; qlin.
    + assert(HE:nq(2*r)==2*nq r).
      { rewrite nq_mul; change(nq 2) with 2; reflexivity. }
      destruct(IH (2*r)%N ltac:(rewrite HE; qlin)) as [v [HF [HL HU]]].
      exists v; split; [exact HF|]. cbn[rho scale]; rewrite HE in HL,HU; split; qlin.
    + assert(HL:(2*(r/2)<=r)%N) by div2.
      assert(HU:(r<=2*(r/2)+1)%N) by div2.
      pose proof(nq_le _ _ HL) as QL; pose proof(nq_le _ _ HU) as QU.
      rewrite nq_add,nq_mul in QU; rewrite nq_mul in QL.
      change(nq 2) with 2 in QL,QU; change(nq 1) with 1 in QU.
      assert(HP:(1<=r/2)%N).
      { destruct((r/2)%N) eqn:E; [|lia].
        change(nq 0) with 0 in QL,QU; pose proof(rho_nonneg cs); exfalso; qlin. }
      assert(HE:nq(r/2-1)+1==nq(r/2)).
      { replace(r/2)%N with (r/2-1+1)%N at 2 by lia.
        rewrite nq_add; change(nq 1) with 1; reflexivity. }
      destruct(IH (r/2-1)%N ltac:(pose proof(rho_nonneg cs); qlin)) as [v [HF [HA HB]]].
      exists v; split.
      * cbn[foldC stepC]; assert(E:(r/2=?0)%N=false) by (apply N.eqb_neq; lia).
        rewrite E; exact HF.
      * cbn[rho scale]; split; qlin.
Qed.
Lemma good_scan cs : Good cs -> exists v, foldC 0%N cs=Some v /\ (8191<=v)%N.
Proof.
  intros [HP _]; unfold Phi in HP.
  pose proof(rho_nonneg cs) as HR; pose proof(scale_pos cs) as HS.
  destruct(safe_scan cs 0%N ltac:(change(nq 0) with 0; qlin)) as [v [HF [HL HU]]].
  exists v; split; [exact HF|].
  change(nq 0) with 0 in HL,HU.
  destruct(N.le_gt_cases 8191 v) as [HV|HV]; [exact HV|].
  assert(HV':(v<=8190)%N) by lia.
  pose proof(nq_le _ _ HV') as Hq; change(nq 8190) with 8190 in Hq.
  exfalso; unfold Qdiv,Qinv in *; cbn[Qnum Qden] in *; Lqa.nra.
Qed.
Lemma rho_emit_le w : forall r, rho (emitW r w)<=rho w.
Proof.
  induction w as [|b w IH]; intro r; [cbn[rho emitW]; qlin|].
  destruct b; cbn[emitW label rho].
  - specialize(IH (stepT M r)); qlin.
  - specialize(IH (stepT Sg r)); qlin.
  - specialize(IH (stepT Bk r)); destruct(N.odd r); cbn[rho];
      pose proof(rho_nonneg w); qlin.
Qed.
Lemma odd_marker r : N.odd (2*r+1)%N=true.
Proof. rewrite N.odd_add,N.odd_mul; cbn; reflexivity. Qed.
Lemma rho_emit_twice_le w r1 r2 : rho(emitW r2 (emitW r1 w))<=rho w.
Proof.
  pose proof(rho_emit_le (emitW r1 w) r2).
  pose proof(rho_emit_le w r1); qlin.
Qed.
Lemma rho_emit2_odd w : forall r1 r2, N.odd r2=true ->
  rho(emitW r2 (emitW r1 w))<=rho w/4.
Proof.
  induction w as [|b w IH]; intros r1 r2 HO; [cbn[rho emitW]; qlin|].
  destruct b.
  - cbn[emitW label rho].
    pose proof(IH (stepT M r1) (stepT M r2) (odd_marker r2)); qlin.
  - cbn[emitW label rho].
    pose proof(IH (stepT Sg r1) (stepT M r2) (odd_marker r2)); qlin.
  - cbn[emitW label]; destruct(N.odd r1) eqn:E; cbn[emitW label rho].
    + pose proof(rho_emit_twice_le w (stepT Bk r1) (stepT Sg r2)); qlin.
    + rewrite HO; cbn[rho].
      pose proof(rho_emit_twice_le w (stepT Bk r1) (stepT Bk r2)); qlin.
Qed.
Lemma rho_emit2_top w : foldC 0%N w<>None ->
  rho(emitW 0%N (emitW 0%N w))<=rho w/4.
Proof.
  destruct w as [|b w]; [cbn[emitW rho]; intros; qlin|].
  destruct b; intro H.
  - change (rho(emitW 1%N (emitW 1%N w))/2<=(rho w/2)/4).
    pose proof(rho_emit2_odd w 1%N 1%N eq_refl); qlin.
  - change (rho(emitW 1%N (emitW 0%N w))/2<=((1+rho w)/2)/4).
    pose proof(rho_emit2_odd w 0%N 1%N eq_refl); qlin.
  - exfalso; apply H; reflexivity.
Qed.
Lemma rho_app u v : rho(u++v)==rho u+scale u*rho v.
Proof.
  induction u as [|b u IH]; [cbn[app rho scale]; ring|].
  destruct b; cbn[app rho scale]; rewrite IH; unfold Qdiv; ring.
Qed.
Lemma scale_app u v : scale(u++v)==scale u*scale v.
Proof.
  induction u as [|b u IH]; [cbn[app scale]; ring|].
  destruct b; cbn[app scale]; rewrite IH; unfold Qdiv; ring.
Qed.
Lemma Phi_app u v : Phi(u++v)==rho u+scale u*Phi v.
Proof. unfold Phi; rewrite rho_app,scale_app; ring. Qed.

Definition chunk_eq_dec : forall a b:chunk, {a=b}+{a<>b}.
Proof. decide equality. Defined.
Definition goodb w := Qle_bool (Phi w) (1/8192) &&
  (if list_eq_dec chunk_eq_dec w
       (firstn (length w-12) w++repeat Sg 12) then true else false) &&
  N.leb 8 (conv 0%N w).
Lemma goodb_spec w : goodb w=true -> Good w.
Proof.
  unfold goodb,Good. rewrite !Bool.andb_true_iff,Qle_bool_iff,N.leb_le.
  destruct(list_eq_dec chunk_eq_dec w (firstn (length w-12) w++repeat Sg 12));
    intros [[HP HS] HC]; [repeat split; eauto|discriminate].
Qed.
Lemma base_good : Good base12 /\ Good(epoch base12).
Proof. split; apply goodb_spec; vm_compute; reflexivity. Qed.


(* Exact epoch semantics and the finite entrance. *)
Close Scope Q_scope.
Open Scope N_scope.
Lemma pow2_N n : pow2 n=2^(N.of_nat n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn[pow2]; rewrite IH,Nat2N.inj_succ,N.pow_succ_r by lia; reflexivity.
Qed.
Definition drainfuel r := N.to_nat(N.size r).
Lemma drainfuel_bound r : r<pow2(drainfuel r).
Proof. unfold drainfuel; rewrite pow2_N,N2Nat.id; apply N.size_gt. Qed.

Lemma log2_half x : 2<=x -> N.log2 x=N.succ(N.log2(x/2)).
Proof.
  intro HX.
  assert(E:x=2*(x/2)+x mod 2) by (apply N.div_mod; discriminate).
  assert(HR:x mod 2<2) by (apply N.mod_lt; discriminate).
  assert(HP:0<x/2) by div2.
  assert(HR':x mod 2=0 \/ x mod 2=1) by lia.
  destruct HR' as [HR'|HR']; rewrite E at 1; rewrite HR'.
  - rewrite N.add_0_r,N.log2_double by exact HP; reflexivity.
  - rewrite N.log2_succ_double by exact HP; reflexivity.
Qed.
Definition bitlength x := N.to_nat(N.log2 x).
Lemma bitlength_half x : 2<=x -> bitlength x=S(bitlength(x/2)).
Proof. intro H; unfold bitlength; rewrite log2_half,N2Nat.inj_succ by exact H; reflexivity. Qed.

Lemma drainbits_spec n : forall r, r<pow2 n ->
  drainbits n r=bits(bitlength(r+1))(r+1).
Proof.
  induction n as [|n IH]; intros r HB.
  - cbn[pow2] in HB; assert(r=0) by lia; subst; reflexivity.
  - destruct(r=?0) eqn:E.
    + apply N.eqb_eq in E; subst; reflexivity.
    + assert(HR:0<r) by (apply N.eqb_neq in E; lia).
      assert(HQ:(r-1)/2<pow2 n) by (cbn[pow2] in HB; div2).
      assert(HD:(r-1)/2+1=(r+1)/2) by div2.
      assert(HO:N.odd(r-1)=N.odd(r+1)).
      { rewrite N.odd_sub,N.odd_add by lia; reflexivity. }
      cbn[drainbits]; rewrite E,IH by exact HQ.
      rewrite (bitlength_half (r+1) ltac:(lia)); cbn[bits].
      rewrite HO,HD; reflexivity.
Qed.

Lemma bits_app n m x : bits(n+m) x=bits n x++bits m(halves n x).
Proof.
  revert x; induction n as [|n IH]; intro x; [reflexivity|].
  cbn[bits halves Nat.add]; rewrite IH; reflexivity.
Qed.
Lemma halves3_add8 x : halves 3(x+8)=halves 3 x+1.
Proof. cbn[halves]; div2. Qed.
Lemma bits3_add8 x : bits 3(x+8)=bits 3 x.
Proof.
  assert(H1:(x+8)/2=x/2+4) by div2.
  assert(H2:(x+8)/2/2=x/2/2+2) by div2.
  cbn[bits]; rewrite H2,H1.
  rewrite !N.odd_add; cbn[N.odd]; rewrite !Bool.xorb_false_r; reflexivity.
Qed.
Lemma bitlength_add8 x : bitlength(x+8)=(3+bitlength(halves 3 x+1))%nat.
Proof.
  assert(H0:2<=x+8) by lia.
  assert(H1:2<=(x+8)/2) by div2.
  assert(H2:2<=(x+8)/2/2) by div2.
  rewrite (bitlength_half _ H0),(bitlength_half _ H1),(bitlength_half _ H2).
  change (S(S(S(bitlength(halves 3(x+8)))))=(3+bitlength(halves 3 x+1))%nat).
  rewrite halves3_add8; reflexivity.
Qed.

Lemma epoch_suffix v n : 3<=v -> halves 3(v-3)<pow2 n ->
  bits 3(v-3)++drainbits n(halves 3(v-3))=
    bits(bitlength(v+5))(v+5).
Proof.
  intros HV HN; rewrite drainbits_spec by exact HN.
  replace(v+5) with (v-3+8) by lia.
  rewrite bitlength_add8,bits_app,bits3_add8,halves3_add8; reflexivity.
Qed.

Lemma epoch_run w v : cap w=0 -> foldC 0(decor w)=Some v -> 3<=v ->
  exists u, cap u=0 /\ decor u=epoch(decor w) /\
    lt w ([S3;S2]*>0inf) -->+ lt u ([S3;S2]*>0inf).
Proof.
  intros HC HF HV.
  destruct(overflow_tail w v HC HF HV) as [z [HZ [DZ RZ]]].
  destruct(drain_run (drainfuel(cap z)) z (drainfuel_bound(cap z))) as [u [HU [DU RU]]].
  exists u; split; [exact HU|]; split.
  - rewrite DU,DZ,<-app_assoc,HZ.
    rewrite epoch_suffix by (try exact HV; rewrite <-HZ; apply drainfuel_bound).
    unfold epoch,bitlength; rewrite(foldC_total _ _ _ HF); reflexivity.
  - eapply progress_evstep_trans; eassumption.
Qed.

Lemma ok_epochs_sound n : forall w, cap w=0 -> ok_epochs n(decor w)=true ->
  exists u, cap u=0 /\ decor u=epochs n(decor w) /\
    lt w ([S3;S2]*>0inf) -->* lt u ([S3;S2]*>0inf).
Proof.
  induction n as [|n IH]; intros w HC HO.
  - exists w; split; [exact HC|]; split; [reflexivity|apply evstep_refl].
  - cbn[ok_epochs] in HO.
    destruct(foldC 0(decor w)) as [v|] eqn:HF; [|discriminate].
    apply Bool.andb_true_iff in HO; destruct HO as [HV HO]; apply N.leb_le in HV.
    destruct(epoch_run w v HC HF HV) as [z [HZ [DZ RZ]]].
    destruct(IH z HZ ltac:(rewrite DZ; exact HO)) as [u [HU [DU RU]]].
    exists u; split; [exact HU|]; split.
    + cbn[epochs]; rewrite DU,DZ; reflexivity.
    + apply progress_evstep; eapply progress_evstep_trans; eassumption.
Qed.

Lemma initial_base12 : exists w, cap w=0 /\ decor w=base12 /\
  c0 -->* lt w ([S3;S2]*>0inf).
Proof.
  destruct(ok_epochs_sound 7 seed5 seed5_zero ok_to_12) as [w [HC [HD HR]]].
  exists w; split; [exact HC|]; split; [exact HD|].
  eapply evstep_trans; [apply initial_overflow|exact HR].
Qed.


(* Forced conversions from the prescribed suffix. *)
Lemma emitW_repeat_Sg n : forall r,
  emitW r (repeat Sg n) = repeat M n.
Proof.
  induction n as [|n IH]; intro r; [reflexivity|].
  cbn [repeat emitW label]; rewrite IH; reflexivity.
Qed.
Lemma foldT_repeat_M n : forall r,
  foldT r (repeat M n) + 1 = pow2 n * (r+1).
Proof.
  induction n as [|n IH]; intro r; [cbn [repeat foldT pow2]; nia|].
  cbn [repeat foldT stepT pow2]; rewrite IH; nia.
Qed.

(* A B at 2r+3 necessarily converts and leaves exactly r. Iterating this
   elementary predecessor eight times is enough; no modular conv_Bs theory. *)
Lemma conversion_forced r : conversion Bk (2*r+3) = 1.
Proof.
  unfold conversion; rewrite N.odd_add, N.odd_mul.
  reflexivity.
Qed.
Lemma stepT_forced r : stepT Bk (2*r+3) = r.
Proof. unfold stepT; div2. Qed.
Fixpoint forced_input n (r:N) : N :=
  match n with O => r | S n => 2*forced_input n r+3 end.
Lemma conv_forced_input n r :
  conv (forced_input n r) (repeat Bk n) = N.of_nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [forced_input repeat conv].
  rewrite conversion_forced, stepT_forced, IH, Nat2N.inj_succ; lia.
Qed.
Lemma conv_eight r : conv (4096*r+4093) (repeat Bk 8) = 8.
Proof.
  replace (4096*r+4093) with (forced_input 8 (16*r+13)) by
    (cbn [forced_input]; nia).
  apply conv_forced_input.
Qed.
Lemma fixed_prefix_value a : 2 <= a ->
  foldT a [Sg;Bk;Sg;Bk] = a-2.
Proof. intro H; cbn [foldT stepT]; div2. Qed.

Theorem conv_forced p q :
  8 <= conv 0 (emitW 0 (p ++ repeat Sg 12) ++
    ([Sg;Bk;Sg;Bk] ++ repeat Bk 8 ++ q)).
Proof.
  rewrite conv_app.
  set (r := foldT 0 (emitW 0 p)).
  assert (Ha : foldT 0 (emitW 0 (p ++ repeat Sg 12)) = 4096*r+4095).
  { rewrite emitW_app, emitW_repeat_Sg, foldT_app.
    pose proof (foldT_repeat_M 12 r) as H.
    change (foldT r (repeat M 12)+1=4096*(r+1)) in H.
    change (foldT r (repeat M 12)=4096*r+4095); lia. }
  rewrite Ha, conv_app, fixed_prefix_value by lia.
  replace (4096*r+4095-2) with (4096*r+4093) by lia.
  rewrite conv_app, conv_eight; lia.
Qed.

Corollary epoch_conversions c beta :
  (exists p, c = p ++ repeat Sg 12) ->
  (exists q, beta = [Sg;Bk;Sg;Bk] ++ repeat Bk 8 ++ q) ->
  8 <= conv 0 (emitW 0 c ++ beta).
Proof. intros [p ->] [q ->]; apply conv_forced. Qed.


Open Scope Q_scope.
(* Normalized price bounds: no separate integer-height/zpow framework. *)
Lemma scale_emit_exact w : forall r,
  scale (emitW r w) * nq (4 ^ conv r w) == scale w.
Proof.
  induction w as [|b w IH]; intro r.
  - cbn [emitW conv scale]; reflexivity.
  - destruct b; cbn [emitW label conv conversion].
    + rewrite N.add_0_l; cbn [scale]; specialize (IH (stepT M r)); qlin.
    + rewrite N.add_0_l; cbn [scale]; specialize (IH (stepT Sg r)); qlin.
    + destruct (N.odd r); cbn [scale].
      * rewrite N.pow_add_r, nq_mul; change (nq (4^1)) with 4.
        specialize (IH (stepT Bk r)); qlin.
      * rewrite N.add_0_l; specialize (IH (stepT Bk r)); qlin.
Qed.

Lemma scale_emit_le w r : scale (emitW r w) <= scale w.
Proof.
  pose proof (scale_pos (emitW r w)) as HP.
  pose proof (scale_emit_exact w r) as HE.
  assert (H1:(1 <= 4 ^ conv r w)%N).
  { assert (4 ^ conv r w <> 0)%N by (apply N.pow_nonzero; discriminate); lia. }
  pose proof (nq_le _ _ H1); change (nq 1) with 1 in *.
  Lqa.nra.
Qed.

Lemma scale_emit_small w r : (8 <= conv r w)%N ->
  65536 * scale (emitW r w) <= scale w.
Proof.
  intro HC.
  pose proof (scale_pos (emitW r w)) as HP.
  pose proof (scale_emit_exact w r) as HE.
  assert (H1:(65536 <= 4 ^ conv r w)%N).
  { change (4^8 <= 4^conv r w)%N; apply N.pow_le_mono_r; lia. }
  pose proof (nq_le _ _ H1); change (nq 65536) with 65536 in *.
  Lqa.nra.
Qed.

Lemma pow2_ge1 n : (1 <= pow2 n)%N.
Proof. pose proof (pow2_pos n); lia. Qed.

Lemma suffix_bound w : Phi w <= 3 * nq (pow2 (length w)) - 2.
Proof.
  induction w as [|b w IH].
  - change (1 <= 3*1-2); Lqa.lra.
  - pose proof (nq_le _ _ (pow2_ge1 (length w))) as HP.
    change (nq 1) with 1 in HP.
    cbn [length pow2]; rewrite nq_mul; change (nq 2) with 2.
    unfold Phi in *; destruct b; cbn [rho scale]; qlin.
Qed.

Lemma fresh_suffix_small w beta :
  scale w * nq (pow2 (length beta)) == 1/2 ->
  (8 <= conv 0%N w)%N ->
  scale (emitW 0%N w) * Phi beta <= 3/131072.
Proof.
  intros HE HC.
  pose proof (scale_emit_small w 0%N HC) as HS.
  pose proof (suffix_bound beta) as HB.
  pose proof (scale_pos (emitW 0%N w)) as HP.
  pose proof (nq_nonneg (pow2 (length beta))) as HQ.
  assert (HA: scale (emitW 0%N w) * Phi beta <=
    scale (emitW 0%N w) * (3*nq (pow2 (length beta)))).
  { Lqa.nra. }
  assert (HD: 65536*scale (emitW 0%N w)*nq (pow2 (length beta)) <=
    scale w*nq (pow2 (length beta))).
  { apply Qmult_le_compat_r; assumption. }
  rewrite HE in HD; qlin.
Qed.

(* Once the emitted suffix shape is known, these are the entire price
   obligations for two-epoch closure. *)
Lemma two_epoch_price w beta gamma :
  Good w -> Good (epoch w) ->
  epoch w = emitW 0%N w ++ beta ->
  epoch (epoch w) = emitW 0%N (epoch w) ++ gamma ->
  scale w * nq (pow2 (length beta)) == 1/2 ->
  scale (epoch w) * nq (pow2 (length gamma)) == 1/2 ->
  Phi (epoch (epoch w)) <= 1/8192.
Proof.
  intros HW HD EB EG SB SG.
  destruct (good_scan w HW) as [v [HF HV]].
  pose proof (rho_emit2_top w ltac:(rewrite HF; discriminate)) as HA.
  pose proof (fresh_suffix_small w beta SB (proj2 (proj2 HW))) as HB.
  pose proof (fresh_suffix_small (epoch w) gamma SG (proj2 (proj2 HD))) as HC.
  pose proof (scale_emit_le (emitW 0%N w) 0%N) as HS.
  pose proof (rho_emit_le beta (foldT 0%N (emitW 0%N w))) as HR.
  pose proof (scale_pos (emitW 0%N (emitW 0%N w))) as HP.
  pose proof (rho_nonneg beta) as HN.
  pose proof (scale_pos beta) as HT.
  assert (HB':scale (emitW 0%N (emitW 0%N w))*
    rho (emitW (foldT 0%N (emitW 0%N w)) beta) <= 3/131072).
  { eapply Qle_trans; [|exact HB].
    eapply Qle_trans with (y:=scale (emitW 0%N (emitW 0%N w))*rho beta).
    - rewrite (Qmult_comm _ (rho (emitW _ beta))), (Qmult_comm _ (rho beta)).
      apply Qmult_le_compat_r; [exact HR|Lqa.lra].
    - eapply Qle_trans; [apply Qmult_le_compat_r; [exact HS|exact HN]|].
      rewrite (Qmult_comm _ (rho beta)),(Qmult_comm _ (Phi beta)).
      apply Qmult_le_compat_r.
      + unfold Phi; Lqa.lra.
      + pose proof (scale_pos (emitW 0%N w)); Lqa.lra. }
  rewrite EG,Phi_app.
  assert (HE:rho (emitW 0%N (epoch w)) ==
    rho (emitW 0%N (emitW 0%N w)) +
    scale (emitW 0%N (emitW 0%N w))*
      rho (emitW (foldT 0%N (emitW 0%N w)) beta)).
  { rewrite EB,emitW_app,rho_app; reflexivity. }
  rewrite HE.
  destruct HW as [HW _]; unfold Phi in HW.
  pose proof (scale_pos w); qlin.
Qed.

(* Sharp terminal bounds and the shape of each newly added suffix. *)


Open Scope N_scope.
Lemma shape_pow2_add a b : pow2 (a+b)=pow2 a*pow2 b.
Proof. induction a; cbn [Nat.add pow2]; [lia|rewrite IHa; ring]. Qed.
Lemma shape_pow2_mono a b : (a<=b)%nat -> pow2 a<=pow2 b.
Proof. intro H; induction H; [lia|cbn [pow2]; lia]. Qed.
Lemma foldT_repeat_Sg n : forall r,
  foldT r (repeat Sg n)=pow2 n*r.
Proof.
  induction n; intro r; cbn [repeat foldT stepT pow2]; [lia|rewrite IHn; ring].
Qed.

Open Scope Q_scope.
Lemma shape_nq_pow2_succ n : nq (pow2 (S n))==2*nq (pow2 n).
Proof. cbn [pow2]. rewrite nq_mul. reflexivity. Qed.
Lemma shape_nq_le_inv a b : nq a<=nq b -> (a<=b)%N.
Proof. unfold nq. rewrite <-Zle_Qle. lia. Qed.
Lemma shape_nq_pow2_ge1 n : 1<=nq (pow2 n).
Proof. change (nq 1<=nq (pow2 n)). apply nq_le. pose proof (pow2_pos n); lia. Qed.

(* No integer-height or signed-power library is needed. Every scale is
   either an integral power of two or the reciprocal of such a power. *)
Lemma scale_dyadic c : exists e,
  scale c==nq (pow2 e) \/ scale c*nq (pow2 e)==1.
Proof.
  induction c as [|b c [e [HE|HE]]].
  - exists O. left. reflexivity.
  - destruct b.
    + destruct e as [|e].
      * exists 1%nat. right. cbn [scale]. change (nq (pow2 1)) with 2.
        change (nq (pow2 0)) with 1 in HE. qlin.
      * exists e. left. cbn [scale]. rewrite shape_nq_pow2_succ in HE. qlin.
    + destruct e as [|e].
      * exists 1%nat. right. cbn [scale]. change (nq (pow2 1)) with 2.
        change (nq (pow2 0)) with 1 in HE. qlin.
      * exists e. left. cbn [scale]. rewrite shape_nq_pow2_succ in HE. qlin.
    + exists (S e). left. cbn [scale]. rewrite shape_nq_pow2_succ. qlin.
  - destruct b.
    + exists (S e). right. cbn [scale]. rewrite shape_nq_pow2_succ. qlin.
    + exists (S e). right. cbn [scale]. rewrite shape_nq_pow2_succ. qlin.
    + destruct e as [|e].
      * exists 1%nat. left. cbn [scale]. change (nq (pow2 1)) with 2.
        change (nq (pow2 0)) with 1 in HE. qlin.
      * exists e. right. cbn [scale]. rewrite shape_nq_pow2_succ in HE. qlin.
Qed.

Lemma cheap_scale_exponent c : Phi c<=1/8192 ->
  exists e, (13<=e)%nat /\ scale c*nq (pow2 e)==1.
Proof.
  intro HP. pose proof (rho_nonneg c) as HR. pose proof (scale_pos c) as HS.
  unfold Phi in HP.
  destruct (scale_dyadic c) as [e [HE|HE]].
  - pose proof (shape_nq_pow2_ge1 e). exfalso. qlin.
  - exists e. split; [|exact HE].
    destruct (le_dec 13 e); [assumption|].
    pose proof (shape_pow2_mono e 12 ltac:(lia)) as HM.
    pose proof (nq_le _ _ HM) as HQ.
    change (nq (pow2 12)) with 4096 in HQ.
    exfalso. unfold Qdiv,Qinv in *; cbn [Qnum Qden] in *; Lqa.nra.
Qed.

(* The strong terminal bounds are retained as an optional arithmetic
   interface. The public epoch shape theorem below only exposes scale. *)
Lemma terminal_facts c : Phi c<=1/8192 ->
  (exists p, c=p++repeat Sg 12) ->
  exists e z, (13<=e)%nat /\ pow2 e=(8192*z)%N /\ (1<=z)%N /\
    scale c*nq (pow2 e)==1 /\
    foldC 0%N c=Some (foldT 0%N c) /\
    (foldT 0%N c mod 4096=0)%N /\
    (8191*z<=foldT 0%N c)%N /\ (foldT 0%N c+5<8192*z)%N.
Proof.
  intros HP HT.
  destruct (cheap_scale_exponent c HP) as [e [HE HS]].
  set (z:=pow2 (e-13)).
  assert (HZ : pow2 e=(8192*z)%N).
  { replace e with ((e-13)+13)%nat at 1 by lia.
    rewrite shape_pow2_add. unfold z. change (pow2 (e-13)*8192=8192*pow2 (e-13))%N. ring. }
  assert (HZ1 : (1<=z)%N) by (unfold z; pose proof (pow2_pos (e-13)); lia).
  pose proof (rho_nonneg c) as HR. pose proof (scale_pos c) as Hpos.
  assert (Hsmall : rho c<nq 0+1) by (change (nq 0) with 0; unfold Phi in HP; qlin).
  destruct (safe_scan c 0%N Hsmall) as [v [HF [HL HU]]].
  pose proof (foldC_total c 0%N v HF) as HV.
  change (nq 0) with 0 in HL,HU.
  assert (HSz : scale c*(8192*nq z)==1).
  { rewrite HZ,nq_mul in HS. exact HS. }
  assert (Hupq : nq v+1<=8192*nq z).
  { unfold Qdiv,Qinv in *; cbn [Qnum Qden] in *; Lqa.nra. }
  assert (Hloq : 8191*nq z<=nq v).
  { unfold Phi in HP. unfold Qdiv,Qinv in *; cbn [Qnum Qden] in *; Lqa.nra. }
  assert (Hup : (v+1<=8192*z)%N).
  { apply shape_nq_le_inv. rewrite nq_add,nq_mul. exact Hupq. }
  assert (Hlo : (8191*z<=v)%N).
  { apply shape_nq_le_inv. rewrite nq_mul. exact Hloq. }
  assert (Hdiv : (foldT 0%N c mod 4096=0)%N).
  { destruct HT as [p HT]. rewrite HT,foldT_app,foldT_repeat_Sg.
    change ((4096*foldT 0%N p) mod 4096=0)%N.
    rewrite N.mul_comm. apply N.mod_mul. discriminate. }
  exists e,z. repeat split; try assumption.
  - now rewrite HV.
  - now rewrite HV.
  - rewrite HV in Hdiv |- *. lia.
Qed.

Open Scope N_scope.
Lemma shape_bits_length n : forall v, length (bits n v)=n.
Proof. induction n; intro v; cbn [bits length]; [reflexivity|now rewrite IHn]. Qed.
Lemma shape_bits_split a : forall b v,
  bits (a+b) v=bits a v++bits b (v/pow2 a).
Proof.
  induction a as [|a IH]; intros b v.
  - cbn [Nat.add bits pow2]. now rewrite N.div_1_r.
  - cbn [Nat.add bits pow2]. rewrite IH. cbn [app]. f_equal. f_equal.
    rewrite N.div_div by (pose proof (pow2_pos a); lia). reflexivity.
Qed.
Lemma shape_odd_mod v : N.odd v=(v mod 2 =? 1).
Proof. rewrite <-N.bit0_odd,N.bit0_eqb. reflexivity. Qed.
Lemma shape_lowbit_arithmetic r q : r<2 ->
  (r+2*q) mod 2=r /\ (r+2*q)/2=q.
Proof. intro Hr. split; lia. Qed.
Lemma shape_bits_mod n : forall v, bits n v=bits n (v mod pow2 n).
Proof.
  induction n as [|n IH]; intro v; [reflexivity|].
  cbn [bits pow2].
  assert (HM : v mod (2*pow2 n)=v mod 2+2*((v/2) mod pow2 n)).
  { rewrite N.mod_mul_r by (pose proof (pow2_pos n); lia). reflexivity. }
  pose proof (shape_lowbit_arithmetic (v mod 2) ((v/2) mod pow2 n)
    ltac:(apply N.mod_lt; discriminate)) as [HP HD].
  assert (Hpar : (v mod (2*pow2 n)) mod 2=v mod 2) by (rewrite HM; exact HP).
  assert (Hdiv : (v mod (2*pow2 n))/2=(v/2) mod pow2 n) by (rewrite HM; exact HD).
  assert (HO : N.odd v=N.odd (v mod (2*pow2 n))).
  { rewrite !shape_odd_mod,Hpar. reflexivity. }
  rewrite <-HO,Hdiv. f_equal. apply IH.
Qed.

Lemma shape_bits_first12 v t : (12<=t)%nat -> v mod 4096=5 ->
  exists q, bits t v=[Sg;Bk;Sg;Bk]++repeat Bk 8++q.
Proof.
  intros HT HV. exists (bits (t-12) (v/pow2 12)).
  replace t with (12+(t-12))%nat at 1 by lia.
  rewrite (shape_bits_split 12 (t-12) v),(shape_bits_mod 12 v).
  change (v mod pow2 12) with (v mod 4096). rewrite HV.
  reflexivity.
Qed.
Lemma shape_bits_last12 v t : (12<=t)%nat -> v/pow2 (t-12)=8191 ->
  exists q, bits t v=q++repeat Sg 12.
Proof.
  intros HT HV. exists (bits (t-12) v).
  replace t with ((t-12)+12)%nat at 1 by lia.
  rewrite (shape_bits_split (t-12) 12 v),HV.
  reflexivity.
Qed.

Open Scope Q_scope.
Lemma epoch_shape c : Phi c<=1/8192 ->
  (exists p, c=p++repeat Sg 12) ->
  exists beta,
    epoch c=emitW 0%N c++beta /\
    scale c*nq (pow2 (length beta))==1/2 /\
    (exists q, beta=q++repeat Sg 12) /\
    (exists q, beta=[Sg;Bk;Sg;Bk]++repeat Bk 8++q).
Proof.
  intros HP HT.
  destruct (terminal_facts c HP HT) as [e [z [HE [HPow [HZ [HScale [HF [Hdiv [Hlo Hhi]]]]]]]]].
  set (v:=foldT 0%N c).
  fold v in Hdiv,Hlo,Hhi.
  set (t:=(e-1)%nat).
  assert (Het : e=S t) by (unfold t; lia).
  assert (Ht12 : (12<=t)%nat) by (unfold t; lia).
  assert (HPt : pow2 t=(4096*z)%N).
  { rewrite Het in HPow. cbn [pow2] in HPow. lia. }
  assert (HPsmall : pow2 (t-12)=z).
  { assert (HEq : pow2 t=(pow2 (t-12)*4096)%N).
    { replace t with ((t-12)+12)%nat at 1 by lia.
      rewrite shape_pow2_add. reflexivity. }
    lia. }
  assert (Hlog : N.log2 (v+5)=N.of_nat t).
  { apply N.log2_unique; [lia|].
    rewrite <-Nat2N.inj_succ,<- !pow2_N.
    rewrite HPt,<-Het,HPow. lia. }
  assert (Hquot : ((v+5)/pow2 (t-12)=8191)%N).
  { rewrite HPsmall. symmetry.
    apply (N.div_unique (v+5) z 8191 (v+5-8191*z)); lia. }
  assert (Hmod : ((v+5) mod 4096=5)%N) by lia.
  exists (bits t (v+5)%N). split.
  - unfold epoch. fold v. rewrite Hlog,Nat2N.id. reflexivity.
  - split.
    + rewrite shape_bits_length.
      rewrite Het,shape_nq_pow2_succ in HScale. qlin.
    + split; [apply shape_bits_last12|apply shape_bits_first12]; assumption.
Qed.


Open Scope Q_scope.
Lemma good_pair w : Good w -> Good (epoch w) -> Good (epoch (epoch w)).
Proof.
  intros HW HD.
  destruct (epoch_shape w (proj1 HW) (proj1 (proj2 HW)))
    as [beta [EB [SB [TB FB]]]].
  destruct (epoch_shape (epoch w) (proj1 HD) (proj1 (proj2 HD)))
    as [gamma [EG [SG [TG FG]]]].
  split; [eapply two_epoch_price; eassumption|].
  split.
  - destruct TG as [q EQ]. exists (emitW 0%N (epoch w)++q).
    rewrite EG,EQ,app_assoc; reflexivity.
  - rewrite EG. apply epoch_conversions; [exact (proj1 (proj2 HD))|exact FG].
Qed.

Close Scope Q_scope.
Open Scope sym_scope.
Open Scope N_scope.
Definition invariant w := cap w=0 /\ Good (decor w) /\ Good (epoch (decor w)).
Lemma invariant_step w : invariant w -> exists u,
  lt w ([S3;S2]*>0inf) -[tm]->+ lt u ([S3;S2]*>0inf) /\ invariant u.
Proof.
  intros [HZ [HW HD]].
  destruct (good_scan _ HW) as [v [HF HV]].
  destruct (epoch_run w v HZ HF ltac:(lia)) as [u [HU [EU HR]]].
  exists u; split; [exact HR|].
  unfold invariant; rewrite HU,EU. split; [reflexivity|].
  split; [exact HD|apply good_pair; assumption].
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  destruct initial_base12 as [w [HZ [HD HR]]].
  eapply multistep_nonhalt; [exact HR|].
  eapply progress_nonhalt_cond with (P:=invariant) (i0:=w)
    (C:=fun w => lt w ([S3;S2]*>0inf)).
  - exact invariant_step.
  - unfold invariant; rewrite HZ,HD; split; [reflexivity|exact base_good].
Qed.

End TM28.


Close Scope Q_scope. Close Scope Z_scope. Close Scope N_scope.
Close Scope nat_scope. Open Scope sym_scope.
Set Default Goal Selector "1".

(* Machine 32. *)
From BusyCoq Require Import Individual25.
From Coq Require Import String NArith Lia List PeanoNat Arith.Wf_nat Recdef.
Import ListNotations.
Set Default Goal Selector "all".

Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB3RB0LB---2RB_2RA3LA4LB2LB0RA").

(* Digits are nearest-head first; blocks are in physical tape order. *)
Inductive digit := D0 | D1 | DB | DA.
Inductive block := F | O | T | I.
Definition digit_cells d : list Sym :=
  match d with
  | D0 => [S2; S0] | D1 => [S2; S2]
  | DB => [S3; S0] | DA => [S3; S2]
  end.
Definition label b : Sym :=
  match b with F => S4 | O => S0 | T => S2 | I => S1 end.
Definition cells := flat_map (fun b => [label b; S4]).
Definition counter := flat_map digit_cells.
Definition binary d := match d with D0 | D1 => true | _ => false end.
Definition isF b := match b with F => true | _ => false end.
Definition notI b := match b with I => false | _ => true end.

Open Scope N_scope.
Fixpoint gap (w : list digit) : N :=
  match w with
  | [] => 0 | D0 :: v => 2 * gap v + 1 | D1 :: v => 2 * gap v
  | DB :: v => (2 * gap v + 1) / 3 | DA :: v => (2 * gap v) / 3
  end.

Inductive Inc : list digit -> list digit -> Prop :=
| inc0 w : Inc (D0 :: w) (D1 :: w)
| inc1 w v : Inc w v -> Inc (D1 :: w) (D0 :: v)
| incB w v : Inc w v -> Inc (DB :: w) (DA :: v)
| incA w v u : Inc w v -> Inc v u -> Inc (DA :: w) (DB :: u).

(* Quotient/remainder facts keep every actual counter value binary. *)
Ltac ndiv :=
  repeat match goal with
  | |- context [?x / ?d] =>
      let E := fresh "Ediv" in let R := fresh "Rdiv" in
      let q := fresh "q" in let r := fresh "r" in
      assert (E : x = d * (x / d) + x mod d) by
        (apply N.div_mod; discriminate);
      assert (R : x mod d < d) by (apply N.mod_lt; discriminate);
      set (q := x / d) in *; set (r := x mod d) in *;
      clearbody q r
  | H : context [?x / ?d] |- _ =>
      let E := fresh "Ediv" in let R := fresh "Rdiv" in
      let q := fresh "q" in let r := fresh "r" in
      assert (E : x = d * (x / d) + x mod d) by
        (apply N.div_mod; discriminate);
      assert (R : x mod d < d) by (apply N.mod_lt; discriminate);
      set (q := x / d) in *; set (r := x mod d) in *;
      clearbody q r
  end; nia.

Lemma inc_gap w v : Inc w v -> gap w = gap v + 1.
Proof. intro H; induction H; cbn [gap]; ndiv. Qed.
Lemma inc_length w v : Inc w v -> length v = length w.
Proof. intro H; induction H; cbn; congruence. Qed.
Lemma inc_pattern w v : Inc w v -> map binary v = map binary w.
Proof. intro H; induction H; cbn; congruence. Qed.

Definition beta h := if h mod 3 =? 0 then O else if h mod 3 =? 1 then T else I.
Definition alpha h := if h mod 3 =? 0 then T else if h mod 3 =? 1 then I else O.
Lemma mod3 h : h mod 3 = 0 \/ h mod 3 = 1 \/ h mod 3 = 2.
Proof. pose proof (N.mod_lt h 3 ltac:(discriminate)); lia. Qed.
Lemma beta_succ h : beta (h + 1) = alpha h.
Proof.
  unfold beta, alpha. destruct (mod3 h) as [H|[H|H]];
    assert (E : (h+1) mod 3 = (h mod 3 + 1) mod 3)
      by (rewrite N.Div0.add_mod; reflexivity);
    rewrite E, H; reflexivity.
Qed.
Lemma alpha_two h : alpha (h + 2) = beta h.
Proof.
  unfold beta, alpha. destruct (mod3 h) as [H|[H|H]];
    assert (E : (h+2) mod 3 = (h mod 3 + 2) mod 3)
      by (rewrite N.Div0.add_mod; reflexivity);
    rewrite E, H; reflexivity.
Qed.
Fixpoint sat (w : list digit) : list block :=
  match w with
  | [] => []
  | D0 :: v | D1 :: v => sat v ++ [F]
  | DB :: v => sat v ++ [beta (gap v)]
  | DA :: v => sat v ++ [alpha (gap v)]
  end.
Lemma sat_preserved w v : Inc w v -> sat v = sat w.
Proof.
  intro H; induction H; cbn [sat]; try congruence.
  - rewrite IHInc, (inc_gap _ _ H), beta_succ; reflexivity.
  - rewrite IHInc2, IHInc1, (inc_gap _ _ H), (inc_gap _ _ H0).
    replace (gap u + 1 + 1) with (gap u + 2) by lia.
    rewrite alpha_two; reflexivity.
Qed.
Lemma sat_pattern w : map isF (sat w) = rev (map binary w).
Proof.
  induction w as [|d w IH]; [reflexivity|].
  destruct d; cbn [sat binary map rev]; rewrite map_app, IH; cbn;
    try reflexivity; unfold beta, alpha;
    repeat destruct (_ =? _); reflexivity.
Qed.

Lemma inc_exists w : 0 < gap w -> exists v, Inc w v.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length digit))).
  destruct w as [|d w]; [cbn; lia|].
  destruct d; intro Hp.
  - exists (D1 :: w); constructor.
  - assert (Hw : 0 < gap w) by (cbn [gap] in Hp; lia).
    destruct (IH w ltac:(unfold ltof; cbn; lia) Hw) as [v Hv].
    exists (D0 :: v); constructor; exact Hv.
  - assert (Hw : 0 < gap w) by (cbn [gap] in Hp; ndiv).
    destruct (IH w ltac:(unfold ltof; cbn; lia) Hw) as [v Hv].
    exists (DA :: v); constructor; exact Hv.
  - assert (Hw : 1 < gap w) by (cbn [gap] in Hp; ndiv).
    destruct (IH w ltac:(unfold ltof; cbn; lia) ltac:(lia)) as [v Hv].
    pose proof (inc_gap _ _ Hv) as Hg.
    pose proof (inc_length _ _ Hv) as Hl.
    destruct (IH v ltac:(unfold ltof; cbn; lia) ltac:(lia)) as [u Hu].
    exists (DB :: u); econstructor; eauto.
Qed.

Definition xnext (g : N) (b : block) : N :=
  match b with
  | F => 2*g+1 | O => 2*g | T => 2*g-1 | I => 2*((g-8)/3)+1
  end.
Definition affordable g b := match b with I => 8 <= g | T => 1 <= g | _ => True end.
Fixpoint XSafe (g : N) (L : list block) : Prop :=
  match L with [] => True | b :: xs => affordable g b /\ XSafe (xnext g b) xs end.
Fixpoint xfold (g : N) (L : list block) : N :=
  match L with [] => g | b :: xs => xfold (xnext g b) xs end.
Lemma xnext_mono g G b : g <= G -> xnext g b <= xnext G b.
Proof. intro H; destruct b; unfold xnext; ndiv. Qed.
Lemma xnext_max g b : xnext g b <= xnext g F.
Proof. destruct b; unfold xnext; ndiv. Qed.
Lemma xnext_min g b : 8 <= g -> xnext g I <= xnext g b.
Proof. intro H; destruct b; unfold xnext; ndiv. Qed.
Lemma xfold_app L M g : xfold g (L ++ M) = xfold (xfold g L) M.
Proof. revert g; induction L; cbn; auto. Qed.
Lemma xsafe_app L M g :
  XSafe g L -> XSafe (xfold g L) M -> XSafe g (L ++ M).
Proof. revert g; induction L; cbn; intuition. Qed.

Definition inv b (t : N) :=
  match b with F => t/2 | O => (t+1)/2 | T => (t+2)/2 | I => 8+3*(t/2) end.
Lemma inv_sound b t G : inv b t <= G -> affordable G b /\ t <= xnext G b.
Proof. destruct b; unfold inv, affordable, xnext; intro H; split; try trivial; ndiv. Qed.
Lemma inv_twice b t : 2*inv b t <= 3*t+16.
Proof. destruct b; unfold inv; ndiv. Qed.

Lemma inherited_exact L S g G :
  map isF S = map notI L -> XSafe g L -> g <= G ->
  XSafe G S /\ xfold g L <= xfold G S.
Proof.
  revert S g G; induction L as [|x L IH]; intros S g G E H Hle;
    destruct S as [|y S]; try discriminate.
  - cbn; auto.
  - cbn in E; inversion E as [[Eh Et]].
    destruct H as [Ha Hr].
    assert (Hy : affordable G y /\ xnext g x <= xnext G y).
    { destruct x.
      - destruct y; cbn in Eh; try discriminate; split; [exact Logic.I|].
        apply xnext_mono; exact Hle.
      - destruct y; cbn in Eh; try discriminate; split; [exact Logic.I|].
        eapply N.le_trans; [apply xnext_max|apply xnext_mono; exact Hle].
      - destruct y; cbn in Eh; try discriminate; split; [exact Logic.I|].
        eapply N.le_trans; [apply xnext_max|apply xnext_mono; exact Hle].
      - assert (Hg : 8 <= G) by (cbn [affordable] in Ha; lia).
        split; [destruct y; cbn [affordable]; auto; lia|].
        eapply N.le_trans; [apply xnext_mono; exact Hle|apply xnext_min; exact Hg]. }
    destruct Hy as [Hay Hxy].
    destruct (IH S _ _ Et Hr Hxy) as [HS HD].
    split; [split; assumption|exact HD].
Qed.

Definition descend (g : N) := (2*g-1)/3.
Definition freshDigit (g : N) :=
  if g mod 3 =? 0 then I else if g mod 3 =? 1 then O else T.
Lemma descend_lt g : 0 < g -> descend g < g.
Proof. unfold descend; intro H; ndiv. Qed.
Lemma Nnat_lt a b : (N.to_nat a < N.to_nat b)%nat <-> a < b.
Proof. rewrite <- Nat.compare_lt_iff, <- N2Nat.inj_compare; reflexivity. Qed.
Lemma Nnat_le a b : (N.to_nat a <= N.to_nat b)%nat <-> a <= b.
Proof. rewrite <- Nat.compare_le_iff, <- N2Nat.inj_compare; reflexivity. Qed.
Function fresh (g : N) {measure N.to_nat g} : list block :=
  match g with
  | N0 => []
  | Npos _ => freshDigit g :: fresh (descend g)
  end.
Proof. intros; apply Nnat_lt; apply descend_lt; lia. Defined.

Fixpoint need_word (L : list block) : N :=
  match L with [] => 62 | b :: xs => inv b (need_word xs) end.
Definition need g := need_word (fresh g).
Lemma fresh_zero : fresh 0 = [].
Proof. rewrite fresh_equation; reflexivity. Qed.
Lemma fresh_pos g : 0 < g -> fresh g = freshDigit g :: fresh (descend g).
Proof. intro H; rewrite fresh_equation; destruct g; [lia|reflexivity]. Qed.
Lemma need_zero : need 0 = 62.
Proof. unfold need; rewrite fresh_zero; reflexivity. Qed.
Lemma need_pos g : 0 < g -> need g = inv (freshDigit g) (need (descend g)).
Proof. intro H; unfold need; rewrite fresh_pos by exact H; reflexivity. Qed.
Lemma need_word_safe L G :
  need_word L <= G -> XSafe G L /\ 62 <= xfold G L.
Proof.
  revert G; induction L as [|b L IH]; intros G H; cbn in *; [auto|].
  destruct (inv_sound _ _ _ H) as [Ha Hn].
  destruct (IH _ Hn); split; [split; assumption|assumption].
Qed.

Lemma normal_small_certificate :
  forallb (fun n => need (N.of_nat n) + 30 <=? 2*N.of_nat n)
    (seq 133 67) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma normal_small g : 133 <= g < 200 -> need g + 30 <= 2*g.
Proof.
  intro H. pose proof normal_small_certificate as C.
  rewrite forallb_forall in C.
  specialize (C (N.to_nat g)).
  assert (Hin : In (N.to_nat g) (seq 133 67)).
  { apply in_seq. split.
    - change (N.to_nat 133 <= N.to_nat g)%nat; apply Nnat_le; lia.
    - change (N.to_nat g < N.to_nat 200)%nat; apply Nnat_lt; lia. }
  specialize (C Hin). rewrite N2Nat.id in C. apply N.leb_le; exact C.
Qed.
Lemma need_bound g : 133 <= g -> need g + 30 <= 2*g.
Proof.
  induction g as [g IH] using (well_founded_induction N.lt_wf_0).
  intro H. destruct (N.lt_ge_cases g 200) as [Hs|Hs].
  - apply normal_small; lia.
  - assert (Hp : 0 < g) by lia.
    assert (Hd : 133 <= descend g) by (unfold descend; ndiv).
    pose proof (IH _ (descend_lt _ Hp) Hd) as Hi.
    rewrite need_pos by exact Hp.
    pose proof (inv_twice (freshDigit g) (need (descend g))) as Hv.
    unfold descend in *; ndiv.
Qed.
Lemma fresh_ends_zero g : 0 < g -> exists P, fresh g = P ++ [O].
Proof.
  induction g as [g IH] using (well_founded_induction N.lt_wf_0).
  intro H. destruct (N.eq_dec (descend g) 0) as [Hz|Hz].
  - assert (Hg : g = 1) by (unfold descend in Hz; ndiv).
    subst g; exists ([] : list block); rewrite fresh_pos by reflexivity.
    change ([O] = [O]); reflexivity.
  - destruct (IH _ (descend_lt _ H) ltac:(lia)) as [P HP].
    exists (freshDigit g :: P). rewrite fresh_pos by exact H.
    rewrite HP; reflexivity.
Qed.

Definition junctionTop (g : N) := (g-8)/3.
Definition junctionGap (g : N) := (2*junctionTop g)/3.
Definition junctionFirst (g : N) :=
  if g mod 3 =? 0 then O else if g mod 3 =? 1 then I else T.
Definition suffix g := junctionFirst g :: alpha (junctionTop g) :: fresh (junctionGap g).
Definition suffixNeed g := need_word (suffix g).
Lemma junction_small_certificate :
  forallb (fun n => suffixNeed (2*N.of_nat n) <=? 2*N.of_nat n)
    (seq 31 273) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma junction_small g :
  62 <= g < 608 -> g mod 2 = 0 -> suffixNeed g <= g.
Proof.
  intros H He. pose proof junction_small_certificate as C.
  rewrite forallb_forall in C.
  specialize (C (N.to_nat (g/2))).
  assert (Htwo : g = 2*(g/2)) by
    (pose proof (N.div_mod g 2 ltac:(discriminate)); lia).
  assert (Hin : In (N.to_nat (g/2)) (seq 31 273)).
  { apply in_seq. split.
    - change (N.to_nat 31 <= N.to_nat (g/2))%nat; apply Nnat_le; lia.
    - change (N.to_nat (g/2) < N.to_nat 304)%nat; apply Nnat_lt; lia. }
  specialize (C Hin). rewrite N2Nat.id, <- Htwo in C. apply N.leb_le; exact C.
Qed.
Lemma suffix_need_bound g : 62 <= g -> g mod 2 = 0 -> suffixNeed g <= g.
Proof.
  intros H He. destruct (N.lt_ge_cases g 608) as [Hs|Hs].
  - apply junction_small; auto; lia.
  - assert (Hj : 133 <= junctionGap g) by
      (unfold junctionGap, junctionTop; ndiv).
    pose proof (need_bound _ Hj) as Hn.
    pose proof (inv_twice (alpha (junctionTop g)) (need (junctionGap g))) as H2.
    pose proof (inv_twice (junctionFirst g)
      (inv (alpha (junctionTop g)) (need (junctionGap g)))) as H1.
    assert (H9 : 9*junctionGap g <= 2*g) by
      (unfold junctionGap, junctionTop; ndiv).
    unfold suffixNeed, suffix; cbn [need_word]; fold (need (junctionGap g)); nia.
Qed.
Lemma suffix_safe g G :
  62 <= g -> g mod 2 = 0 -> g <= G ->
  XSafe G (suffix g) /\ 62 <= xfold G (suffix g) /\ xfold G (suffix g) mod 2 = 0.
Proof.
  intros H He HG.
  destruct (need_word_safe (suffix g) G) as [HS HE].
  { eapply N.le_trans; [apply suffix_need_bound; eauto|exact HG]. }
  split; [exact HS|]. split; [exact HE|].
  assert (Hp : 0 < junctionGap g) by (unfold junctionGap, junctionTop; ndiv).
  destruct (fresh_ends_zero _ Hp) as [P HP].
  unfold suffix; rewrite HP.
  change (xfold G ((junctionFirst g :: alpha (junctionTop g) :: P) ++ [O]) mod 2 = 0).
  rewrite xfold_app; cbn [xfold xnext]. rewrite N.mul_comm.
  apply N.Div0.mod_mul.
Qed.

(* The compressed carry rule has arbitrary untouched tape contexts. *)
Lemma inc_sweep w v : Inc w v -> forall l r,
  l <* counter w {{B}}> S2 >> r -[tm]->+
  l <* counter v {{B}}> S4 >> r.
Proof.
  intro H; induction H; intros l r; cbn [counter flat_map digit_cells]; simpl_tape.
  - execute.
  - do 2 step. eapply progress_trans; [apply IHInc|]. execute.
  - do 4 step. eapply progress_trans; [apply IHInc|]. execute.
  - do 2 step. eapply progress_trans; [apply IHInc1|].
    do 4 step. eapply progress_trans; [apply IHInc2|]. execute.
Qed.
Lemma inc_sweep3 w v : Inc w v -> forall l r,
  l <* counter w {{B}}> S3 >> r -[tm]->+
  l <* counter v {{B}}> S2 >> r.
Proof.
  intro H; destruct H; intros l r; cbn [counter flat_map digit_cells]; simpl_tape.
  - execute.
  - do 2 step. eapply progress_trans; [apply inc_sweep; exact H|]. execute.
  - do 4 step. eapply progress_trans; [apply inc_sweep; exact H|]. execute.
  - do 2 step. eapply progress_trans; [apply inc_sweep; exact H|].
    do 4 step. eapply progress_trans; [apply inc_sweep; exact H0|]. execute.
Qed.

Definition left w := counter w *> S2 >> S2 >> 0inf.
Lemma overflow w : gap w = 0 -> forall r,
  left w {{B}}> S2 >> r -[tm]->+
  left [] {{B}}> S4 >> S4 >> cells (sat w) *> r.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length digit))).
  destruct w as [|d w].
  - intros _ r; cbn [left counter flat_map sat cells]; execute.
  - destruct d; intro Hz.
    + cbn [gap] in Hz; lia.
    + assert (Hw : gap w = 0) by (cbn [gap] in Hz; lia).
      intro r; cbn [left counter flat_map digit_cells sat];
        unfold cells; rewrite flat_map_app; cbn [flat_map label]; simpl_tape.
      do 2 step. apply (IH w ltac:(unfold ltof; cbn; lia) Hw).
    + assert (Hw : gap w = 0) by (cbn [gap] in Hz; ndiv).
      intro r; cbn [sat]; rewrite Hw; cbn [beta].
      cbn [left counter flat_map digit_cells]; unfold cells;
        rewrite flat_map_app; cbn [flat_map label]; simpl_tape.
      do 4 step. apply (IH w ltac:(unfold ltof; cbn; lia) Hw).
    + assert (Hw : gap w <= 1) by (cbn [gap] in Hz; ndiv).
      destruct (N.eq_dec (gap w) 0) as [H0|H1].
      * intro r; cbn [sat]; rewrite H0; cbn [alpha].
        cbn [left counter flat_map digit_cells]; unfold cells;
          rewrite flat_map_app; cbn [flat_map label]; simpl_tape.
        do 2 step. apply (IH w ltac:(unfold ltof; cbn; lia) H0).
      * assert (Hg : gap w = 1) by lia.
        destruct (inc_exists w ltac:(lia)) as [v Hv].
        pose proof (inc_gap _ _ Hv) as Hgap.
        pose proof (inc_length _ _ Hv) as Hlen.
        pose proof (sat_preserved _ _ Hv) as Hsat.
        intro r; cbn [sat]; rewrite Hg; cbn [alpha].
        cbn [left counter flat_map digit_cells]; unfold cells;
          rewrite flat_map_app; cbn [flat_map label]; simpl_tape.
        do 2 step. eapply progress_trans; [apply inc_sweep; exact Hv|].
        do 4 step.
        rewrite <- Hsat. apply (IH v ltac:(unfold ltof; cbn; lia) ltac:(lia)).
Qed.

Definition Four w u := exists a b c,
  Inc w a /\ Inc a b /\ Inc b c /\ Inc c u.
Lemma four_exists w : 4 <= gap w -> exists u, Four w u.
Proof.
  intro H.
  destruct (inc_exists w ltac:(lia)) as [a Ha]; pose proof (inc_gap _ _ Ha).
  destruct (inc_exists a ltac:(lia)) as [b Hb]; pose proof (inc_gap _ _ Hb).
  destruct (inc_exists b ltac:(lia)) as [c Hc]; pose proof (inc_gap _ _ Hc).
  destruct (inc_exists c ltac:(lia)) as [u Hu].
  exists u, a, b, c; auto.
Qed.
Lemma four_facts w u : Four w u ->
  gap w = gap u + 4 /\ sat u = sat w /\ map binary u = map binary w.
Proof.
  intros [a [b [c [Ha [Hb [Hc Hu]]]]]].
  pose proof (inc_gap _ _ Ha); pose proof (inc_gap _ _ Hb);
    pose proof (inc_gap _ _ Hc); pose proof (inc_gap _ _ Hu).
  split; [lia|]. split.
  - rewrite (sat_preserved _ _ Hu), (sat_preserved _ _ Hc),
      (sat_preserved _ _ Hb), (sat_preserved _ _ Ha); reflexivity.
  - rewrite (inc_pattern _ _ Hu), (inc_pattern _ _ Hc),
      (inc_pattern _ _ Hb), (inc_pattern _ _ Ha); reflexivity.
Qed.
Lemma one_bridge0 w u : Four w u -> forall l r,
  l <* counter (D0 :: w) {{B}}> S1 >> r -[tm]->+
  l <* counter (DB :: u) {{B}}> S4 >> r.
Proof.
  intros [a [b [c [Ha [Hb [Hc Hu]]]]]] l r.
  cbn [counter flat_map digit_cells]; simpl_tape.
  do 4 step. eapply progress_trans; [apply inc_sweep; exact Ha|].
  do 2 step.
  eapply progress_trans;
    [apply (inc_sweep3 (DB :: a) (DA :: b)); apply incB; exact Hb|].
  eapply (inc_sweep (DA :: b) (DB :: u)); apply incA with c; assumption.
Qed.
Lemma one_bridge1 w u : Four w u -> forall l r,
  l <* counter (D1 :: w) {{B}}> S1 >> r -[tm]->+
  l <* counter (DA :: u) {{B}}> S4 >> r.
Proof.
  intros [a [b [c [Ha [Hb [Hc Hu]]]]]] l r.
  cbn [counter flat_map digit_cells]; simpl_tape.
  do 2 step. eapply progress_trans; [apply inc_sweep; exact Ha|].
  do 4 step.
  eapply progress_trans;
    [apply (inc_sweep3 (DA :: a) (DB :: c)); apply incA with b; assumption|].
  eapply (inc_sweep (DB :: c) (DA :: u)); apply incB; exact Hu.
Qed.

Definition BinHead w :=
  match w with D0 :: _ | D1 :: _ => True | _ => False end.
Lemma binhead_pattern w : BinHead w -> map binary w = true :: tl (map binary w).
Proof. destruct w as [|d w]; [contradiction|]; destruct d; cbn; intuition. Qed.
Lemma reset_block w b : BinHead w -> affordable (gap w) b ->
  exists v, BinHead v /\ gap v = xnext (gap w) b /\
    map binary v = true :: notI b :: tl (map binary w) /\
    forall l r, l <* counter w {{B}}> label b >> S4 >> r -[tm]->*
      l <* counter v {{B}}> r.
Proof.
  intros HB HA. destruct b.
  - exists (D0 :: w); split; [exact Logic.I|]. split; [reflexivity|].
    split; [cbn; rewrite (binhead_pattern _ HB); reflexivity|].
    intros l r; cbn [label counter flat_map digit_cells]; simpl_tape; execute.
  - exists (D1 :: w); split; [exact Logic.I|]. split; [reflexivity|].
    split; [cbn; rewrite (binhead_pattern _ HB); reflexivity|].
    intros l r; cbn [label counter flat_map digit_cells]; simpl_tape; execute.
  - destruct (inc_exists w ltac:(cbn [affordable] in HA; lia)) as [v Hv].
    exists (D0 :: v); split; [exact Logic.I|].
    split; [cbn [gap xnext]; pose proof (inc_gap _ _ Hv); lia|].
    split; [cbn; rewrite (inc_pattern _ _ Hv), (binhead_pattern _ HB); reflexivity|].
    intros l r; cbn [label]. follow100 (inc_sweep _ _ Hv).
    cbn [counter flat_map digit_cells]; simpl_tape; execute.
  - destruct w as [|d w]; [contradiction|]. destruct d; try contradiction.
    + assert (Hg : 4 <= gap w) by (cbn [affordable gap] in HA; lia).
      destruct (four_exists w Hg) as [u Hu].
      destruct (four_facts _ _ Hu) as [Hgu [Hsu Hpu]].
      exists (D0 :: DB :: u); split; [exact Logic.I|].
      split; [cbn [gap xnext]; ndiv|].
      split; [cbn [map binary notI tl]; rewrite Hpu; reflexivity|].
      intros l r; cbn [label]. follow100 (one_bridge0 _ _ Hu).
      cbn [counter flat_map digit_cells]; simpl_tape; execute.
    + assert (Hg : 4 <= gap w) by (cbn [affordable gap] in HA; lia).
      destruct (four_exists w Hg) as [u Hu].
      destruct (four_facts _ _ Hu) as [Hgu [Hsu Hpu]].
      exists (D0 :: DA :: u); split; [exact Logic.I|].
      split; [cbn [gap xnext]; ndiv|].
      split; [cbn [map binary notI tl]; rewrite Hpu; reflexivity|].
      intros l r; cbn [label]. follow100 (one_bridge1 _ _ Hu).
      cbn [counter flat_map digit_cells]; simpl_tape; execute.
Qed.

Lemma reset_exact L w : BinHead w -> XSafe (gap w) L ->
  exists v, BinHead v /\ gap v = xfold (gap w) L /\
    map binary v = true :: rev (map notI L) ++ tl (map binary w) /\
    forall l r, l <* counter w {{B}}> cells L *> r -[tm]->*
      l <* counter v {{B}}> r.
Proof.
  revert w; induction L as [|b L IH]; intros w HB HS.
  - exists w; split; [exact HB|]. split; [reflexivity|].
    split; [apply binhead_pattern; exact HB|]. intros; finish.
  - destruct HS as [Ha Hr].
    destruct (reset_block w b HB Ha) as [u [Hu [Hgu [Hpu Hrun]]]].
    rewrite <- Hgu in Hr.
    destruct (IH u Hu Hr) as [v [Hv [Hgv [Hpv Hrest]]]].
    exists v; split; [exact Hv|]. split; [cbn; rewrite Hgv, Hgu; reflexivity|].
    split.
    + rewrite Hpv, Hpu; cbn [map rev tl]. rewrite <- app_assoc; reflexivity.
    + intros l r; cbn [cells flat_map]; simpl_tape.
      follow Hrun. apply Hrest.
Qed.

Lemma junction_label0 h : beta h = junctionFirst (2*h+9).
Proof.
  destruct (mod3 h) as [H|[H|H]]; unfold beta, junctionFirst;
    rewrite N.Div0.add_mod, N.Div0.mul_mod, H; reflexivity.
Qed.
Lemma junction_label1 h : alpha h = junctionFirst (2*h+8).
Proof.
  destruct (mod3 h) as [H|[H|H]]; unfold alpha, junctionFirst;
    rewrite N.Div0.add_mod, N.Div0.mul_mod, H; reflexivity.
Qed.
Lemma junction_exact w : BinHead w -> 9 <= gap w ->
  exists u, gap u = junctionGap (gap w) /\
    sat u = sat (tl w) ++ [junctionFirst (gap w); alpha (junctionTop (gap w))] /\
    forall l, l <* counter w {{B}}> S1 >> 0inf -[tm]->*
      l <* counter u {{B}}> 0inf.
Proof.
  intros HB HG; destruct w as [|d w]; [contradiction|].
  destruct d; try contradiction.
  - assert (H4 : 4 <= gap w) by (cbn [gap] in HG; lia).
    destruct (four_exists _ H4) as [u HU].
    destruct (four_facts _ _ HU) as [Hg [Hs Hp]].
    assert (E : gap (D0::w) = 2*gap u+9) by (cbn [gap]; lia).
    assert (ET : junctionTop (gap (D0::w)) = gap (DB::u)) by
      (unfold junctionTop; cbn [gap]; ndiv).
    exists (DA::DB::u); split.
    + unfold junctionGap; rewrite ET; reflexivity.
    + split.
      * cbn [sat tl]; rewrite Hs, ET, E, <- junction_label0.
        rewrite <- app_assoc; reflexivity.
      * intro l. follow100 (one_bridge0 _ _ HU).
        cbn [counter flat_map digit_cells]; simpl_tape; execute.
  - assert (H4 : 4 <= gap w) by (cbn [gap] in HG; lia).
    destruct (four_exists _ H4) as [u HU].
    destruct (four_facts _ _ HU) as [Hg [Hs Hp]].
    assert (E : gap (D1::w) = 2*gap u+8) by (cbn [gap]; lia).
    assert (ET : junctionTop (gap (D1::w)) = gap (DA::u)) by
      (unfold junctionTop; cbn [gap]; ndiv).
    exists (DA::DA::u); split.
    + unfold junctionGap; rewrite ET; reflexivity.
    + split.
      * cbn [sat tl]; rewrite Hs, ET, E, <- junction_label1.
        rewrite <- app_assoc; reflexivity.
      * intro l. follow100 (one_bridge1 _ _ HU).
        cbn [counter flat_map digit_cells]; simpl_tape; execute.
Qed.

Definition phase L := left [] {{B}}> S4 >> S4 >> cells L *> S1 >> 0inf.
Lemma normal_exact w :
  left w {{B}}> 0inf -[tm]->+ phase (sat w ++ fresh (gap w)).
Proof.
  induction w as [w IH] using (well_founded_induction
    (well_founded_ltof _ (fun w => N.to_nat (gap w)))).
  destruct (N.eq_dec (gap w) 0) as [Hz|Hz].
  - unfold phase; rewrite Hz, fresh_zero, app_nil_r.
    do 2 step. apply overflow; exact Hz.
  - destruct (inc_exists w ltac:(lia)) as [v Hv].
    pose proof (inc_gap _ _ Hv) as Hg.
    assert (Hd : gap (DB :: v) = descend (gap w)) by
      (cbn [gap]; unfold descend; ndiv).
    assert (Hlt : ltof _ (fun w => N.to_nat (gap w)) (DB :: v) w).
    { unfold ltof; apply Nnat_lt; rewrite Hd; apply descend_lt; lia. }
    assert (Hb : freshDigit (gap w) = beta (gap v)).
    { rewrite Hg; unfold freshDigit, beta.
      destruct (mod3 (gap v)) as [H|[H|H]];
        rewrite N.Div0.add_mod, H; reflexivity. }
    pose proof (IH _ Hlt) as Hrun.
    cbn [sat] in Hrun; rewrite (sat_preserved _ _ Hv), Hd in Hrun.
    rewrite fresh_pos by lia. rewrite Hb.
    rewrite <- app_assoc in Hrun. cbn [app] in Hrun.
    do 2 step. unfold left.
    eapply progress_trans; [apply inc_sweep; exact Hv|].
    do 2 step. exact Hrun.
Qed.

Lemma map_tail {X Y} (f : X -> Y) xs : map f (tl xs) = tl (map f xs).
Proof. destruct xs; reflexivity. Qed.
Lemma revolution L : XSafe 1 L -> 9 <= xfold 1 L ->
  exists S, map isF S = map notI L /\
    phase L -[tm]->+ phase (S ++ suffix (xfold 1 L)).
Proof.
  intros HS HG.
  destruct (reset_exact L [D0] Logic.I HS) as [w [Hw [Hgw [Hpw Hreset]]]].
  change (gap w = xfold 1 L) in Hgw.
  destruct (junction_exact w Hw ltac:(lia)) as [u [Hgu [Hsu Hj]]].
  exists (sat (tl w)); split.
  - rewrite sat_pattern, map_tail.
    rewrite Hpw. cbn [map tl]. rewrite app_nil_r, rev_involutive; reflexivity.
  - pose proof (normal_exact u) as Hn.
    rewrite Hsu, Hgu, <- app_assoc, Hgw in Hn.
    change (left u {{B}}> 0inf -[tm]->+
      phase (sat (tl w) ++ suffix (xfold 1 L))) in Hn.
    unfold phase at 1. do 2 step.
    eapply evstep_progress_trans; [apply Hreset|].
    eapply evstep_progress_trans; [apply Hj|]. exact Hn.
Qed.

Definition Invariant L :=
  XSafe 1 L /\ 62 <= xfold 1 L /\ xfold 1 L mod 2 = 0.
Lemma invariant_step L : Invariant L ->
  exists L', phase L -[tm]->+ phase L' /\ Invariant L'.
Proof.
  intros [HS [HG HE]].
  destruct (revolution L HS ltac:(lia)) as [S [Hpat Hrun]].
  destruct (inherited_exact L S 1 1 Hpat HS (N.le_refl 1)) as [HS' HD].
  destruct (suffix_safe _ _ HG HE HD) as [HF [H62 Heven]].
  exists (S ++ suffix (xfold 1 L)); split; [exact Hrun|].
  unfold Invariant; split; [apply xsafe_app; assumption|].
  rewrite xfold_app; auto.
Qed.

Definition firstBlocks := [F;F;F;O;F;O;T].
Definition seed := repeat F 7 ++ suffix 243.
Lemma first_safe : XSafe 1 firstBlocks.
Proof. vm_compute; intuition discriminate. Qed.
Lemma first_gap : xfold 1 firstBlocks = 243.
Proof. vm_compute; reflexivity. Qed.
Lemma seed_gap : xfold 1 seed = 28958.
Proof. vm_compute; reflexivity. Qed.
Lemma seed_safe : XSafe 1 seed.
Proof. vm_compute; intuition discriminate. Qed.
Lemma seed_invariant : Invariant seed.
Proof.
  unfold Invariant; rewrite seed_gap; split; [apply seed_safe|].
  vm_compute; intuition discriminate.
Qed.
Lemma allF n S : map isF S = repeat true n -> S = repeat F n.
Proof.
  revert S; induction n as [|n IH]; intros S H; destruct S as [|b S];
    cbn in *; try discriminate; [reflexivity|].
  destruct b; cbn in H; try discriminate.
  inversion H. f_equal. apply IH; assumption.
Qed.
Lemma seed_reached : phase firstBlocks -[tm]->+ phase seed.
Proof.
  destruct (revolution firstBlocks first_safe ltac:(rewrite first_gap; discriminate))
    as [S [Hpat Hrun]].
  assert (E : S = repeat F 7) by (apply allF; exact Hpat).
  rewrite E, first_gap in Hrun; exact Hrun.
Qed.
Lemma init_306 : c0 -[tm]->* phase firstBlocks.
Proof.
  unfold phase, firstBlocks, left, cells, counter; cbn.
  do 306 step. finish.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_306|].
  eapply multistep_nonhalt; [apply progress_evstep; apply seed_reached|].
  eapply progress_nonhalt_cond with (P:=Invariant) (i0:=seed).
  - exact invariant_step.
  - exact seed_invariant.
Qed.

End TM32.


Close Scope Q_scope. Close Scope Z_scope. Close Scope N_scope.
Close Scope nat_scope. Open Scope sym_scope.
Set Default Goal Selector "1".

(* Machine 38. *)
From BusyCoq Require Import Individual25.
From Coq Require Import NArith ZArith Lia List String.
Import ListNotations.

(* BB(2,5), classification entry 38.  The tape blocks below are data,
   not a second machine or a bespoke execution relation. *)
Module TM38.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LA3LB_1LA3LB1RA4RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LB := W | U | D.
Inductive RB := V | C | C1 | G | P | S | Q.

Definition lc (b : LB) : list Sym :=
  match b with W => [1;1] | U => [1;0] | D => [4;0] end.
Definition rc (b : RB) : list Sym :=
  match b with
  | V => [2;2] | C => [1;3] | C1 => [2;3] | G => [3;3]
  | P => [2] | S => [3] | Q => [1]
  end.
Definition left (bs : list LB) := flat_map lc bs *> [1;1] *> 0inf.
Definition right (rs : list RB) := flat_map rc rs *> 0inf.
Definition lt (bs : list LB) (rs : list RB) := left bs <{{A}} right rs.
Definition gt (bs : list LB) (rs : list RB) := left bs {{A}}> right rs.
Definition wide (bs : list LB) (rs : list RB) := left bs << 0 {{B}}> right rs.
Definition lb (bs : list LB) (rs : list RB) := left bs <{{B}} right rs.

Ltac block_run := unfold lt, gt, wide, lb, left, right;
  cbn [flat_map lc rc]; execute.

Lemma lt_nil r : lt [] r -->+ wide [] r.
Proof. block_run. Qed.
Lemma lt_W l r : lt (W::l) r -->* lt l (V::r).
Proof. block_run. Qed.
Lemma lt_U l r : lt (U::l) r -->* gt (W::l) r.
Proof. block_run. Qed.
Lemma lt_D l r : lt (D::l) r -->* lt l (C::r).
Proof. block_run. Qed.

Lemma gt_nil l : gt l [] -->* lt l [P;Q].
Proof. block_run. Qed.
Lemma gt_V l r : gt l (V::r) -->* gt (U::l) r.
Proof. block_run. Qed.
Lemma gt_C l r : gt l (C::r) -->* lt l (C1::r).
Proof. block_run. Qed.
Lemma gt_C1 l r : gt l (C1::r) -->* gt (D::l) r.
Proof. block_run. Qed.
Lemma gt_G l r : gt l (G::r) -->* lt l (C::r).
Proof. block_run. Qed.
Lemma gt_P l r : gt l (P::r) -->* wide l r.
Proof. block_run. Qed.
Lemma gt_S l r : gt l (S::r) -->* lt l (Q::r).
Proof. block_run. Qed.
Lemma gt_Q l r : gt l (Q::r) -->* lt l (P::r).
Proof. block_run. Qed.

Lemma wide_nil l : wide l [] -->* lb l [G].
Proof. block_run. Qed.
Lemma wide_V l r : wide l (V::r) -->* wide (U::l) r.
Proof. block_run. Qed.
Lemma wide_C l r : wide l (C::r) -->* lt l (C::S::r).
Proof. block_run. Qed.
Lemma wide_C1 l r : wide l (C1::r) -->* lt l (P::V::r).
Proof. block_run. Qed.
Lemma wide_G l r : wide l (G::r) -->* lt l (C::Q::r).
Proof. block_run. Qed.
Lemma wide_P l r : wide l (P::r) -->* gt (U::l) r.
Proof. block_run. Qed.
Lemma wide_S l r : wide l (S::r) -->* gt (D::l) r.
Proof. block_run. Qed.
Lemma wide_Q l r : wide l (Q::r) -->* lt l (C::r).
Proof. block_run. Qed.
Lemma lb_U l r : lb (U::l) r -->* lt l (C::r).
Proof. block_run. Qed.
Lemma lb_W l r : lb (W::l) r -->* lb l (G::r).
Proof. block_run. Qed.

(* Parametric segment interfaces also permit composing these rules with
   unrelated tapes through BusyCoq's existing segment/side calculus. *)
Lemma C_call : segRLs tm [((A,[]),(A,[]))] [] (rc C) (rc C1).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=10%nat). reflexivity.
Qed.
Lemma C1_call : segRLs tm [((A,[]),(A,[]))]
    [((A,[]),(A,[]))] (rc C1) (rc C).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=20%nat). reflexivity.
Qed.

Open Scope N_scope.
Fixpoint Kcap (l : list LB) : N :=
  match l with
  | [] => 0 | U::t => 2*Kcap t+1 | W::t => 2*Kcap t | D::t => Kcap t/2
  end.
Fixpoint Phi (l : list LB) : list RB :=
  match l with
  | [] => [] | U::t | W::t => Phi t ++ [V]
  | D::t => Phi t ++ [if Kcap t mod 2 =? 0 then C else C1]
  end.

(* A decrement is independent of the untouched right context.  Length is
   retained because a D block invokes the shorter left word twice. *)
Lemma left_excursion n : forall l, List.length l = n ->
  (0 < Kcap l -> exists l', List.length l' = List.length l /\
    Kcap l'+1 = Kcap l /\ Phi l' = Phi l /\
    forall r, lt l r -->* gt l' r) /\
  (Kcap l = 0 -> forall r, lt l r -->* lt [] (Phi l ++ r)).
Proof.
  induction n as [|n IH]; intros l Hl.
  - destruct l; [|discriminate]. split.
    + cbn [Kcap]. lia.
    + intros _ r. apply evstep_refl.
  - destruct l as [|b t]; [discriminate|].
    assert (Ht : List.length t = n) by (cbn in Hl; lia).
    destruct b.
    + split.
      * intro HK. assert (Hpos : 0 < Kcap t) by (cbn [Kcap] in HK; lia).
        destruct (proj1 (IH t Ht) Hpos) as [t' [Hlen [Hk [Hp Hr]]]].
        exists (U::t'). repeat split.
        -- cbn. lia.
        -- cbn [Kcap]. lia.
        -- cbn [Phi]. now rewrite Hp.
        -- intro r. follow lt_W. follow (Hr (V::r)). apply gt_V.
      * intro HK. assert (H0 : Kcap t = 0) by (cbn [Kcap] in HK; lia).
        intro r. follow lt_W.
        cbn [Phi]. rewrite <- app_assoc. cbn.
        apply (proj2 (IH t Ht) H0).
    + split.
      * intros _. exists (W::t). split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. intro r. apply lt_U.
      * cbn [Kcap]. lia.
    + split.
      * intro HK. assert (Hpos : 2 <= Kcap t) by (cbn [Kcap] in HK; lia).
        destruct (proj1 (IH t Ht) ltac:(lia)) as [t1 [Hlen1 [Hk1 [Hp1 Hr1]]]].
        assert (Ht1 : List.length t1 = n) by lia.
        destruct (proj1 (IH t1 Ht1) ltac:(lia)) as [t2 [Hlen2 [Hk2 [Hp2 Hr2]]]].
        exists (D::t2). repeat split.
        -- cbn. lia.
        -- cbn [Kcap]. lia.
        -- cbn [Phi]. rewrite Hp2, Hp1.
           assert (He : Kcap t2 mod 2 = Kcap t mod 2) by lia.
           now rewrite He.
        -- intro r. follow lt_D. follow (Hr1 (C::r)). follow gt_C.
           follow (Hr2 (C1::r)). apply gt_C1.
      * intro HK. assert (Hsmall : Kcap t = 0 \/ Kcap t = 1)
          by (cbn [Kcap] in HK; lia).
        destruct Hsmall as [H0|H1]; intro r.
        -- follow lt_D. cbn [Phi]. rewrite H0.
           cbn. rewrite <- app_assoc. cbn.
           apply (proj2 (IH t Ht) H0).
        -- destruct (proj1 (IH t Ht) ltac:(lia)) as [t1 [Hlen1 [Hk1 [Hp1 Hr1]]]].
           assert (Ht1 : List.length t1 = n) by lia.
           assert (H0 : Kcap t1 = 0) by lia.
           follow lt_D. follow (Hr1 (C::r)). follow gt_C.
           cbn [Phi]. rewrite H1. cbn. rewrite <- app_assoc. cbn.
           rewrite <- Hp1. apply (proj2 (IH t1 Ht1) H0).
Qed.

Lemma left_exc_pos l : 0 < Kcap l ->
  exists l', Kcap l'+1 = Kcap l /\ Phi l' = Phi l /\
    forall r, lt l r -->* gt l' r.
Proof.
  intro H. destruct (proj1 (left_excursion (List.length l) l eq_refl) H)
    as [l' [_ H']]. eauto.
Qed.
Lemma left_exc_zero l : Kcap l = 0 ->
  forall r, lt l r -->* lt [] (Phi l ++ r).
Proof. exact (proj2 (left_excursion (List.length l) l eq_refl)). Qed.

Fixpoint cOK (E : N) (w : list RB) : bool :=
  match w with
  | [] => true
  | V::t => cOK (2*E+1) t
  | C1::t => (1 <=? E) && cOK (2*E-1) t
  | C::t => (6 <=? E) && cOK ((E-6)/2) t
  | _ => false
  end.
Fixpoint cCap (E : N) (w : list RB) : N :=
  match w with
  | [] => E
  | V::t => cCap (2*E+1) t
  | C1::t => cCap (2*E-1) t
  | C::t => cCap ((E-6)/2) t
  | _ => E
  end.
Fixpoint cEmit (E : N) (w : list RB) : list RB :=
  match w with
  | [] => []
  | V::t => V :: cEmit (2*E+1) t
  | C1::t => V :: cEmit (2*E-1) t
  | C::t => (if E mod 2 =? 0 then C else C1) :: cEmit ((E-6)/2) t
  | _ => []
  end.

Lemma cascade w : forall l, cOK (Kcap l) w = true ->
  exists l', Kcap l' = cCap (Kcap l) w /\
    Phi l' = Phi l ++ cEmit (Kcap l) w /\
    forall r, wide l (w++r) -->* wide l' r.
Proof.
  induction w as [|b w IH]; intros l Hok.
  - exists l. cbn [cCap cEmit]. rewrite app_nil_r.
    repeat split. intro r. apply evstep_refl.
  - destruct b; cbn [cOK] in Hok; try discriminate.
    + destruct (IH (U::l) Hok) as [l' [Hk [Hp Hr]]].
      exists l'. repeat split.
      * exact Hk.
      * rewrite Hp. cbn [Phi Kcap cEmit]. now rewrite <- app_assoc.
      * intro r. cbn [app]. follow wide_V. apply Hr.
    + apply Bool.andb_true_iff in Hok. destruct Hok as [HE Hok].
      apply N.leb_le in HE.
      destruct (left_exc_pos l ltac:(lia)) as [l1 [k1 [p1 r1]]].
      destruct (left_exc_pos l1 ltac:(lia)) as [l2 [k2 [p2 r2]]].
      destruct (left_exc_pos l2 ltac:(lia)) as [l3 [k3 [p3 r3]]].
      destruct (left_exc_pos l3 ltac:(lia)) as [l4 [k4 [p4 r4]]].
      destruct (left_exc_pos l4 ltac:(lia)) as [l5 [k5 [p5 r5]]].
      destruct (left_exc_pos l5 ltac:(lia)) as [l6 [k6 [p6 r6]]].
      assert (HK : Kcap (D::l6) = (Kcap l-6)/2) by (cbn [Kcap]; f_equal; lia).
      destruct (IH (D::l6) ltac:(now rewrite HK)) as [l' [Hk [Hp Hr]]].
      exists l'. repeat split.
      * now rewrite Hk, HK.
      * rewrite Hp. cbn [Phi]. rewrite p6,p5,p4,p3,p2,p1,HK.
        assert (He : Kcap l6 mod 2 = Kcap l mod 2) by lia.
        rewrite He. cbn [cEmit]. now rewrite <- app_assoc.
      * intro r. cbn [app]. follow wide_C.
        follow (r1 (C::S::w++r)). follow gt_C.
        follow (r2 (C1::S::w++r)). follow gt_C1. follow gt_S. follow lt_D.
        follow (r3 (C::Q::w++r)). follow gt_C.
        follow (r4 (C1::Q::w++r)). follow gt_C1. follow gt_Q. follow lt_D.
        follow (r5 (C::P::w++r)). follow gt_C.
        follow (r6 (C1::P::w++r)). follow gt_C1. follow gt_P.
        apply Hr.
    + apply Bool.andb_true_iff in Hok. destruct Hok as [HE Hok].
      apply N.leb_le in HE.
      destruct (left_exc_pos l ltac:(lia)) as [m [Hm [Hp Hr]]].
      assert (HK : Kcap (U::m) = 2*Kcap l-1) by (cbn [Kcap]; lia).
      destruct (IH (U::m) ltac:(now rewrite HK)) as [l' [Hk [Hp' Hr']]].
      exists l'. repeat split.
      * now rewrite Hk,HK.
      * rewrite Hp'. cbn [Phi]. rewrite Hp,HK.
        cbn [cEmit]. now rewrite <- app_assoc.
      * intro r. cbn [app]. follow wide_C1.
        follow (Hr (P::V::w++r)). follow gt_P. follow wide_V. apply Hr'.
Qed.

(* Binary right counter.  Its recursion is on a positive's representation,
   so even huge finite counters never build a unary natural. *)
Fixpoint encP (p : positive) : list RB :=
  match p with
  | xH => []
  | xO q => match q with xH => [] | _ => C :: encP q end
  | xI q => match q with xH => [P;Q] | _ => C1 :: encP q end
  end.
Definition encR (M : N) : list RB :=
  match M with N0 => [] | Npos p => encP p end.

Lemma right_exc_positive p : p <> xH -> forall l,
  gt l (encP p) -->* lt l (encP (Pos.succ p)).
Proof.
  induction p as [p IH|p IH|]; intros Hp l.
  - destruct p as [p|p|].
    + change (gt l (C1::encP (xI p)) -->*
        lt l (C::encP (Pos.succ (xI p)))).
      follow gt_C1. follow (IH ltac:(discriminate) (D::l)). apply lt_D.
    + change (gt l (C1::encP (xO p)) -->*
        lt l (C::encP (Pos.succ (xO p)))).
      follow gt_C1. follow (IH ltac:(discriminate) (D::l)). apply lt_D.
    + change (gt l [P;Q] -->* lt l [C]). follow gt_P. apply wide_Q.
  - destruct p as [p|p|].
    + change (gt l (C::encP (xI p)) -->* lt l (C1::encP (xI p))). apply gt_C.
    + change (gt l (C::encP (xO p)) -->* lt l (C1::encP (xO p))). apply gt_C.
    + change (gt l [] -->* lt l [P;Q]). apply gt_nil.
  - contradiction.
Qed.

Lemma right_exc M : 2 <= M -> forall l,
  gt l (encR M) -->* lt l (encR (M+1)).
Proof.
  intro HM. destruct M as [|p]; [lia|].
  assert (Hp : p <> xH) by (intro E; subst; lia).
  replace (N.pos p+1) with (N.succ (N.pos p)) by lia.
  apply right_exc_positive. exact Hp.
Qed.

Lemma pair_iter k : forall l M, Kcap l = k -> 2 <= M ->
  lt l (encR M) -->* lt [] (Phi l ++ encR (M+k)).
Proof.
  induction k using N.peano_ind; intros l M HK HM.
  - rewrite N.add_0_r. apply left_exc_zero. exact HK.
  - destruct (left_exc_pos l ltac:(lia)) as [m [Hk [Hp Hr]]].
    follow (Hr (encR M)). follow (right_exc M HM m).
    replace (M+N.succ k) with (M+1+k) by lia.
    rewrite <- Hp. apply IHk; lia.
Qed.

Lemma cgg_phase l : 6 <= Kcap l ->
  lt l [C;G;G] -->* lt [] (Phi l ++ encR (Kcap l+10)).
Proof.
  intro HE.
  destruct (left_exc_pos l ltac:(lia)) as [l1 [k1 [p1 r1]]].
  destruct (left_exc_pos l1 ltac:(lia)) as [l2 [k2 [p2 r2]]].
  destruct (left_exc_pos l2 ltac:(lia)) as [l3 [k3 [p3 r3]]].
  destruct (left_exc_pos l3 ltac:(lia)) as [l4 [k4 [p4 r4]]].
  destruct (left_exc_pos l4 ltac:(lia)) as [l5 [k5 [p5 r5]]].
  destruct (left_exc_pos l5 ltac:(lia)) as [l6 [k6 [p6 r6]]].
  follow (r1 [C;G;G]). follow gt_C.
  follow (r2 [C1;G;G]). follow gt_C1. follow gt_G. follow lt_D.
  follow (r3 [C;C;G]). follow gt_C.
  follow (r4 [C1;C;G]). follow gt_C1. follow gt_C. follow lt_D.
  follow (r5 [C;C1;G]). follow gt_C.
  follow (r6 [C1;C1;G]). follow gt_C1. follow gt_C1. follow gt_G.
  follow lt_D. follow lt_D.
  change (lt l6 (encR 16) -->* lt [] (Phi l ++ encR (Kcap l+10))).
  replace (Kcap l+10) with (16+Kcap l6) by lia.
  rewrite <- p1, <- p2, <- p3, <- p4, <- p5, <- p6.
  apply pair_iter; [reflexivity|lia].
Qed.

Fixpoint pow2 (n : nat) : N :=
  match n with O => 1 | Datatypes.S k => 2*pow2 k end.
Fixpoint compbits (n : nat) (d : N) : list RB :=
  match n with
  | O => []
  | Datatypes.S k => (if d mod 2 =? 0 then C1 else C) :: compbits k (d/2)
  end.

Definition reset (w : list RB) := lt [] (w ++ [P;Q]).

(* Exact operational return, before the binary-complement normalization. *)
Lemma reset_return_raw u : cOK 0 u = true -> 7 <= cCap 0 u ->
  reset (u ++ [C1]) -->+ lt [] (cEmit 0 u ++ encR (cCap 0 u+9)).
Proof.
  intros Hok H7. unfold reset. rewrite <- app_assoc. cbn [app].
  follow10 lt_nil.
  destruct (cascade u [] Hok) as [l [Hk [Hp Hr]]].
  cbn [Kcap Phi] in Hk,Hp.
  follow (Hr [C1;P;Q]).
  destruct (left_exc_pos l ltac:(lia)) as [m [Hm [Hpm Hrm]]].
  follow wide_C1. follow (Hrm [P;V;P;Q]).
  follow gt_P. follow wide_V. follow wide_P. follow gt_Q.
  follow lt_U. follow gt_P.
  follow wide_nil. follow lb_W. follow lb_U.
  follow (cgg_phase m ltac:(lia)).
  rewrite Hpm, Hp. replace (Kcap m+10) with (cCap 0 u+9) by lia.
  apply evstep_refl.
Qed.

Lemma encR_double M : 2 <= M -> encR (2*M) = C::encR M.
Proof.
  intro H. destruct M as [|p]; [lia|].
  change (encP (xO p) = C::encP p).
  destruct p; [reflexivity|reflexivity|exfalso; lia].
Qed.
Lemma encR_double_one M : 2 <= M -> encR (2*M+1) = C1::encR M.
Proof.
  intro H. destruct M as [|p]; [lia|].
  change (encP (xI p) = C1::encP p).
  destruct p; [reflexivity|reflexivity|exfalso; lia].
Qed.
Lemma encR_ge M : 4 <= M ->
  encR M = (if M mod 2 =? 0 then C else C1) :: encR (M/2).
Proof.
  intro H. destruct (N.eqb_spec (M mod 2) 0) as [He|Ho].
  - assert (E : M = 2*(M/2)) by lia.
    rewrite E at 1. apply encR_double. lia.
  - assert (E : M = 2*(M/2)+1) by lia.
    rewrite E at 1. apply encR_double_one. lia.
Qed.
Lemma pow2_pos n : 0 < pow2 n.
Proof. induction n; cbn [pow2]; nia. Qed.
Lemma encR_comp n : forall d, d < pow2 n ->
  encR (4*pow2 n-1-d) = compbits n d ++ [P;Q].
Proof.
  induction n as [|n IH]; intros d Hd.
  - cbn [pow2] in Hd. assert (d=0) by lia. subst. reflexivity.
  - pose proof (pow2_pos n) as HP.
    cbn [pow2] in Hd |- *.
    rewrite encR_ge by lia. cbn [compbits].
    assert (Hq : (4*(2*pow2 n)-1-d)/2 = 4*pow2 n-1-d/2) by lia.
    rewrite Hq, IH by lia.
    destruct (N.eqb_spec (d mod 2) 0) as [He|Ho].
    + assert (Hpar : ((4*(2*pow2 n)-1-d) mod 2 =? 0) = false)
        by (apply N.eqb_neq; lia).
      now rewrite Hpar.
    + assert (Hpar : ((4*(2*pow2 n)-1-d) mod 2 =? 0) = true)
        by (apply N.eqb_eq; lia).
      now rewrite Hpar.
Qed.

Lemma reset_return u n d : cOK 0 u = true -> 7 <= cCap 0 u ->
  d < pow2 n -> cCap 0 u+10+d = 4*pow2 n ->
  reset (u++[C1]) -->+ reset (cEmit 0 u ++ compbits n d).
Proof.
  intros Hok H7 Hd Hnd. unfold reset at 2. rewrite <- app_assoc.
  rewrite <- (encR_comp n d Hd).
  replace (4*pow2 n-1-d) with (cCap 0 u+9) by lia.
  apply reset_return_raw; assumption.
Qed.

(* Normalized debt, always compared after clearing denominators. *)
Fixpoint hs (w : list RB) : Z :=
  match w with
  | [] => 0%Z | V::t | C1::t => (hs t+1)%Z
  | C::t => (hs t-1)%Z | _::t => hs t
  end.
Fixpoint xs (x : N) (w : list RB) : N :=
  match w with
  | [] => x | V::t => xs (2*x) t | C1::t => xs (2*x+2) t
  | C::t => xs (x/2+3) t | _::t => xs x t
  end.
Fixpoint pc (x : N) (w : list RB) : nat :=
  match w with
  | [] => O | V::t => pc (2*x) t | C1::t => pc (2*x+2) t
  | C::t => ((if (x mod 2 =? 0)%N then 1 else 0) + pc ((x/2+3)%N) t)%nat
  | _::t => pc x t
  end.
Fixpoint em (x : N) (w : list RB) : list RB :=
  match w with
  | [] => [] | V::t => V::em (2*x) t | C1::t => V::em (2*x+2) t
  | C::t => (if x mod 2 =? 0 then C1 else C)::em (x/2+3) t
  | _::t => em x t
  end.
Definition Letters (w : list RB) := Forall (fun c => c=V \/ c=C \/ c=C1) w.
Fixpoint pow4 (n : nat) : N :=
  match n with O => 1 | Datatypes.S k => 4*pow4 k end.

Lemma xs_append a : forall x b, xs x (a++b) = xs (xs x a) b.
Proof. induction a as [|c a IH]; intros x b; [reflexivity|destruct c; cbn [xs]; apply IH]. Qed.
Lemma hs_append a b : hs (a++b) = (hs a+hs b)%Z.
Proof. induction a as [|c a IH]; [reflexivity|destruct c; cbn [app hs]; rewrite IH; lia]. Qed.
Lemma pc_append a : forall x b, pc x (a++b) = (pc x a+pc (xs x a) b)%nat.
Proof.
  induction a as [|c a IH]; intros x b; [reflexivity|].
  destruct c; cbn [app pc xs]; rewrite IH; lia.
Qed.
Lemma em_append a : forall x b, em x (a++b) = em x a ++ em (xs x a) b.
Proof.
  induction a as [|c a IH]; intros x b; [reflexivity|].
  destruct c; cbn [app em xs]; rewrite IH; reflexivity.
Qed.
Lemma hs_em a : forall x, hs (em x a) = (hs a+2*Z.of_nat (pc x a))%Z.
Proof.
  induction a as [|c a IH]; intro x; [reflexivity|].
  destruct c; cbn [em pc hs]; try (rewrite IH; lia).
  destruct (x mod 2 =? 0); cbn [hs]; rewrite IH; lia.
Qed.
Lemma letters_em a : forall x, Letters (em x a).
Proof.
  induction a as [|c a IH]; intro x; [constructor|].
  destruct c; cbn [em]; try apply IH;
    constructor; try apply IH; try (unfold Letters; simpl; tauto).
  destruct (x mod 2 =? 0); auto.
Qed.
Lemma letters_compbits n : forall d, Letters (compbits n d).
Proof.
  induction n as [|n IH]; intro d; [constructor|].
  cbn [compbits]. constructor; [destruct (d mod 2 =? 0); auto|apply IH].
Qed.

Lemma pow2_add a b : pow2 (a+b) = pow2 a*pow2 b.
Proof. induction a; cbn [Nat.add pow2]; [lia|rewrite IHa; ring]. Qed.
Lemma pow2_twice n : pow2 (2*n) = pow4 n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (2*Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2*n))) by lia.
  cbn [pow2 pow4]. rewrite IH. ring.
Qed.
Lemma pow4_pos n : 0 < pow4 n.
Proof. induction n; cbn [pow4]; nia. Qed.
Lemma pow2_mono a b : (a<=b)%nat -> pow2 a <= pow2 b.
Proof. intro H. induction H; [lia|cbn [pow2]; nia]. Qed.

Lemma mu_mono w : forall a b x,
  Z.of_nat b = (Z.of_nat a+hs w)%Z -> x*pow2 b <= xs x w*pow2 a.
Proof.
  induction w as [|c w IH]; intros a b x Hb.
  - cbn [hs] in Hb. assert (a=b) by lia. subst. cbn [xs]. lia.
  - destruct c; cbn [xs]; cbn [hs] in Hb.
    + pose proof (IH (Datatypes.S a) b (2*x) ltac:(lia)) as HH.
      cbn [pow2] in HH. nia.
    + pose proof (IH a (Datatypes.S b) (x/2+3) ltac:(lia)) as HH.
      cbn [pow2] in HH. assert (x<=2*(x/2+3)) by lia. nia.
    + pose proof (IH (Datatypes.S a) b (2*x+2) ltac:(lia)) as HH.
      cbn [pow2] in HH. nia.
    + apply IH. exact Hb.
    + apply IH. exact Hb.
    + apply IH. exact Hb.
    + apply IH. exact Hb.
Qed.
Lemma cancel_aux s X p q : 0<p -> s*p<=X*q -> 256*X<=p -> 256*s<=q.
Proof. intros Hp H1 H2. assert (256*X*q<=p*q) by nia. nia. Qed.

Lemma cost_bound n : forall d a b x,
  Z.of_nat b = (Z.of_nat a+hs (compbits n d))%Z ->
  xs x (compbits n d)*pow2 a <= (x+8*d+2)*pow2 b.
Proof.
  induction n as [|n IH]; intros d a b x Hb.
  - cbn [compbits hs] in Hb. assert (a=b) by lia. subst.
    cbn [compbits xs]. nia.
  - cbn [compbits] in Hb |- *.
    destruct (N.eqb_spec (d mod 2) 0) as [He|Ho]; cbn [hs] in Hb; cbn [xs].
    + pose proof (IH (d/2) (Datatypes.S a) b (2*x+2) ltac:(lia)) as HH.
      cbn [pow2] in HH.
      assert (2*x+2+8*(d/2)+2 <= 2*(x+8*d+2)) by lia. nia.
    + pose proof (IH (d/2) a (Datatypes.S b) (x/2+3) ltac:(lia)) as HH.
      cbn [pow2] in HH.
      assert (2*(x/2+3+8*(d/2)+2) <= x+8*d+2) by lia. nia.
Qed.

Lemma cascade_of_debt w : forall h x E H, Letters w ->
  E+1+x=pow2 h -> Z.of_nat H=(Z.of_nat h+hs w)%Z ->
  256*xs x w<=pow2 H ->
  cOK E w=true /\ cEmit E w=em x w /\ cCap E w+1+xs x w=pow2 H.
Proof.
  induction w as [|c w IH]; intros h x E H HL HE HH HX.
  - cbn [hs] in HH. assert (H=h) by lia. subst.
    cbn [cOK cEmit em cCap xs]. auto.
  - inversion HL as [|? ? Hc HLw]; subst.
    destruct c; try (destruct Hc as [Hc|[Hc|Hc]]; discriminate);
      cbn [hs] in HH; cbn [xs] in HX.
    + destruct (IH (Datatypes.S h) (2*x) (2*E+1) H HLw
        ltac:(cbn [pow2]; lia) ltac:(lia) HX) as [H1 [H2 H3]].
      cbn [cOK cEmit em cCap xs]. rewrite H1,H2. auto.
    + pose proof (mu_mono w h (Datatypes.S H) (x/2+3) ltac:(lia)) as HM.
      cbn [pow2] in HM.
      assert (HB : 256*(2*(x/2+3))<=pow2 h).
      { apply (cancel_aux _ (xs (x/2+3) w) (pow2 H) (pow2 h));
          [apply pow2_pos|nia|exact HX]. }
      destruct h as [|h]; [cbn [pow2] in HB; lia|].
      cbn [pow2] in HB,HE.
      assert (H6 : 6<=E) by lia.
      destruct (IH h (x/2+3) ((E-6)/2) H HLw ltac:(lia) ltac:(lia) HX)
        as [H1 [H2 H3]].
      assert (H6b : (6<=?E)=true) by (apply N.leb_le; exact H6).
      cbn [cOK cEmit em cCap xs]. rewrite H6b,H1,H2. cbn [andb].
      split; [reflexivity|]. split; [|exact H3]. f_equal.
      destruct (N.eqb_spec (E mod 2) 0), (N.eqb_spec (x mod 2) 0); try reflexivity; exfalso; lia.
    + pose proof (mu_mono w (Datatypes.S h) H (2*x+2) ltac:(lia)) as HM.
      pose proof (cancel_aux _ _ _ _ (pow2_pos H) HM HX) as HB.
      cbn [pow2] in HB. assert (H1E : 1<=E) by lia.
      destruct (IH (Datatypes.S h) (2*x+2) (2*E-1) H HLw
        ltac:(cbn [pow2]; lia) ltac:(lia) HX) as [H1 [H2 H3]].
      assert (H1b : (1<=?E)=true) by (apply N.leb_le; exact H1E).
      cbn [cOK cEmit em cCap xs]. rewrite H1b,H1,H2. auto.
Qed.

Definition Iinv (x y : N) (p : nat) :=
  (p=O /\ y=0 /\ x mod 2=0) \/ ((1<=p)%nat /\ y<=pow4 (p-1)*x).

Lemma image_bound w : forall x y p, Iinv x y p ->
  Iinv (xs x w) (xs y (em x w)) (p+pc x w).
Proof.
  induction w as [|c w IH]; intros x y p HI.
  - cbn [xs em pc]. rewrite Nat.add_0_r. exact HI.
  - destruct c; cbn [xs em pc]; try (apply IH; exact HI).
    + apply IH. unfold Iinv in HI |- *. destruct HI as [[Hp [Hy Hx]]|[Hp Hy]].
      * left. repeat split; lia.
      * right. split; [exact Hp|nia].
    + destruct (N.eqb_spec (x mod 2) 0) as [He|Ho]; cbn [xs].
      * replace (p+(1+pc (x/2+3) w))%nat with (Datatypes.S p+pc (x/2+3) w)%nat by lia.
        apply IH. right. split; [lia|].
        replace (Datatypes.S p-1)%nat with p by lia.
        unfold Iinv in HI. destruct HI as [[Hp [Hy Hx]]|[Hp Hy]].
        -- subst p y. cbn [pow4]. lia.
        -- destruct p as [|p]; [lia|].
           replace (Datatypes.S p-1)%nat with p in Hy by lia.
           cbn [pow4]. pose proof (pow4_pos p). nia.
      * cbn [Nat.add]. apply IH. right.
        unfold Iinv in HI. destruct HI as [[Hp [Hy Hx]]|[Hp Hy]]; [contradiction|].
        split; [exact Hp|]. pose proof (pow4_pos (p-1)). nia.
    + apply IH. unfold Iinv in HI |- *. destruct HI as [[Hp [Hy Hx]]|[Hp Hy]].
      * left. repeat split; lia.
      * right. split; [exact Hp|nia].
Qed.

Lemma compbits_add a : forall b d,
  compbits (a+b) d = compbits a d ++ compbits b (d/pow2 a).
Proof.
  induction a as [|a IH]; intros b d.
  - cbn [Nat.add compbits pow2]. now rewrite N.div_1_r.
  - cbn [Nat.add compbits pow2]. rewrite IH. cbn [app]. f_equal. f_equal.
    rewrite N.div_div by (pose proof (pow2_pos a); lia). reflexivity.
Qed.
Lemma compbits_zero n : compbits n 0 = repeat C1 n.
Proof.
  induction n; [reflexivity|].
  change (C1::compbits n 0=C1::repeat C1 n). now rewrite IHn.
Qed.
Lemma hs_compbits_ge n : forall d, (-Z.of_nat n <= hs (compbits n d))%Z.
Proof.
  induction n as [|n IH]; intro d; [cbn [compbits hs]; lia|].
  pose proof (IH (d/2)). cbn [compbits]. destruct (d mod 2 =? 0); cbn [hs]; lia.
Qed.
Lemma xs_rep n : forall x, xs x (repeat C1 n)+2=(x+2)*pow2 n.
Proof.
  induction n as [|n IH]; intro x; cbn [repeat xs pow2]; [lia|].
  rewrite IH. ring.
Qed.
Lemma pc_prom_five y : y mod 2=0 -> (3<=pc y [C;C1;C;C1;C])%nat.
Proof.
  intro Hy. cbn [pc]. rewrite Hy. cbn [N.eqb].
  assert (H1 : ((2*(y/2+3)+2) mod 2 =? 0)=true) by (apply N.eqb_eq; lia).
  rewrite H1.
  assert (H2 : ((2*((2*(y/2+3)+2)/2+3)+2) mod 2 =? 0)=true)
    by (apply N.eqb_eq; lia).
  rewrite H2. lia.
Qed.

(* Only the five low bits are needed for the promotion lower bound. *)
Lemma compbits_prom d : d mod 32=21 -> compbits 5 d = [C;C1;C;C1;C].
Proof.
  intro Hd. cbn [compbits].
  assert (H0 : (d mod 2 =? 0)=false) by (apply N.eqb_neq; lia).
  assert (H1 : ((d/2) mod 2 =? 0)=true) by (apply N.eqb_eq; lia).
  assert (H2 : ((d/2/2) mod 2 =? 0)=false) by (apply N.eqb_neq; lia).
  assert (H3 : ((d/2/2/2) mod 2 =? 0)=true) by (apply N.eqb_eq; lia).
  assert (H4 : ((d/2/2/2/2) mod 2 =? 0)=false) by (apply N.eqb_neq; lia).
  now rewrite H0,H1,H2,H3,H4.
Qed.

Record Inv (w : list RB) : Prop := {
  inv_letters : Letters w;
  inv_tail : exists v, w=v++repeat C1 6;
  inv_prom : (3<=pc 0 w)%nat;
  inv_debt : exists H, Z.of_nat H=hs w /\ 256*xs 0 w<=pow2 H
}.

Lemma inv_step w : Inv w -> exists w', Inv w' /\ reset w -->+ reset w'.
Proof.
  intros [HL [v Ew] HP [H [HH HX]]]. subst w.
  set (u := v++repeat C1 5).
  assert (Ew : v++repeat C1 6=u++[C1])
    by (unfold u; rewrite <- app_assoc; reflexivity).
  rewrite Ew in HL,HP,HH,HX |- *.
  assert (HLu : Letters u) by (apply Forall_app in HL; tauto).
  set (z := xs 0 u). set (p := pc 0 u).
  assert (HXw : xs 0 (u++[C1])=2*z+2) by (rewrite xs_append; reflexivity).
  assert (HHw : hs (u++[C1])=(hs u+1)%Z) by (rewrite hs_append; reflexivity).
  assert (HPw : pc 0 (u++[C1])=p) by (rewrite pc_append; cbn [pc]; lia).
  rewrite HXw in HX. rewrite HHw in HH. rewrite HPw in HP.
  assert (HZ32 : z+2=(xs 0 v+2)*32).
  { unfold z,u. rewrite xs_append. exact (xs_rep 5 (xs 0 v)). }
  destruct H as [|h]; [cbn [pow2] in HX; lia|].
  cbn [pow2] in HX.
  assert (HB : 256*(z+1)<=pow2 h) by lia.
  destruct (cascade_of_debt u O 0 0 h HLu eq_refl ltac:(lia) ltac:(unfold z in HB; lia))
    as [HOK [HEmit HCap]]. fold z in HCap.
  assert (H14 : (14<=h)%nat).
  { destruct (le_dec 14 h); [assumption|].
    pose proof (pow2_mono h 13 ltac:(lia)) as HH13.
    change (pow2 h<=8192) in HH13. lia. }
  set (n := (h-2)%nat). set (m := (n-6)%nat).
  assert (Hhn : h=(n+2)%nat) by (unfold n; lia).
  assert (Hnm : n=(m+6)%nat) by (unfold m,n in *; lia).
  assert (HPn : pow2 h=4*pow2 n) by (rewrite Hhn,pow2_add; cbn [pow2]; ring).
  assert (HPm : pow2 n=64*pow2 m) by (rewrite Hnm,pow2_add; change (pow2 m*64=64*pow2 m); ring).
  set (d := z-9).
  assert (HdM : d<pow2 m) by (unfold d; lia).
  assert (HdN : d<pow2 n) by lia.
  assert (H7 : 7<=cCap 0 u) by lia.
  assert (Hnd : cCap 0 u+10+d=4*pow2 n) by (unfold d; lia).
  pose proof (reset_return u n d HOK H7 HdN Hnd) as HR.
  exists (cEmit 0 u++compbits n d). split; [|exact HR].
  rewrite HEmit. set (y := xs 0 (em 0 u)).
  assert (HyEven : y mod 2=0).
  { assert (Hu : u=(v++repeat C1 4)++[C1])
      by (unfold u; rewrite <- app_assoc; reflexivity).
    unfold y. rewrite Hu,em_append,xs_append. cbn [em xs]. lia. }
  pose proof (image_bound u 0 0 O ltac:(left; repeat split; reflexivity)) as HI.
  change (Iinv z y p) in HI.
  assert (HyZ : y<=pow4 (p-1)*z).
  { unfold Iinv in HI. destruct HI as [[Hp0 _]|[_ Hy]]; [lia|exact Hy]. }
  pose proof (hs_em u 0) as HHE. fold p in HHE.
  constructor.
  - unfold Letters. apply Forall_app. split; [apply letters_em|apply letters_compbits].
  - exists (em 0 u++compbits m d).
    rewrite Hnm,compbits_add. rewrite (N.div_small d (pow2 m) HdM),compbits_zero.
    now rewrite app_assoc.
  - assert (HN5 : n=(5+(n-5))%nat) by (unfold n; lia).
    assert (Hd32 : d mod 32=21) by (unfold d; lia).
    rewrite HN5,compbits_add,app_assoc,pc_append,xs_append.
    rewrite pc_append,(compbits_prom d Hd32).
    pose proof (pc_prom_five y HyEven) as HPfive. unfold y in HPfive. lia.
  - pose proof (hs_compbits_ge n d) as Hge.
    set (height := (Z.of_nat (h+2*p)+hs (compbits n d))%Z).
    assert (Hheight : (0<=height)%Z) by (unfold height; lia).
    exists (Z.to_nat height). split.
    + rewrite Z2Nat.id by exact Hheight.
      rewrite hs_append,HHE. unfold height. lia.
    + pose proof (cost_bound n d (h+2*p)%nat (Z.to_nat height) y
        ltac:(rewrite Z2Nat.id by exact Hheight; reflexivity)) as HC.
      rewrite xs_append. fold y.
      assert (Hkey : 256*(y+8*d+2)<=pow2 (h+2*p)).
      { rewrite pow2_add,pow2_twice.
        assert (H4 : pow4 p=4*pow4 (p-1)).
        { destruct p; [lia|]. replace (Datatypes.S p-1)%nat with p by lia. reflexivity. }
        assert (H16 : 16<=pow4 (p-1)).
        { destruct p as [|[|[|q]]]; try lia.
          replace (Datatypes.S (Datatypes.S (Datatypes.S q))-1)%nat with
            (Datatypes.S (Datatypes.S q)) by lia.
          cbn [pow4]. pose proof (pow4_pos q). nia. }
        rewrite H4.
        assert (HZ : y+8*d+2 <= (z+1)*(4*pow4 (p-1))) by (unfold d; nia).
        assert (HM : 256*(z+1)*(4*pow4 (p-1)) <= pow2 h*(4*pow4 (p-1)))
          by (apply N.mul_le_mono_r; exact HB).
        clear - HZ HM. nia. }
      eapply cancel_aux; [apply pow2_pos|exact HC|exact Hkey].
Qed.

(* Compact bootstrap: the first body is short, later bodies are generated
   by the proved return map. No expanded 50-letter seed is stored. *)
Definition u8 : list RB := repeat V 6 ++ [C1;C;C1].
Definition u9 := removelast (cEmit 0 u8 ++ compbits 5 1).
Definition u10 := removelast (cEmit 0 u9 ++ compbits 9 45).
Definition u11 := removelast (cEmit 0 u10 ++ compbits 11 53).
Definition w12 := cEmit 0 u11 ++ compbits 19 693.

(* The source bootstrap's initial 21 raw steps and following 504 block
   steps total 1094 raw steps. BusyCoq checks the raw run directly. *)
Lemma initial_reset : c0 -->* reset (u8++[C1]).
Proof.
  apply evstep_c_spec. exists 1094%nat. vm_compute. reflexivity.
Qed.

Lemma boot_step u n d :
  cOK 0 u=true /\ 7<=cCap 0 u /\ d<pow2 n /\ cCap 0 u+10+d=4*pow2 n ->
  reset (u++[C1]) -->* reset (cEmit 0 u++compbits n d).
Proof.
  intros [H1 [H2 [H3 H4]]]. apply progress_evstep.
  apply reset_return; assumption.
Qed.
Ltac finite_check := vm_compute; repeat split; congruence.

Lemma reach_w12 : c0 -->* reset w12.
Proof.
  follow initial_reset.
  follow (boot_step u8 5 1 ltac:(finite_check)).
  assert (E9 : cEmit 0 u8++compbits 5 1=u9++[C1]) by reflexivity.
  rewrite E9.
  follow (boot_step u9 9 45 ltac:(finite_check)).
  assert (E10 : cEmit 0 u9++compbits 9 45=u10++[C1]) by reflexivity.
  rewrite E10.
  follow (boot_step u10 11 53 ltac:(finite_check)).
  assert (E11 : cEmit 0 u10++compbits 11 53=u11++[C1]) by reflexivity.
  rewrite E11.
  exact (boot_step u11 19 693 ltac:(finite_check)).
Qed.

Lemma inv_w12 : Inv w12.
Proof.
  constructor.
  - unfold Letters. vm_compute. repeat (constructor; [auto|]). constructor.
  - exists (firstn 44 w12). reflexivity.
  - vm_compute. lia.
  - exists 36%nat. finite_check.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact reach_w12|].
  apply (@progress_nonhalt_cond tm (list RB) w12 reset Inv).
  - intros w Hw. destruct (inv_step w Hw) as [w' [HI HR]].
    exists w'. auto.
  - exact inv_w12.
Qed.


End TM38.


Close Scope Q_scope. Close Scope Z_scope. Close Scope N_scope.
Close Scope nat_scope. Open Scope sym_scope.
Set Default Goal Selector "1".

(* Machine 54. *)
From BusyCoq Require Import Individual25.
From Coq Require Import Lia PeanoNat List String NArith ZifyNat.
Import ListNotations.

(** BB(2,5), number 54.  Only the original machine is defined here.
    The finite right-hand transducer is expressed directly with BusyCoq's
    segment/call relations; no private tape or reachability library is used. *)
Module TM54.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB---4LA_1LA3LA1RA4RA1LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation h := (A, ([] : list Sym)).
Notation sig := (h,h).
Definition carries n r r' := sideRLs tm ([sig]^^n) r r'.
Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=40); reflexivity.

Lemma wall_rule : segRLs tm [sig] [] [4] [4].
Proof. finite_rule. Qed.
Lemma one_two_rule : segRLs tm [sig] [] [1;2] [2;2].
Proof. finite_rule. Qed.
Lemma one_four_rule : segRLs tm [sig] [] [1;4] [2;4].
Proof. finite_rule. Qed.
Lemma double_rule : segRLs tm [sig] [sig;sig] [2;2] [2;2].
Proof. finite_rule. Qed.
Lemma digit0_rule : segRLs tm [sig] [] [2;4] [1;1].
Proof. finite_rule. Qed.
Lemma digit1_rule : segRLs tm [sig] [] [1;1] [2;1].
Proof. finite_rule. Qed.
Lemma digit2_rule : segRLs tm [sig] [sig] [2;1] [2;4].
Proof. finite_rule. Qed.

Lemma carries_zero r : carries 0 r r.
Proof. constructor. Qed.
Lemma carries_add a b r u v :
  carries a r u -> carries b u v -> carries (a+b) r v.
Proof. unfold carries; rewrite lpow_add; apply sideRLs_trans. Qed.
Lemma carries_split a b r v : carries (a+b) r v ->
  exists u, carries a r u /\ carries b u v.
Proof. unfold carries; rewrite lpow_add; apply sideRLs_split. Qed.

Lemma carries_wall n r : carries n (4 >> r) (4 >> r).
Proof.
  induction n; [constructor|].
  change (carries (1+n) (4 >> r) (4 >> r)).
  eapply carries_add; [|exact IHn].
  exact (segRLs_sideRLs_concat wall_rule (sideRLseq_O tm r)).
Qed.

Lemma carries_double n r r' : carries (2*n) r r' ->
  carries n (2 >> 2 >> r) (2 >> 2 >> r').
Proof.
  unfold carries; intro H.
  pose proof (segRLs_wall'' (n:=n) double_rule) as Hrule.
  change ([sig;sig]) with ([sig]^^2) in Hrule.
  rewrite <-lpow_mul, Nat.mul_comm in Hrule.
  exact (segRLs_sideRLs_concat Hrule H).
Qed.

Inductive digit := d0 | d1 | d2.
Definition enc_digit d : list Sym :=
  match d with d0 => [2;4] | d1 => [1;1] | d2 => [2;1] end.
Fixpoint ternary (ds:list digit) : side :=
  match ds with [] => 0inf | d::ds => enc_digit d *> ternary ds end.

Lemma carry_ternary ds : exists ds', carries 1 (ternary ds) (ternary ds').
Proof.
  induction ds as [|d ds [ds' H]].
  - exists [d2]. unfold carries, ternary; cbn.
    apply sideRL_1; intro l; start_progress.
  - destruct d.
    + exists (d1::ds).
      exact (segRLs_sideRLs_concat digit0_rule (sideRLseq_O tm (ternary ds))).
    + exists (d2::ds).
      exact (segRLs_sideRLs_concat digit1_rule (sideRLseq_O tm (ternary ds))).
    + exists (d0::ds').
      exact (segRLs_sideRLs_concat digit2_rule H).
Qed.

Lemma carries_ternary n ds : exists ds', carries n (ternary ds) (ternary ds').
Proof.
  revert ds; induction n; intro ds.
  - exists ds; constructor.
  - destruct (carry_ternary ds) as [u H].
    destruct (IHn u) as [v H']; exists v.
    exact (carries_add 1 n _ _ _ H H').
Qed.

Lemma digit0_three : segRLs tm ([sig]^^3) [sig] [2;4] [2;4].
Proof. finite_rule. Qed.

Lemma carries_digit0_three n r r' : carries n r r' ->
  carries (3*n) (2 >> 4 >> r) (2 >> 4 >> r').
Proof.
  unfold carries; intro H.
  pose proof (segRLs_wall'' (n:=n) digit0_three) as Hrule.
  rewrite <-lpow_mul, Nat.mul_comm in Hrule.
  exact (segRLs_sideRLs_concat Hrule H).
Qed.

(** A doubled block before a wall absorbs any number of calls. *)
Lemma even_twos_wall b n r :
  carries n ([2]^^(2*b) *> 4 >> r) ([2]^^(2*b) *> 4 >> r).
Proof.
  revert n; induction b; intro n.
  - apply carries_wall.
  - replace (2*S b) with (2+2*b) by lia.
    rewrite lpow_add; cbn [lpow app Str_app].
    apply carries_double; apply IHb.
Qed.

(** A doubled block before a ternary zero preserves that zero on 3n calls. *)
Lemma even_twos_digit b n ds : exists ds',
  carries (3*n) ([2]^^(2*b) *> 2 >> 4 >> ternary ds)
    ([2]^^(2*b) *> 2 >> 4 >> ternary ds').
Proof.
  revert n; induction b; intro n.
  - destruct (carries_ternary n ds) as [ds' H].
    exists ds'; apply carries_digit0_three; exact H.
  - destruct (IHb (2*n)) as [ds' H]; exists ds'.
    replace (2*S b) with (2+2*b) by lia.
    rewrite lpow_add; cbn [lpow app Str_app].
    apply carries_double.
    replace (2*(3*n)) with (3*(2*n)) by lia; exact H.
Qed.

Lemma twos_preserve_three a t ds : exists ds',
  carries (3*t) ([2]^^a *> 4 >> ternary ds)
    ([2]^^a *> 4 >> ternary ds').
Proof.
  destruct (Nat.Even_or_Odd a) as [[b E]|[b E]]; subst a.
  - exists ds; apply even_twos_wall.
  - destruct (even_twos_digit b t ds) as [ds' H]; exists ds'.
    rewrite lpow_add, !Str_app_assoc; cbn [lpow app Str_app]; exact H.
Qed.

(** One call consumes the leading 1; further groups of three preserve the
    shifted delimiter, regardless of the parity of the run of 2s. *)
Lemma offset_loop a t ds : exists ds',
  carries (3*t+1) (1 >> [2]^^a *> 4 >> ternary ds)
    ([2]^^(a+1) *> 4 >> ternary ds').
Proof.
  destruct (twos_preserve_three (S a) t ds) as [ds' H]; exists ds'.
  replace (a+1) with (S a) by lia.
  replace (3*t+1) with (1+3*t) by lia.
  eapply carries_add; [|exact H].
  destruct a; cbn [lpow app Str_app].
  - exact (segRLs_sideRLs_concat one_four_rule (sideRLseq_O tm (ternary ds))).
  - exact (segRLs_sideRLs_concat one_two_rule
      (sideRLseq_O tm ([2]^^a *> 4 >> ternary ds))).
Qed.

(** The congruence is proved symbolically; no large natural is evaluated. *)
Lemma loop_power s : exists t, (2^(6*s+2) = 18*t+4)%nat.
Proof.
  induction s as [|s [t H]].
  - exists 0%nat; reflexivity.
  - exists (64*t+14)%nat.
    replace (6*S s+2)%nat with (6*s+2+6)%nat by lia.
    rewrite Nat.pow_add_r, H; cbn [Nat.pow]; nia.
Qed.

(** Left-hand binary counter, nearest cell first. *)
Definition bit (b:bool) : list Sym := [if b then 1 else 0;1].
Definition bits bs := flat_map bit bs.
Definition event m r := 0inf {{A}}> 0 >> [2]^^m *> r.
Definition bconfig bs (r:side) := 0inf << 1 <* bits bs {{B}}> r.
Definition mconfig bs (r:side) := 0inf << 1 <* bits bs << 1 {{A}}> r.

Lemma sweep_right n l r :
  l {{B}}> [2]^^(2*n) *> r -->* l <* [0;1]^^n {{B}}> r.
Proof.
  rewrite Nat.mul_comm, lpow_mul.
  apply (shift_rule_R []); execute.
Qed.

Lemma sweep_left n l r :
  l <* [1]^^n <{{A}} r -->* l <{{A}} [2]^^n *> r.
Proof.
  apply (shift_rule_L []); execute.
Qed.

Lemma bits_false n : bits ([false]^^n) = [0;1]^^n.
Proof. unfold bits; rewrite flat_map_lpow; reflexivity. Qed.
Lemma bits_true n : bits ([true]^^n) = [1]^^(2*n).
Proof.
  unfold bits; rewrite flat_map_lpow.
  rewrite Nat.mul_comm, lpow_mul; reflexivity.
Qed.
Lemma bits_app a b : bits (a++b) = bits a ++ bits b.
Proof. apply flat_map_app. Qed.

Lemma event_even n r : event (2*n) r -->* bconfig ([false]^^n) r.
Proof.
  unfold event, bconfig; rewrite bits_false.
  eapply evstep_step; [prove_step|].
  change (0inf << 1 {{B}}> [2]^^(2*n) *> r -->*
    0inf << 1 <* [0;1]^^n {{B}}> r).
  apply sweep_right.
Qed.
Lemma event_odd n r : event (2*n+1) r -->* mconfig ([false]^^n) r.
Proof.
  unfold event, mconfig; rewrite bits_false, lpow_add.
  rewrite Str_app_assoc; cbn [lpow app Str_app].
  eapply evstep_step; [prove_step|].
  change (0inf << 1 {{B}}> [2]^^(2*n) *> 2 >> r -->*
    0inf << 1 <* [0;1]^^n << 1 {{A}}> r).
  follow sweep_right; execute.
Qed.

Lemma b_two bs r : bconfig bs (2 >> r) -->* mconfig bs r.
Proof. unfold bconfig, mconfig; execute. Qed.
Lemma m_two bs r : mconfig bs (2 >> r) -->* bconfig (false::bs) r.
Proof. unfold bconfig, mconfig, bits, bit; execute. Qed.

Definition blocked bs r := mconfig bs (4 >> r).

(** A higher binary counter is used only through A-left/B-right calls.
    Keeping the lowest bit in the driver avoids a separate numeric bitsOf
    library and all of its arithmetic representation lemmas. *)
Notation ih := (B, ([] : list Sym)).
Notation isig := (h,ih).
Definition left_calls n l l' := sideRLs (flip tm) ([isig]^^n) l l'.

Lemma binary_zero : segRLs (flip tm) [isig] [] [0;1] [1;1].
Proof. finite_rule. Qed.
Lemma binary_one : segRLs (flip tm) [isig] [isig] [1;1] [0;1].
Proof. finite_rule. Qed.
Lemma binary_pair : segRLs (flip tm) [isig;isig] [isig] [0;1] [0;1].
Proof. finite_rule. Qed.

Lemma binary_low k :
  segRLs (flip tm) ([isig]^^(2*k+1)) ([isig]^^k) [0;1] [1;1].
Proof.
  rewrite lpow_add.
  replace ([isig]^^k) with ([isig]^^k ++ []) by apply app_nil_r.
  eapply segRLs_trans; [|exact binary_zero].
  pose proof (segRLs_wall'' (n:=k) binary_pair) as H.
  change ([isig;isig]) with ([isig]^^2) in H.
  rewrite <-lpow_mul, Nat.mul_comm in H; exact H.
Qed.

Lemma binary_count k :
  segRLs (flip tm) ([isig]^^(2^k-1)) [] ([0;1]^^k) ([1;1]^^k).
Proof.
  induction k as [|k IH]; [constructor|].
  assert (Hpos : (2^k <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  replace (2^S k-1)%nat with (2*(2^k-1)+1)%nat by (cbn [Nat.pow]; lia).
  cbn [lpow].
  eapply segRLs_concat; [apply binary_low|exact IH].
Qed.

Lemma left_calls_split a b l l' : left_calls (a+b) l l' ->
  exists m, left_calls a l m /\ left_calls b m l'.
Proof. unfold left_calls; rewrite lpow_add; apply sideRLs_split. Qed.

Lemma left_call l l' r : left_calls 1 l l' ->
  l <{{A}} r -->+ l' {{B}}> r.
Proof.
  unfold left_calls; cbn [lpow app]; intro H.
  inversion H as [|h1 h2 r1 r2 r3 ls HC HS]; subst.
  inversion HS; subst.
  apply (to_DH_config_progress_unflip (HC r)).
Qed.

Lemma right_call l r r' : carries 1 r r' ->
  l {{A}}> r -->+ l <{{A}} r'.
Proof.
  unfold carries; cbn [lpow app]; intro H.
  inversion H as [|h1 h2 r1 r2 r3 ls HC HS]; subst.
  inversion HS; subst; apply HC.
Qed.

Lemma driver_one l l' r r' :
  left_calls 1 l l' -> carries 1 r r' ->
  l << 1 << 0 {{B}}> 1 >> r -->* l' << 1 << 0 {{B}}> 4 >> r'.
Proof.
  intros Hl Hr.
  step; step; step.
  follow100 (right_call (l << 1 << 1 << 4) r r' Hr).
  step; step; step.
  follow100 (left_call l l' (2 >> 2 >> 4 >> r') Hl).
  execute.
Qed.

Lemma driver_four l l' r : left_calls 2 l l' ->
  l << 1 << 0 {{B}}> 4 >> r -->* l' << 1 << 0 {{B}}> 1 >> r.
Proof.
  intro H; destruct (left_calls_split 1 1 _ _ H) as [u [H1 H2]].
  step; step; step.
  follow100 (left_call l u (2 >> 1 >> 1 >> r) H1).
  step; step; step.
  follow100 (left_call u l' (2 >> 2 >> 1 >> r) H2).
  execute.
Qed.

Lemma driver_rounds j l l' r r' :
  left_calls (3*j) l l' -> carries j r r' ->
  l << 1 << 0 {{B}}> 4 >> r -->* l' << 1 << 0 {{B}}> 4 >> r'.
Proof.
  revert l l' r r'; induction j; intros l l' r r' Hl Hr.
  - inversion Hl; inversion Hr; subst; finish.
  - replace (3*S j) with (2+(1+3*j)) in Hl by lia.
    destruct (left_calls_split 2 (1+3*j) _ _ Hl) as [u [H2 Hu]].
    destruct (left_calls_split 1 (3*j) _ _ Hu) as [v [H1 Hv]].
    destruct (carries_split 1 j _ _ Hr) as [w [HR Hw]].
    follow (driver_four l u r H2).
    follow (driver_one _ _ _ _ H1 HR).
    apply IHj; assumption.
Qed.

Lemma driver_start j l l' r r' :
  left_calls (1+3*j) l l' -> carries (j+1) r r' ->
  l << 1 << 0 {{B}}> 1 >> r -->* l' << 1 << 0 {{B}}> 4 >> r'.
Proof.
  intros Hl Hr.
  destruct (left_calls_split 1 (3*j) _ _ Hl) as [u [H1 Hu]].
  replace (j+1) with (1+j) in Hr by lia.
  destruct (carries_split 1 j _ _ Hr) as [v [HR Hv]].
  follow (driver_one _ _ _ _ H1 HR).
  apply (driver_rounds j); assumption.
Qed.

Lemma four_exit l r :
  l << 1 << 0 {{B}}> 4 >> r -->+ l <{{A}} 2 >> 1 >> 1 >> r.
Proof. start_progress. Qed.

Lemma ones_pairs k : ([1;1]^^k : list Sym) = [1]^^(2*k).
Proof. rewrite Nat.mul_comm, lpow_mul; reflexivity. Qed.

Lemma driver_overflow k r :
  0inf << 1 <* [1;1]^^k << 1 << 0 {{B}}> 4 >> r -->*
  event (2*k+2) (1 >> 1 >> r).
Proof.
  follow100 (four_exit (0inf << 1 <* [1;1]^^k) r).
  rewrite ones_pairs.
  replace (0inf << 1 <* [1]^^(2*k)) with (0inf <* [1]^^(2*k+1)).
  2: rewrite lpow_add, Str_app_assoc; reflexivity.
  follow sweep_left.
  unfold event; rewrite !lpow_add, !Str_app_assoc.
  apply evstep_refl'; reflexivity.
Qed.

Lemma event_even_progress n r :
  event (2*n) r -->+ bconfig ([false]^^n) r.
Proof.
  unfold event, bconfig; rewrite bits_false.
  eapply progress_intro; [prove_step|].
  change (0inf << 1 {{B}}> [2]^^(2*n) *> r -->*
    0inf << 1 <* [0;1]^^n {{B}}> r).
  apply sweep_right.
Qed.

(** The full symbolic loop: six extra binary bits multiply the capacity
    by 64, while every three higher-counter calls send one right carry. *)
Lemma loop_step s a ds : exists ds',
  event (2*(6*s+2)) (1 >> 1 >> [2]^^a *> 4 >> ternary ds) -->+
  event (2*(6*s+2)) (1 >> 1 >> [2]^^(a+1) *> 4 >> ternary ds').
Proof.
  destruct (loop_power s) as [t Hpow].
  destruct (offset_loop a t ds) as [ds' Hr]; exists ds'.
  set (p := (6*s+1)%nat).
  assert (Hp : (6*s+2 = S p)%nat) by (unfold p; lia).
  assert (Hcount : (2^p-1 = 1+3*(3*t))%nat).
  { rewrite Hp in Hpow; cbn [Nat.pow] in Hpow; lia. }
  pose proof (segRLs_sideRLs_concat (binary_count p)
    (sideRLseq_O (flip tm) (0inf << 1))) as Hl.
  change (left_calls (2^p-1) (0inf << 1 <* [0;1]^^p)
    (0inf << 1 <* [1;1]^^p)) in Hl.
  rewrite Hcount in Hl.
  follow10 event_even_progress.
  unfold bconfig; rewrite bits_false, Hp; cbn [lpow app Str_app].
  follow (driver_start (3*t) _ _ _ _ Hl Hr).
  replace (2*S p) with (2*p+2) by lia.
  apply driver_overflow.
Qed.

Lemma loop_nonhalt s a ds :
  ~halts tm (event (2*(6*s+2)) (1 >> 1 >> [2]^^a *> 4 >> ternary ds)).
Proof.
  eapply progress_nonhalt with
    (P:=fun c => exists a ds,
      c = event (2*(6*s+2)) (1 >> 1 >> [2]^^a *> 4 >> ternary ds)).
  - intros c [a0 [ds0 E]]; subst c.
    destruct (loop_step s a0 ds0) as [ds1 H].
    eexists; split; [|exact H].
    exists (a0+1)%nat, ds1; reflexivity.
  - exists a, ds; reflexivity.
Qed.

(** The first finite checkpoint is deliberately small.  Later macro
    checkpoints must not be expanded as unary values of 2^50. *)
Lemma init_681 : c0 -->* event 13 (4 >> ternary [d0;d2;d2]).
Proof.
  apply evstep_c_spec; exists 681.
  vm_compute; reflexivity.
Qed.

(** General finite-reader interface for the remaining initialization.
    Counts have a binary executable representation and a separate natural
    interpretation used only by the relational proofs. *)
Fixpoint capacity (bs:list bool) : N :=
  match bs with
  | [] => 0%N
  | b::bs => if b then (2*capacity bs)%N else (2*capacity bs+1)%N
  end.
Fixpoint capacity_nat (bs:list bool) : nat :=
  match bs with
  | [] => 0%nat
  | b::bs => if b then (2*capacity_nat bs)%nat else (2*capacity_nat bs+1)%nat
  end.
Lemma capacity_correct bs : N.to_nat (capacity bs) = capacity_nat bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  destruct b; cbn [capacity capacity_nat];
    rewrite ?N2Nat.inj_add, N2Nat.inj_mul, IH; reflexivity.
Qed.

Lemma binary_high k :
  segRLs (flip tm) ([isig]^^(2*k)) ([isig]^^k) [1;1] [1;1].
Proof.
  assert (H : segRLs (flip tm) [isig;isig] [isig] [1;1] [1;1]) by finite_rule.
  pose proof (segRLs_wall'' (n:=k) H) as H'.
  change ([isig;isig]) with ([isig]^^2) in H'.
  rewrite <-lpow_mul, Nat.mul_comm in H'; exact H'.
Qed.

Lemma binary_count_any bs :
  segRLs (flip tm) ([isig]^^capacity_nat bs) [] (bits bs) ([1;1]^^List.length bs).
Proof.
  induction bs as [|b bs IH]; [constructor|].
  destruct b; cbn [bits flat_map bit capacity_nat List.length lpow];
    eapply segRLs_concat; [apply binary_high|exact IH|apply binary_low|exact IH].
Qed.

Lemma left_capacity bs :
  left_calls (N.to_nat (capacity bs)) (0inf << 1 <* bits bs)
    (0inf << 1 <* [1;1]^^List.length bs).
Proof.
  rewrite capacity_correct.
  exact (segRLs_sideRLs_concat (binary_count_any bs)
    (sideRLseq_O (flip tm) (0inf << 1))).
Qed.

Fixpoint increment_bits bs : option (list bool) :=
  match bs with
  | [] => None
  | false::bs => Some (true::bs)
  | true::bs => option_map (cons false) (increment_bits bs)
  end.

Lemma increment_bits_sound bs bs' : increment_bits bs = Some bs' ->
  segRLs (flip tm) [isig] [] (bits bs) (bits bs').
Proof.
  revert bs'; induction bs as [|b bs IH]; intros bs' H; [discriminate|].
  destruct b; cbn [increment_bits] in H.
  - destruct (increment_bits bs) as [u|] eqn:E; inversion H; subst; clear H.
    cbn [bits flat_map bit].
    eapply segRLs_concat; [exact binary_one|apply IH; reflexivity].
  - inversion H; subst; clear H; cbn [bits flat_map bit].
    eapply segRLs_concat; [exact binary_zero|constructor].
Qed.

Lemma m_one bs bs' r : increment_bits bs = Some bs' ->
  mconfig bs (1 >> r) -->* bconfig (false::bs') r.
Proof.
  intro H.
  pose proof (segRLs_sideRLs_concat (increment_bits_sound _ _ H)
    (sideRLseq_O (flip tm) (0inf << 1))) as Hl.
  change (left_calls 1 (0inf << 1 <* bits bs) (0inf << 1 <* bits bs')) in Hl.
  unfold mconfig, bconfig; cbn [bits flat_map bit].
  step; step.
  follow100 (left_call (0inf << 1 <* bits bs) (0inf << 1 <* bits bs') (2 >> 2 >> r) Hl).
  execute.
Qed.

Lemma blocked_calls n l l' r : left_calls n l l' ->
  l << 1 {{A}}> 4 >> r -->* l' << 1 {{A}}> 4 >> r.
Proof.
  revert l; induction n; intros l H.
  - inversion H; subst; finish.
  - destruct (left_calls_split 1 n _ _ H) as [u [H1 Hn]].
    step; step.
    follow100 (left_call l u (2 >> 4 >> r) H1).
    eapply evstep_step; [prove_step|].
    apply IHn; exact Hn.
Qed.

Lemma blocked_exit l r : l << 1 {{A}}> 4 >> r -->+ l <{{A}} 2 >> 4 >> r.
Proof. start_progress. Qed.

Lemma m_four bs r : mconfig bs (4 >> r) -->*
  event (2*List.length bs+2) (4 >> r).
Proof.
  unfold mconfig.
  follow (blocked_calls _ _ _ r (left_capacity bs)).
  follow100 (blocked_exit (0inf << 1 <* [1;1]^^List.length bs) r).
  rewrite ones_pairs.
  replace (0inf << 1 <* [1]^^(2*List.length bs))
    with (0inf <* [1]^^(2*List.length bs+1)).
  2: rewrite lpow_add, Str_app_assoc; reflexivity.
  follow sweep_left.
  unfold event; rewrite !lpow_add, !Str_app_assoc.
  apply evstep_refl'; reflexivity.
Qed.

Lemma one_exit l r r' : carries 1 r r' ->
  l << 1 << 0 {{B}}> 1 >> r -->* l <{{A}} 2 >> 2 >> 4 >> r'.
Proof.
  intro Hr; step; step; step.
  follow100 (right_call (l << 1 << 1 << 4) r r' Hr).
  execute.
Qed.

Lemma finish_one p r r' : carries 1 r r' ->
  0inf << 1 <* [1;1]^^p << 1 << 0 {{B}}> 1 >> r -->*
  event (2*p+3) (4 >> r').
Proof.
  intro Hr; follow (one_exit (0inf << 1 <* [1;1]^^p) _ _ Hr).
  rewrite ones_pairs.
  replace (0inf << 1 <* [1]^^(2*p)) with (0inf <* [1]^^(2*p+1)).
  2: rewrite lpow_add, Str_app_assoc; reflexivity.
  follow sweep_left.
  unfold event; rewrite !lpow_add, !Str_app_assoc.
  apply evstep_refl'; reflexivity.
Qed.

Lemma finish_four_one p l r :
  left_calls 1 l (0inf << 1 <* [1;1]^^p) ->
  l << 1 << 0 {{B}}> 4 >> r -->* event (2*p+3) (1 >> r).
Proof.
  intro Hl; follow100 (four_exit l r).
  follow100 (left_call l (0inf << 1 <* [1;1]^^p) (2 >> 1 >> 1 >> r) Hl).
  eapply evstep_step; [prove_step|].
  eapply evstep_step; [prove_step|].
  eapply evstep_step; [prove_step|].
  change (0inf << 1 <* [1;1]^^p <{{A}} 2 >> 2 >> 1 >> r -->*
    event (2*p+3) (1 >> r)).
  rewrite ones_pairs.
  replace (0inf << 1 <* [1]^^(2*p)) with (0inf <* [1]^^(2*p+1)).
  2: rewrite lpow_add, Str_app_assoc; reflexivity.
  follow sweep_left.
  unfold event; rewrite !lpow_add, !Str_app_assoc.
  apply evstep_refl'; reflexivity.
Qed.

Definition extra rem : nat := if Nat.eqb rem 2 then 1%nat else 0%nat.
Definition finish_config p rem r :=
  match rem with
  | O => event (2*p+2) (1 >> 1 >> r)
  | S O => event (2*p+3) (1 >> r)
  | _ => event (2*p+3) (4 >> r)
  end.

Lemma finish_four p rem l r r' : (rem<3)%nat ->
  left_calls rem l (0inf << 1 <* [1;1]^^p) ->
  carries (extra rem) r r' ->
  l << 1 << 0 {{B}}> 4 >> r -->* finish_config p rem r'.
Proof.
  intros Hb Hl Hr.
  destruct rem as [|[|[|rem]]]; [| | |lia]; cbn [finish_config] in *.
  - inversion Hl; inversion Hr; subst; apply driver_overflow.
  - inversion Hr; subst; apply finish_four_one; exact Hl.
  - follow (driver_four _ _ r Hl); apply finish_one; exact Hr.
Qed.

Lemma aligned_four p q rem l r r' : (rem<3)%nat ->
  left_calls (3*q+rem) l (0inf << 1 <* [1;1]^^p) ->
  carries (q+extra rem) r r' ->
  l << 1 << 0 {{B}}> 4 >> r -->* finish_config p rem r'.
Proof.
  intros Hb Hl Hr.
  destruct (left_calls_split (3*q) rem _ _ Hl) as [u [Hq Hu]].
  destruct (carries_split q (extra rem) _ _ Hr) as [v [HR Hv]].
  follow (driver_rounds q _ _ _ _ Hq HR).
  apply finish_four; assumption.
Qed.

Lemma aligned_one p q rem l r r' : (rem<3)%nat ->
  left_calls (1+(3*q+rem)) l (0inf << 1 <* [1;1]^^p) ->
  carries (1+(q+extra rem)) r r' ->
  l << 1 << 0 {{B}}> 1 >> r -->* finish_config p rem r'.
Proof.
  intros Hb Hl Hr.
  destruct (left_calls_split 1 (3*q+rem) _ _ Hl) as [u [H1 Hu]].
  destruct (carries_split 1 (q+extra rem) _ _ Hr) as [v [HR Hv]].
  follow (driver_one _ _ _ _ H1 HR).
  apply (aligned_four p q rem); assumption.
Qed.

Lemma left_calls_zero l l' : left_calls 0 l l' -> l=l'.
Proof. intro H; inversion H; reflexivity. Qed.

Lemma div3_spec c :
  (N.to_nat c = 3*N.to_nat (c/3) + N.to_nat (c mod 3))%nat /\
  (N.to_nat (c mod 3)<3)%nat.
Proof.
  split.
  - pose proof (N.div_mod c 3 ltac:(discriminate)) as H.
    apply (f_equal N.to_nat) in H.
    rewrite N2Nat.inj_add, N2Nat.inj_mul in H; cbn in H; lia.
  - pose proof (N.mod_lt c 3 ltac:(discriminate)); lia.
Qed.

Definition finish_eval p rem ys : nat * list Sym :=
  match rem with
  | O => (2*p+2,1::1::ys)
  | S O => (2*p+3,1::ys)
  | _ => (2*p+3,4::ys)
  end.
Definition event_pair (s:nat*list Sym) := event (fst s) (snd s *> 0inf).
Lemma finish_eval_config p rem ys :
  event_pair (finish_eval p rem ys) = finish_config p rem (ys *> 0inf).
Proof. destruct rem as [|[|rem]]; reflexivity. Qed.

Section Macro.
Variable batch_eval : list Sym -> N -> option (list Sym).
Hypothesis batch_sound : forall xs n ys, batch_eval xs n = Some ys ->
  carries (N.to_nat n) (xs *> 0inf) (ys *> 0inf).

Definition aligned_eval hi (d:Sym) xs : option (nat*list Sym) :=
  let c := capacity hi in
  let p := List.length hi in
  match d with
  | S1 =>
      if N.eqb c 0 then
        option_map (fun ys => (2*p+3,4::ys)) (batch_eval xs 1%N)
      else
        let q := ((c-1)/3)%N in
        let rem := N.to_nat ((c-1) mod 3)%N in
        option_map (finish_eval p rem)
          (batch_eval xs (1+q+N.of_nat (extra rem))%N)
  | S4 =>
      let q := (c/3)%N in
      let rem := N.to_nat (c mod 3)%N in
      option_map (finish_eval p rem)
        (batch_eval xs (q+N.of_nat (extra rem))%N)
  | _ => None
  end.

Lemma aligned_eval_sound hi d xs out : aligned_eval hi d xs = Some out ->
  bconfig (false::hi) (d >> xs *> 0inf) -->* event_pair out.
Proof.
  intro H; unfold aligned_eval in H; destruct d; try discriminate.
  - destruct (N.eqb (capacity hi) 0) eqn:Ezero.
    + apply N.eqb_eq in Ezero.
      destruct (batch_eval xs 1%N) as [ys|] eqn:E; inversion H; subst; clear H.
      apply batch_sound in E.
      pose proof (left_capacity hi) as Hl; rewrite Ezero in Hl.
      apply left_calls_zero in Hl.
      unfold bconfig; cbn [bits flat_map bit].
      change (0inf << 1 <* bits hi << 1 << 0 {{B}}> 1 >> xs *> 0inf -->*
        event (2*List.length hi+3) (4 >> ys *> 0inf)).
      rewrite Hl; apply finish_one; exact E.
    + apply N.eqb_neq in Ezero.
      destruct (batch_eval xs (1+(capacity hi-1)/3+
        N.of_nat (extra (N.to_nat ((capacity hi-1) mod 3))))%N) as [ys|] eqn:E;
        inversion H; subst; clear H.
      rewrite finish_eval_config.
      apply batch_sound in E.
      rewrite !N2Nat.inj_add, Nat2N.id in E.
      destruct (div3_spec (capacity hi-1)%N) as [Hdiv Hbound].
      assert (Hcount : (N.to_nat (capacity hi) =
        1+(3*N.to_nat ((capacity hi-1)/3)+N.to_nat ((capacity hi-1) mod 3)))%nat).
      { rewrite N2Nat.inj_sub in Hdiv; lia. }
      pose proof (left_capacity hi) as Hl; rewrite Hcount in Hl.
      unfold bconfig; cbn [bits flat_map bit].
      apply (aligned_one (List.length hi) (N.to_nat ((capacity hi-1)/3))
        (N.to_nat ((capacity hi-1) mod 3))); [exact Hbound|exact Hl|].
      replace (1+(N.to_nat ((capacity hi-1)/3)+
        extra (N.to_nat ((capacity hi-1) mod 3))))%nat
        with ((1+N.to_nat ((capacity hi-1)/3))+
        extra (N.to_nat ((capacity hi-1) mod 3)))%nat by lia.
      exact E.
  - destruct (batch_eval xs (capacity hi/3+
      N.of_nat (extra (N.to_nat (capacity hi mod 3))))%N) as [ys|] eqn:E;
      inversion H; subst; clear H.
    rewrite finish_eval_config.
    apply batch_sound in E; rewrite N2Nat.inj_add, Nat2N.id in E.
    destruct (div3_spec (capacity hi)) as [Hdiv Hbound].
    pose proof (left_capacity hi) as Hl; rewrite Hdiv in Hl.
    unfold bconfig; cbn [bits flat_map bit].
    apply (aligned_four (List.length hi) (N.to_nat (capacity hi/3))
      (N.to_nat (capacity hi mod 3))); assumption.
Qed.

Fixpoint reader_eval (b:bool) bs xs : option (nat*list Sym) :=
  match xs with
  | [] => None
  | d::xs =>
    if b then
      match d with
      | S2 => reader_eval false bs xs
      | _ => match bs with false::hi => aligned_eval hi d xs | _ => None end
      end
    else
      match d with
      | S2 => reader_eval true (false::bs) xs
      | S1 => match increment_bits bs with
              | Some bs' => reader_eval true (false::bs') xs
              | None => None
              end
      | S4 => Some (2*List.length bs+2,4::xs)
      | _ => None
      end
  end.

Definition reader_config (b:bool) bs xs :=
  if b then bconfig bs (xs *> 0inf) else mconfig bs (xs *> 0inf).

Lemma reader_eval_sound xs b bs out : reader_eval b bs xs = Some out ->
  reader_config b bs xs -->* event_pair out.
Proof.
  revert b bs out; induction xs as [|d xs IH]; intros b bs out H; [discriminate|].
  destruct b; cbn [reader_eval reader_config] in *.
  - destruct d.
    all: try (destruct bs as [|bh hi]; [discriminate|];
      destruct bh; [discriminate|]; apply aligned_eval_sound; exact H).
    follow b_two; apply (IH false); exact H.
  - destruct d; try discriminate.
    + destruct (increment_bits bs) as [bs'|] eqn:E; [|discriminate].
      follow (m_one _ _ (xs *> 0inf) E); apply (IH true); exact H.
    + follow m_two; apply (IH true); exact H.
    + inversion H; subst; clear H; apply m_four.
Qed.

Definition macro_step (s:nat*list Sym) :=
  reader_eval (Nat.eqb (fst s mod 2) 0) ([false]^^(fst s/2)) (snd s).
Fixpoint macro_run fuel s :=
  match fuel with
  | O => Some s
  | S fuel => match macro_step s with Some s' => macro_run fuel s' | None => None end
  end.

Lemma macro_step_sound s s' : macro_step s = Some s' ->
  event_pair s -->* event_pair s'.
Proof.
  destruct s as [m xs]; intro H; unfold macro_step in H; cbn [fst snd] in H.
  pose proof (Nat.div_mod m 2 ltac:(lia)) as Hd.
  pose proof (Nat.mod_upper_bound m 2 ltac:(lia)) as Hb.
  destruct (Nat.eqb (m mod 2) 0) eqn:E.
  - apply Nat.eqb_eq in E; assert (Hm : m=2*(m/2)) by lia.
    unfold event_pair; cbn [fst snd]; rewrite Hm at 1.
    follow event_even; apply (reader_eval_sound xs true); exact H.
  - apply Nat.eqb_neq in E; assert (Hm : m=2*(m/2)+1) by lia.
    unfold event_pair; cbn [fst snd]; rewrite Hm at 1.
    follow event_odd; apply (reader_eval_sound xs false); exact H.
Qed.

Lemma macro_run_sound fuel s s' : macro_run fuel s = Some s' ->
  event_pair s -->* event_pair s'.
Proof.
  revert s; induction fuel; intros s H; cbn [macro_run] in H.
  - inversion H; subst; finish.
  - destruct (macro_step s) as [u|] eqn:E; [|discriminate].
    follow (macro_step_sound _ _ E); apply IHfuel; exact H.
Qed.
End Macro.


Definition carry_digit (d : nat) : list Sym :=
  match d with O => [2;4] | S O => [1;1] | _ => [2;1] end.

Open Scope nat_scope.

(* This induction is a theorem about arbitrary counts, never an executable
   unary counter. The evaluator below works entirely over N. *)
Lemma carries_digit n : forall d r r', (d<3)%nat ->
  carries ((d+n)/3) r r' ->
  carries n (carry_digit d *> r) (carry_digit ((d+n) mod 3) *> r').
Proof.
  induction n as [|n IH]; intros d r r' Hd HC.
  - rewrite Nat.add_0_r, Nat.div_small in HC by lia.
    inversion HC; subst.
    rewrite Nat.add_0_r, Nat.mod_small by lia. apply carries_zero.
  - destruct d as [|[|d]]; [| |assert (d=0)%nat by lia; subst d].
    + change (carries (1+n) (carry_digit 0 *> r)
        (carry_digit ((1+n) mod 3) *> r')).
      eapply carries_add.
      * exact (segRLs_sideRLs_concat digit0_rule (sideRLseq_O tm r)).
      * apply (IH 1); [lia|exact HC].
    + replace (1+S n)%nat with (2+n)%nat by lia.
      change (carries (1+n) (carry_digit 1 *> r)
        (carry_digit ((2+n) mod 3) *> r')).
      eapply carries_add.
      * exact (segRLs_sideRLs_concat digit1_rule (sideRLseq_O tm r)).
      * apply (IH 2); [lia|].
        replace (2+n)%nat with (1+S n)%nat by lia. exact HC.
    + replace ((2+S n)/3)%nat with (1+n/3)%nat in HC by lia.
      destruct (carries_split 1 (n/3) r r' HC) as [u [H1 Hn]].
      replace ((2+S n) mod 3)%nat with (n mod 3)%nat by lia.
      change (carries (1+n) (carry_digit 2 *> r) (carry_digit (n mod 3) *> r')).
      eapply carries_add.
      * exact (segRLs_sideRLs_concat digit2_rule H1).
      * apply (IH 0); [lia|exact Hn].
Qed.

Definition ndigit (d : N) := carry_digit (N.to_nat d).

Lemma carries_ndigit n d r r' : (d<3)%N ->
  carries (N.to_nat ((d+n)/3)) r r' ->
  carries (N.to_nat n) (ndigit d *> r) (ndigit ((d+n) mod 3) *> r').
Proof.
  intros Hd HC. unfold ndigit.
  rewrite N2Nat.inj_mod,N2Nat.inj_add.
  apply carries_digit; [lia|].
  rewrite <-N2Nat.inj_add.
  change (carries (N.to_nat (d+n)/N.to_nat 3) r r').
  rewrite <-N2Nat.inj_div. exact HC.
Qed.

Lemma carries_blank_one : carries 1 0inf ([S2;S1] *> 0inf).
Proof.
  unfold carries. apply sideRL_1. intro l. start_progress.
Qed.

Open Scope N_scope.
Fixpoint blank_batch (fuel : nat) (n : N) : option (list Sym) :=
  if n =? 0 then Some [] else
  match fuel with
  | O => None
  | S f => option_map (app (ndigit ((n+1) mod 3))) (blank_batch f ((n+1)/3))
  end.

Lemma blank_batch_sound fuel : forall n ys,
  blank_batch fuel n=Some ys -> carries (N.to_nat n) 0inf (ys *> 0inf).
Proof.
  induction fuel as [|fuel IH]; intros n ys HC;
    cbn [blank_batch] in HC; destruct (N.eqb_spec n 0) as [H0|H0].
  - subst n. inversion HC; subst. apply carries_zero.
  - discriminate.
  - subst n. inversion HC; subst. apply carries_zero.
  - destruct (blank_batch fuel ((n+1)/3)) as [zs|] eqn:EZ; [|discriminate].
    inversion HC; subst ys; clear HC.
    pose proof (IH _ _ EZ) as HZ.
    rewrite Str_app_assoc.
    replace (N.to_nat n) with (1+N.to_nat (n-1))%nat by lia.
    eapply carries_add; [exact carries_blank_one|].
    change (carries (N.to_nat (n-1)) (ndigit 2 *> 0inf)
      (ndigit ((n+1) mod 3) *> zs *> 0inf)).
    replace (n+1) with (2+(n-1)) by lia.
    apply carries_ndigit; [lia|].
    replace (2+(n-1)) with (n+1) by lia. exact HZ.
Qed.

Fixpoint batch_carry (xs : list Sym) (n : N) : option (list Sym) :=
  if n =? 0 then Some xs else
  match xs with
  | [] => blank_batch 256 n
  | S4::zs => Some (S4::zs)
  | S1::S1::zs => option_map (app (ndigit ((1+n) mod 3))) (batch_carry zs ((1+n)/3))
  | S1::S2::zs => option_map (app [S2;S2]) (batch_carry zs (2*(n-1)))
  | S1::S4::zs => option_map (app (ndigit ((n-1) mod 3))) (batch_carry zs ((n-1)/3))
  | S2::S4::zs => option_map (app (ndigit (n mod 3))) (batch_carry zs (n/3))
  | S2::S1::zs => option_map (app (ndigit ((2+n) mod 3))) (batch_carry zs ((2+n)/3))
  | S2::S2::zs => option_map (app [S2;S2]) (batch_carry zs (2*n))
  | _ => None
  end.

Lemma carries_double_N n r r' : carries (N.to_nat (2*n)) r r' ->
  carries (N.to_nat n) (S2 >> S2 >> r) (S2 >> S2 >> r').
Proof.
  intro HC. rewrite N2Nat.inj_mul in HC.
  apply carries_double. exact HC.
Qed.
Lemma carries_one_two_N n r r' : n<>0 ->
  carries (N.to_nat (2*(n-1))) r r' ->
  carries (N.to_nat n) (S1 >> S2 >> r) (S2 >> S2 >> r').
Proof.
  intros Hn HC. replace (N.to_nat n) with (1+N.to_nat (n-1))%nat by lia.
  eapply carries_add.
  - exact (segRLs_sideRLs_concat one_two_rule (sideRLseq_O tm r)).
  - apply carries_double_N. exact HC.
Qed.
Lemma carries_one_four_N n r r' : n<>0 ->
  carries (N.to_nat ((n-1)/3)) r r' ->
  carries (N.to_nat n) (S1 >> S4 >> r) (ndigit ((n-1) mod 3) *> r').
Proof.
  intros Hn HC. replace (N.to_nat n) with (1+N.to_nat (n-1))%nat by lia.
  eapply carries_add.
  - exact (segRLs_sideRLs_concat one_four_rule (sideRLseq_O tm r)).
  - exact (carries_ndigit (n-1) 0 r r' ltac:(lia) HC).
Qed.

Lemma batch_carry_sound : forall xs n ys,
  batch_carry xs n=Some ys ->
  carries (N.to_nat n) (xs *> 0inf) (ys *> 0inf).
Proof.
  fix IH 1. intros xs n ys HC.
  destruct xs as [|s xs]; cbn [batch_carry] in HC;
    destruct (N.eqb_spec n 0) as [H0|H0].
  - subst n. inversion HC; subst. apply carries_zero.
  - apply (blank_batch_sound 256). exact HC.
  - subst n. inversion HC; subst. apply carries_zero.
  - destruct s; try discriminate.
    + destruct xs as [|t zs]; [discriminate|]. destruct t; try discriminate.
      * destruct (batch_carry zs ((1+n)/3)) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC. rewrite Str_app_assoc.
        exact (carries_ndigit n 1 _ _ ltac:(lia) (IH zs _ _ E)).
      * destruct (batch_carry zs (2*(n-1))) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC.
        apply carries_one_two_N; [exact H0|exact (IH zs _ _ E)].
      * destruct (batch_carry zs ((n-1)/3)) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC. rewrite Str_app_assoc.
        apply carries_one_four_N; [exact H0|exact (IH zs _ _ E)].
    + destruct xs as [|t zs]; [discriminate|]. destruct t; try discriminate.
      * destruct (batch_carry zs ((2+n)/3)) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC. rewrite Str_app_assoc.
        exact (carries_ndigit n 2 _ _ ltac:(lia) (IH zs _ _ E)).
      * destruct (batch_carry zs (2*n)) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC.
        apply carries_double_N. exact (IH zs _ _ E).
      * destruct (batch_carry zs (n/3)) as [u|] eqn:E; [|discriminate].
        inversion HC; subst ys; clear HC. rewrite Str_app_assoc.
        exact (carries_ndigit n 0 _ _ ltac:(lia) (IH zs _ _ E)).
    + inversion HC; subst ys; clear HC. apply carries_wall.
Qed.

Example batch_carry_low_checks :
  batch_carry [S3] 0=Some [S3] /\
  batch_carry [] 1=Some [S2;S1] /\
  batch_carry [] 2=Some [S2;S4;S2;S1] /\
  batch_carry [S4;S0] 8=Some [S4;S0] /\
  batch_carry [S1;S2] 1=Some [S2;S2] /\
  batch_carry [S1;S4] 1=Some [S2;S4] /\
  batch_carry [S2;S4] 2=Some [S2;S1] /\
  batch_carry [S1;S1] 2=Some [S2;S4;S2;S1] /\
  batch_carry [S2;S1] 1=Some [S2;S4;S2;S1] /\
  batch_carry [S2;S2] 1=Some [S2;S2;S2;S4;S2;S1] /\
  batch_carry [S1] 1=None /\
  blank_batch 0 1=None /\ blank_batch 0 0=Some [].
Proof. vm_compute; repeat split; reflexivity. Qed.


Close Scope N_scope.
Close Scope nat_scope.

Fixpoint decode_digits (xs:list Sym) : list digit :=
  match xs with
  | S2::S4::xs => d0::decode_digits xs
  | S1::S1::xs => d1::decode_digits xs
  | S2::S1::xs => d2::decode_digits xs
  | _ => []
  end.
Definition initial_word : list Sym := [4;2;4;2;1;2;1].
Definition seed_digits := Eval vm_compute in
  match macro_run batch_carry 41 (13%nat,initial_word) with
  | Some (_,r) => decode_digits (skipn 7 r)
  | None => []
  end.

Lemma macro_seed : macro_run batch_carry 41 (13%nat,initial_word) =
  Some (100%nat, [1;1] ++ [2]^^4 ++ [4] ++ flat_map enc_digit seed_digits).
Proof. vm_compute; reflexivity. Qed.

Lemma ternary_flat ds : flat_map enc_digit ds *> 0inf = ternary ds.
Proof.
  induction ds; [reflexivity|].
  cbn [flat_map ternary]; rewrite Str_app_assoc, IHds; reflexivity.
Qed.

Lemma init_reaches_loop : c0 -->*
  event 100 (1 >> 1 >> [2]^^4 *> 4 >> ternary seed_digits).
Proof.
  eapply evstep_trans; [exact init_681|].
  pose proof (macro_run_sound batch_carry batch_carry_sound 41 _ _ macro_seed) as H.
  unfold event_pair in H; cbn [fst snd] in H.
  rewrite !Str_app_assoc in H; cbn [Str_app] in H.
  rewrite ternary_flat in H.
  exact H.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init_reaches_loop|].
  exact (loop_nonhalt 8 4 seed_digits).
Qed.

End TM54.


Close Scope Q_scope. Close Scope Z_scope. Close Scope N_scope.
Close Scope nat_scope. Open Scope sym_scope.
Set Default Goal Selector "1".

(* Machine 55. *)
From BusyCoq Require Import Individual25.
From Coq Require Import String NArith Lia List Bool PeanoNat ZifyNat Arith.Wf_nat Recdef.
Import ListNotations.

(** Binary-count version of the digit model in the supplied ShiftOverflow
    proof.  The only machine imported is the generic two-state/five-symbol
    interface.  Local passages below are checked against the original table. *)
Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB4LB0LA_1LA3LA1RA4RA---").
Notation a := (A, ([] : list Sym)).
Notation sig := (a,a).
Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=30); reflexivity.

Lemma block20 : segRLs tm [sig] [] [S2;S0] [S2;S3].
Proof. finite_rule. Qed.
Lemma block23 : segRLs tm [sig] [sig] [S2;S3] [S2;S1].
Proof. finite_rule. Qed.
Lemma block21 : segRLs tm [sig] [sig] [S2;S1] [S2;S0].
Proof. finite_rule. Qed.
Lemma block22 : segRLs tm [sig] [sig;sig] [S2;S2] [S2;S2].
Proof. finite_rule. Qed.
Lemma block02 : segRLs tm [sig] [sig] [S0;S2] [S2;S2].
Proof. finite_rule. Qed.
Lemma block00 : segRLs tm [sig] [] [S0;S0] [S2;S1].
Proof. finite_rule. Qed.
Lemma loose1 : segRLs tm [sig] [] [S1] [S2].
Proof. finite_rule. Qed.
Lemma loose4 : segRLs tm [sig] [] [S4] [S0].
Proof. finite_rule. Qed.
Lemma block223 : segRLs tm [sig] [] [S2;S2;S3] [S2;S0;S0].
Proof. finite_rule. Qed.
Lemma block023 : segRLs tm [sig] [] [S0;S2;S3] [S2;S3;S4].
Proof. finite_rule. Qed.

Open Scope N_scope.
Definition stDigit (d : N) : Sym :=
  if d mod 3 =? 0 then S0 else if d mod 3 =? 1 then S3 else S1.
Definition cycE (t d : N) : N :=
  if d mod 3 =? 0 then t-(t+2)/3
  else if d mod 3 =? 1 then t-t/3 else t-(t+1)/3.
Definition cycD (t d : N) : Sym := stDigit (d+t).

Lemma mod3 d : d mod 3=0 \/ d mod 3=1 \/ d mod 3=2.
Proof. pose proof (N.mod_lt d 3 ltac:(discriminate)); lia. Qed.
Lemma cycE_le t d : cycE t d <= t.
Proof. unfold cycE; repeat destruct (_ =? _); lia. Qed.
Lemma cycE_zero d : cycE 0 d=0.
Proof. unfold cycE; repeat destruct (_ =? _); reflexivity. Qed.
Lemma cycE_succ t d : cycE (t+1) d=
  (if d mod 3 =? 0 then 0 else 1)+cycE t (d+1).
Proof.
  unfold cycE. destruct (mod3 d) as [H|[H|H]];
  assert (E : (d+1) mod 3=(d mod 3+1) mod 3) by
    (rewrite N.Div0.add_mod; reflexivity);
  rewrite E,H.
  - change (t+1-(t+1+2)/3=0+(t-t/3)); lia.
  - change (t+1-(t+1)/3=1+(t-(t+1)/3)); lia.
  - change (t+1-(t+1+1)/3=1+(t-(t+2)/3)); lia.
Qed.
Lemma stDigit_mod d : stDigit (d mod 3)=stDigit d.
Proof. unfold stDigit; rewrite N.Div0.mod_mod; reflexivity. Qed.
Lemma cycD_succ t d : cycD (t+1) d=cycD t (d+1).
Proof. unfold cycD; f_equal; lia. Qed.

(** A radix-3/2 cell: three incoming calls produce two outgoing calls.
    N.to_nat occurs only in the relational specification, never in scan. *)
Lemma cycle_batch t d :
  segRLs tm ([sig]^^N.to_nat t) ([sig]^^N.to_nat (cycE t d))
    [S2;stDigit d] [S2;cycD t d].
Proof.
  revert d; induction t using N.peano_ind; intro d.
  - rewrite cycE_zero; unfold cycD; rewrite N.add_0_r. constructor.
  - replace (N.succ t) with (1+t) by lia.
    rewrite N2Nat.inj_add,lpow_add.
    replace (1+t) with (t+1) by lia.
    rewrite cycE_succ,N2Nat.inj_add,lpow_add,cycD_succ.
    eapply segRLs_trans; [|apply IHt].
    unfold stDigit.
    destruct (mod3 d) as [H|[H|H]];
      assert (E : (d+1) mod 3=(d mod 3+1) mod 3) by
        (rewrite N.Div0.add_mod; reflexivity);
      rewrite E,H; cbn; [exact block20|exact block23|exact block21].
Qed.

Lemma doubling_batch t :
  segRLs tm ([sig]^^N.to_nat t) ([sig]^^N.to_nat (2*t)) [S2;S2] [S2;S2].
Proof.
  pose proof (segRLs_wall'' (n:=N.to_nat t) block22) as H.
  change [sig;sig] with ([sig]^^2) in H.
  rewrite <-lpow_mul in H. rewrite N2Nat.inj_mul.
  change (segRLs tm ([sig]^^N.to_nat t) ([sig]^^(2*N.to_nat t)) [S2;S2] [S2;S2]).
  rewrite Nat.mul_comm. exact H.
Qed.

Lemma Nnat_lt x y : (N.to_nat x<N.to_nat y)%nat <-> x<y.
Proof. rewrite <-Nat.compare_lt_iff,<-N2Nat.inj_compare; reflexivity. Qed.
Function freshW (t : N) {measure N.to_nat t} : list Sym :=
  if t =? 0 then [] else stDigit (t+1)::freshW (t-1-t/3).
Proof. intros; apply Nnat_lt; apply N.eqb_neq in teq; lia. Defined.

Lemma freshW_zero : freshW 0=[].
Proof. rewrite freshW_equation; reflexivity. Qed.
Lemma freshW_succ t : freshW (t+1)=cycD t 2::freshW (cycE t 2).
Proof.
  rewrite freshW_equation. assert (E : (t+1 =? 0)=false) by (apply N.eqb_neq; lia).
  rewrite E. unfold cycD,cycE; cbn.
  replace (t+1-1-(t+1)/3) with (t-(t+1)/3) by lia.
  replace (t+1+1) with (2+t) by lia. reflexivity.
Qed.

Definition cells (w : list Sym) : list Sym := flat_map (fun d => [S2;d]) w.

Lemma freshW_sound t :
  sideRLs tm ([sig]^^N.to_nat t) 0inf (cells (freshW t) *> 0inf).
Proof.
  induction t as [t IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  destruct (N.eq_dec t 0) as [->|Ht].
  - rewrite freshW_zero; constructor.
  - replace t with (1+(t-1)) by lia.
    rewrite N2Nat.inj_add,lpow_add.
    replace (1+(t-1)) with ((t-1)+1) by lia.
    rewrite freshW_succ.
    change (sideRLs tm ([sig]++[sig]^^N.to_nat (t-1))
      0inf ([S2;cycD (t-1) 2] *> cells (freshW (cycE (t-1) 2)) *> 0inf)).
    eapply sideRLs_trans.
    + replace 0inf with ([S0;S0] *> 0inf) at 1 by solve_const0_eq.
      eapply segRLs_sideRLs_concat; [exact block00|constructor].
    + eapply segRLs_sideRLs_concat; [apply (cycle_batch (t-1) 2)|].
      apply IH. unfold ltof; apply Nnat_lt. pose proof (cycE_le (t-1) 2); lia.
Qed.

Definition valid (x : Sym) : bool :=
  match x with S0 | S1 | S2 => true | _ => false end.
Definition hcost (x : Sym) : N := match x with S2=>0 | S0=>1 | _=>2 end.
Definition chT x t := 2*t-hcost x.
Definition expT x t :=
  match x with S2=>cycE (t-1) 0 | S0=>cycE (t-1) 1-1 | _=>cycE (t-2) 0 end.
Definition expD x t :=
  match x with S2=>cycD (t-1) 0 | S0=>cycD (t-1) 1 | _=>cycD (t-2) 0 end.
Definition frT x t :=
  match x with S0=>cycE (t-1) 2 | S1=>cycE (t-1) 0 | _=>cycE t 0 end.
Definition frD x t :=
  match x with S0=>cycD (t-1) 2 | S1=>cycD (t-1) 0 | _=>cycD t 0 end.

Lemma cheap_batch t x : 0<t -> valid x=true ->
  segRLs tm ([sig]^^N.to_nat t) ([sig]^^N.to_nat (chT x t)) [x;S2] [S2;S2].
Proof.
  intros Ht Hx; destruct x; cbn [valid] in Hx; try discriminate.
  - unfold chT,hcost. replace t with (1+(t-1)) at 1 by lia.
    replace (2*t-1) with (1+2*(t-1)) by lia.
    rewrite !N2Nat.inj_add,!lpow_add.
    eapply segRLs_trans; [exact block02|apply doubling_batch].
  - unfold chT,hcost. replace t with (1+(t-1)) at 1 by lia.
    replace (2*t-2) with (0+2*(t-1)) by lia.
    rewrite !N2Nat.inj_add,!lpow_add.
    eapply segRLs_trans; [|apply doubling_batch]. finite_rule.
  - unfold chT,hcost; rewrite N.sub_0_r. apply doubling_batch.
Qed.

Lemma frontier_sound t x : 0<t -> valid x=true ->
  sideRLs tm ([sig]^^N.to_nat t) (x >> 0inf)
    (cells (frD x t::freshW (frT x t)) *> 0inf).
Proof.
  intros Ht Hx; destruct x; cbn [valid] in Hx; try discriminate;
    cbn [frD frT cells flat_map].
  - replace t with (1+(t-1)) at 1 by lia.
    rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
    + rewrite (const_unfold Sym S0) at 1.
      eapply (segRLs_sideRLs_concat block00); constructor.
    + eapply (segRLs_sideRLs_concat (cycle_batch (t-1) 2)); apply freshW_sound.
  - replace t with (1+(t-1)) at 1 by lia.
    rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
    + change (S1 >> 0inf) with ([S1] *> 0inf).
      eapply (segRLs_sideRLs_concat loose1); constructor.
    + rewrite (const_unfold Sym S0) at 1.
      eapply (segRLs_sideRLs_concat (cycle_batch (t-1) 0)); apply freshW_sound.
  - rewrite (const_unfold Sym S0) at 1.
    eapply (segRLs_sideRLs_concat (cycle_batch t 0)); apply freshW_sound.
Qed.

(** A three-cell exceptional token changes the next head.  For head zero,
    the first outgoing call really erases the transient 4; it is not silently
    dropped from the protocol. *)
Lemma expensive_sound t x r r' : 2<=t -> valid x=true ->
  sideRLs tm ([sig]^^N.to_nat (expT x t)) (S0 >> r) r' ->
  sideRLs tm ([sig]^^N.to_nat t) ([x;S2;S3] *> r) ([S2;expD x t] *> r').
Proof.
  intros Ht Hx Hr; destruct x; cbn [valid] in Hx; try discriminate;
    cbn [expT] in Hr; cbn [expD].
  - replace t with (1+(t-1)) at 1 by lia.
    rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
    + eapply (segRLs_sideRLs_concat block023); constructor.
    + change ([S2;S3;S4] *> r) with ([S2;S3] *> (S4 >> r)).
      eapply (segRLs_sideRLs_concat (cycle_batch (t-1) 1)).
      assert (Hpos : 1<=cycE (t-1) 1) by (unfold cycE; change (1<=t-1-(t-1)/3); lia).
      replace (cycE (t-1) 1) with (1+(cycE (t-1) 1-1)) by lia.
      rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans; [|exact Hr].
      change (sideRLs tm [sig] ([S4] *> r) ([S0] *> r)).
      eapply (segRLs_sideRLs_concat loose4); constructor.
  - replace t with (1+(t-1)) at 1 by lia.
    rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
    + change ([S1;S2;S3] *> r) with ([S1] *> ([S2;S3] *> r)).
      eapply (segRLs_sideRLs_concat loose1); constructor.
    + replace (t-1) with (1+(t-2)) at 1 by lia.
      rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
      * change (S2 >> [S2;S3] *> r) with ([S2;S2;S3] *> r).
        eapply (segRLs_sideRLs_concat block223); constructor.
      * change ([S2;S0;S0] *> r) with ([S2;S0] *> (S0 >> r)).
        eapply (segRLs_sideRLs_concat (cycle_batch (t-2) 0)); exact Hr.
  - replace t with (1+(t-1)) at 1 by lia.
    rewrite N2Nat.inj_add,lpow_add. eapply sideRLs_trans.
    + eapply (segRLs_sideRLs_concat block223); constructor.
    + change ([S2;S0;S0] *> r) with ([S2;S0] *> (S0 >> r)).
      eapply (segRLs_sideRLs_concat (cycle_batch (t-1) 0)); exact Hr.
Qed.

Definition expensive (c : Sym) := match c with S3=>true | _=>false end.
Definition prepend (d : Sym) (o : option (list Sym*N)) : option (list Sym*N) :=
  option_map (fun '(w,v) => (d::w,v)) o.

(** Combining scan and scanT prevents a duplicate success-equivalence proof.
    Rejecting every expensive token at t<2 is equivalent on successful runs:
    the source's head-2/t=1 case immediately calls a nonempty suffix at zero. *)
Fixpoint scan (t : N) (x : Sym) (tail : list Sym) : option (list Sym*N) :=
  if t =? 0 then None else if valid x then
  match tail with
  | [] => Some (frD x t::freshW (frT x t),frT x t)
  | c::rest =>
    if expensive c then
      if t <? 2 then None
      else prepend (expD x t) (scan (expT x t) S0 rest)
    else prepend S2 (scan (chT x t) c rest)
  end else None.

Lemma prepend_some d z w v : prepend d z=Some (w,v) ->
  exists u, z=Some (u,v) /\ w=d::u.
Proof.
  destruct z as [[u v']|]; cbn [prepend option_map]; intro H; try discriminate.
  inversion H; subst. exists u; auto.
Qed.
Lemma scan_sound tail : forall t x w v, scan t x tail=Some (w,v) ->
  sideRLs tm ([sig]^^N.to_nat t) (x >> cells tail *> 0inf) (cells w *> 0inf).
Proof.
  induction tail as [|c tail IH]; intros t x w v H;
    cbn [scan] in H; destruct (t =? 0) eqn:Ht; try discriminate;
    destruct (valid x) eqn:Hx; try discriminate;
    apply N.eqb_neq in Ht.
  - inversion H; subst. apply frontier_sound; [lia|exact Hx].
  - destruct (expensive c) eqn:Hc.
    + assert (Ec : c=S3) by (destruct c; cbn in Hc; congruence); subst c.
      destruct (t <? 2) eqn:Htwo; [discriminate|].
      apply N.ltb_ge in Htwo.
      destruct (prepend_some _ _ _ _ H) as [u [Hu ->]].
      change (sideRLs tm ([sig]^^N.to_nat t)
        ([x;S2;S3] *> (cells tail *> 0inf))
        ([S2;expD x t] *> (cells u *> 0inf))).
      apply expensive_sound; [exact Htwo|exact Hx|apply IH with (v:=v); exact Hu].
    + destruct (prepend_some _ _ _ _ H) as [u [Hu ->]].
      change (sideRLs tm ([sig]^^N.to_nat t)
        ([x;S2] *> (c >> cells tail *> 0inf))
        ([S2;S2] *> (cells u *> 0inf))).
      eapply (segRLs_sideRLs_concat (cheap_batch t x ltac:(lia) Hx)).
      apply IH with (v:=v); exact Hu.
Qed.

Definition epochF (w : list Sym) := scan 1 S0 w.
Definition WordRich (w : list Sym) : Prop :=
  exists w' v, epochF w=Some (w',v) /\ 25<=v.
Definition boundary (w : list Sym) := (0inf {{A}}> (S0 >> cells w *> 0inf)).

Lemma epoch_sound w w' v : epochF w=Some (w',v) ->
  boundary w -[tm]->+ boundary w'.
Proof.
  intro H. pose proof (scan_sound _ _ _ _ _ H) as HS.
  change (sideRLs tm [sig] (S0 >> cells w *> 0inf) (cells w' *> 0inf)) in HS.
  inversion HS; subst. match goal with H : sideRLs _ [] _ _ |- _ => inversion H; subst end.
  unfold boundary. match goal with H : sideRL tm _ _ _ _ |- _ => specialize (H 0inf) end.
  match goal with H : _ -[tm]->+ _ |- _ =>
    eapply progress_evstep_trans; [exact H|] end.
  rewrite (const_unfold Sym S0) at 1. execute.
Qed.

Fixpoint epochIter (n : nat) (w : list Sym) : option (list Sym) :=
  match n with
  | O=>Some w
  | S n=>match epochF w with None=>None | Some (w',_)=>epochIter n w' end
  end.
Lemma epochIter_sound n w u : epochIter n w=Some u ->
  boundary w -[tm]->* boundary u.
Proof.
  revert w u; induction n as [|n IH]; intros w u H.
  - inversion H; subst; apply evstep_refl.
  - cbn [epochIter] in H. destruct (epochF w) as [[w' v]|] eqn:E; try discriminate.
    eapply evstep_trans; [apply progress_evstep; eapply epoch_sound; exact E|apply IH; exact H].
Qed.
Definition richb (w : list Sym) : bool :=
  match epochF w with Some (_,v)=>25<=?v | None=>false end.
Lemma richb_spec w : richb w=true -> WordRich w.
Proof.
  unfold richb,WordRich. destruct (epochF w) as [[w' v]|] eqn:E; try discriminate.
  intro H; apply N.leb_le in H. exists w',v; auto.
Qed.
Lemma seed_check :
  match epochIter 4 [] with Some w=>richb w | None=>false end=true.
Proof. vm_compute; reflexivity. Qed.
Lemma seed : exists w, boundary [] -[tm]->* boundary w /\ WordRich w.
Proof.
  pose proof seed_check as H. destruct (epochIter 4 []) as [w|] eqn:E; try discriminate.
  exists w; split; [apply epochIter_sound with (n:=4%nat); exact E|apply richb_spec; exact H].
Qed.

Lemma scan_valid t x tail w v : scan t x tail=Some (w,v) -> valid x=true /\ 0<t.
Proof.
  destruct tail; cbn [scan]; destruct (t =? 0) eqn:E; try discriminate;
  destruct (valid x) eqn:V; try discriminate; intros; split; try reflexivity;
  apply N.eqb_neq in E; lia.
Qed.
Lemma stDigit_cases d : stDigit d=S0 \/ stDigit d=S1 \/ stDigit d=S3.
Proof. unfold stDigit; repeat destruct (_ =? _); auto. Qed.
Lemma stDigit_three d : stDigit d=S3 -> d mod 3=1.
Proof.
  unfold stDigit. destruct (d mod 3 =? 0) eqn:E0; [discriminate|].
  destruct (d mod 3 =? 1) eqn:E1; [intros; apply N.eqb_eq; exact E1|discriminate].
Qed.
Lemma stDigit_one d : stDigit d=S1 -> d mod 3=2.
Proof.
  unfold stDigit. destruct (d mod 3 =? 0) eqn:E0; [discriminate|].
  destruct (d mod 3 =? 1) eqn:E1; [discriminate|].
  intros; apply N.eqb_neq in E0; apply N.eqb_neq in E1; destruct (mod3 d); lia.
Qed.
Lemma expD_cases x t : expD x t=S0 \/ expD x t=S1 \/ expD x t=S3.
Proof. destruct x; unfold expD,cycD; apply stDigit_cases. Qed.
Lemma frD_cases x t : frD x t=S0 \/ frD x t=S1 \/ frD x t=S3.
Proof. destruct x; unfold frD,cycD; apply stDigit_cases. Qed.

(* These arithmetic facts use binary division throughout. *)
Lemma cycE_0 t : cycE t 0=t-(t+2)/3. Proof. reflexivity. Qed.
Lemma cycE_1 t : cycE t 1=t-t/3. Proof. reflexivity. Qed.
Lemma cycE_2 t : cycE t 2=t-(t+1)/3. Proof. reflexivity. Qed.
Ltac token_arith :=
  lazy beta iota delta [hcost chT expT frT] in *;
  rewrite ?cycE_0,?cycE_1,?cycE_2 in *; lia.

Lemma cheap_compare x y t u : valid x=true -> valid y=true -> t<=u ->
  (hcost y<=hcost x \/ t+1<=u) -> chT x t<=chT y u.
Proof. destruct x,y; cbn [valid]; intros; try discriminate; token_arith. Qed.
Lemma expensive_compare x y t u : valid x=true -> valid y=true -> 2<=t -> t<=u ->
  (hcost y<=hcost x \/ t+1<=u) -> expT x t<=expT y u.
Proof. destruct x,y; cbn [valid]; intros; try discriminate; token_arith. Qed.
Lemma expensive_gain x y t u : valid x=true -> valid y=true -> 2<=t -> t<=u ->
  expT x t+1<=chT y u.
Proof. destruct x,y; cbn [valid]; intros; try discriminate; token_arith. Qed.
Lemma frontier_positive x t : valid x=true -> 1<=frT x t -> 2<=t.
Proof. destruct x; cbn [valid]; intros; try discriminate; token_arith. Qed.
Lemma frontier_cheap x y t u : valid x=true -> valid y=true -> 2<=t -> t<=u ->
  frT x t<=chT y u.
Proof. destruct x,y; cbn [valid]; intros; try discriminate; token_arith. Qed.

Lemma frontier_expensive x y t u : valid x=true -> valid y=true -> 2<=t -> t<=u ->
  (hcost y<=hcost x \/ t+1<=u) -> frD x t=S3 -> frT x t<=expT y u.
Proof.
  destruct x,y; cbn [valid]; intros Hx Hy Ht Htu Hd H3; try discriminate;
    cbn [frD] in H3; unfold cycD in H3; apply stDigit_three in H3; token_arith.
Qed.
Lemma frontier_loose x y t u : valid x=true -> valid y=true -> 2<=t -> t<=u ->
  (hcost y<=hcost x \/ t+1<=u) -> frD x t=S1 -> 3*frT x t<=chT y u.
Proof.
  destruct x,y; cbn [valid]; intros Hx Hy Ht Htu Hd H1; try discriminate;
    cbn [frD] in H1; unfold cycD in H1; apply stDigit_one in H1; token_arith.
Qed.

Definition Good t x tail : Prop :=
  exists w v, scan t x tail=Some (w,v) /\ 25<=v.
Definition pen (x : Sym) : N := match x with S1=>1 | _=>0 end.
Definition FreshExit : Prop := forall v b u, valid b=true -> 25<=v ->
  v+2*v*pen b<=u -> Good u b (freshW v).

Lemma scan_last t x : 0<t -> valid x=true ->
  scan t x []=Some (frD x t::freshW (frT x t),frT x t).
Proof.
  intros Ht Hx; cbn [scan]. assert (E : (t =? 0)=false) by (apply N.eqb_neq; lia).
  rewrite E,Hx; reflexivity.
Qed.
Lemma scan_exp t x tail : 2<=t -> valid x=true ->
  scan t x (S3::tail)=prepend (expD x t) (scan (expT x t) S0 tail).
Proof.
  intros Ht Hx; cbn [scan]. assert (E : (t =? 0)=false) by (apply N.eqb_neq; lia).
  assert (E2 : (t <? 2)=false) by (apply N.ltb_ge; lia).
  rewrite E,Hx,E2; reflexivity.
Qed.
Lemma scan_cheap t x c tail : 0<t -> valid x=true -> expensive c=false ->
  scan t x (c::tail)=prepend S2 (scan (chT x t) c tail).
Proof.
  intros Ht Hx Hc; cbn [scan]. assert (E : (t =? 0)=false) by (apply N.eqb_neq; lia).
  rewrite E,Hx,Hc; reflexivity.
Qed.
Lemma good_exp t x tail : 2<=t -> valid x=true -> Good (expT x t) S0 tail ->
  Good t x (S3::tail).
Proof.
  intros Ht Hx [w [v [H Hv]]]. exists (expD x t::w),v; split; [|exact Hv].
  rewrite scan_exp by assumption. unfold prepend; rewrite H; reflexivity.
Qed.
Lemma good_cheap t x c tail : 0<t -> valid x=true -> expensive c=false ->
  Good (chT x t) c tail -> Good t x (c::tail).
Proof.
  intros Ht Hx Hc [w [v [H Hv]]]. exists (S2::w),v; split; [|exact Hv].
  rewrite scan_cheap by assumption. unfold prepend; rewrite H; reflexivity.
Qed.

(** Lockstep is independent of the frontier-exit arithmetic.  The later
    scan either has a cheaper head or is ahead by at least one call. *)
Lemma lockstep (exit : FreshExit) tail : forall t x w v y u,
  scan t x tail=Some (w,v) -> 25<=v -> valid y=true -> t<=u ->
  (hcost y<=hcost x \/ t+1<=u) -> Good u y w.
Proof.
  induction tail as [|c tail IH]; intros t x w v y u H Hv Hy Htu Hd;
    destruct (scan_valid _ _ _ _ _ H) as [Hx Ht].
  - rewrite (scan_last _ _ Ht Hx) in H. inversion H; subst w v; clear H.
    assert (Ht2 : 2<=t) by (eapply frontier_positive; [exact Hx|lia]).
    destruct (frD_cases x t) as [E|[E|E]]; rewrite E.
    + apply good_cheap; try assumption; try reflexivity; try lia.
      apply exit; [reflexivity|exact Hv|]. cbn [pen].
      pose proof (frontier_cheap _ _ _ _ Hx Hy Ht2 Htu); lia.
    + apply good_cheap; try assumption; try reflexivity; try lia.
      apply exit; [reflexivity|exact Hv|]. cbn [pen].
      pose proof (frontier_loose _ _ _ _ Hx Hy Ht2 Htu Hd E); lia.
    + apply good_exp; try assumption; try lia.
      apply exit; [reflexivity|exact Hv|]. cbn [pen].
      pose proof (frontier_expensive _ _ _ _ Hx Hy Ht2 Htu Hd E); lia.
  - destruct (expensive c) eqn:Hc.
    + assert (Ec : c=S3) by (destruct c; cbn in Hc; congruence); subst c.
      assert (Ht2 : 2<=t).
      { cbn [scan] in H. destruct (t =? 0); [discriminate|]. rewrite Hx in H.
        cbn [expensive] in H. destruct (t <? 2) eqn:E; [discriminate|].
        apply N.ltb_ge; exact E. }
      rewrite (scan_exp _ _ _ Ht2 Hx) in H.
      destruct (prepend_some _ _ _ _ H) as [w' [Hw ->]].
      assert (HE : expT x t<=expT y u) by (apply expensive_compare; assumption).
      assert (HG : expT x t+1<=chT y u) by (apply expensive_gain; assumption).
      destruct (expD_cases x t) as [E|[E|E]]; rewrite E.
      * apply good_cheap; try assumption; try reflexivity; try lia.
        eapply IH; [exact Hw|exact Hv|reflexivity|lia|right; exact HG].
      * apply good_cheap; try assumption; try reflexivity; try lia.
        eapply IH; [exact Hw|exact Hv|reflexivity|lia|right; exact HG].
      * apply good_exp; try assumption; try lia.
        eapply IH; [exact Hw|exact Hv|reflexivity|exact HE|left; reflexivity].
    + rewrite (scan_cheap _ _ _ _ Ht Hx Hc) in H.
      destruct (prepend_some _ _ _ _ H) as [w' [Hw ->]].
      apply good_cheap; try assumption; try reflexivity; try lia.
      eapply IH; [exact Hw|exact Hv|reflexivity|apply cheap_compare; assumption|].
      left; unfold hcost; destruct c; lia.
Qed.

Lemma rich_step (exit : FreshExit) w w' v : WordRich w -> epochF w=Some (w',v) -> WordRich w'.
Proof.
  intros [u [z [H Hz]]] E. rewrite E in H; inversion H; subst.
  unfold WordRich,epochF,Good in *.
  eapply (lockstep exit); [exact E|exact Hz|reflexivity|reflexivity|left; reflexivity].
Qed.

Lemma frontier_compare x t u : valid x=true -> t<=u -> frT x t<=frT x u.
Proof. destruct x; cbn [valid]; intros; try discriminate; token_arith. Qed.
Lemma scan_mono tail : forall t x w v u, scan t x tail=Some (w,v) -> t<=u ->
  exists w' v', scan u x tail=Some (w',v') /\ v<=v'.
Proof.
  induction tail as [|c tail IH]; intros t x w v u H Htu;
    destruct (scan_valid _ _ _ _ _ H) as [Hx Ht].
  - rewrite (scan_last _ _ Ht Hx) in H. inversion H; subst w v.
    exists (frD x u::freshW (frT x u)),(frT x u); split.
    + apply scan_last; [lia|exact Hx].
    + apply frontier_compare; assumption.
  - destruct (expensive c) eqn:Hc.
    + assert (Ec : c=S3) by (destruct c; cbn in Hc; congruence); subst c.
      assert (Ht2 : 2<=t).
      { cbn [scan] in H. destruct (t =? 0); [discriminate|]. rewrite Hx in H.
        cbn [expensive] in H. destruct (t <? 2) eqn:E; [discriminate|].
        apply N.ltb_ge; exact E. }
      rewrite (scan_exp _ _ _ Ht2 Hx) in H.
      destruct (prepend_some _ _ _ _ H) as [w0 [Hw ->]].
      assert (HE : expT x t<=expT x u) by
        (apply expensive_compare; try assumption; left; reflexivity).
      destruct (IH _ _ _ _ _ Hw HE) as [w' [v' [Hw' Hv']]].
      exists (expD x u::w'),v'; split; [|exact Hv'].
      rewrite scan_exp by (try assumption; lia). unfold prepend; rewrite Hw'; reflexivity.
    + rewrite (scan_cheap _ _ _ _ Ht Hx Hc) in H.
      destruct (prepend_some _ _ _ _ H) as [w0 [Hw ->]].
      assert (HE : chT x t<=chT x u) by
        (apply cheap_compare; try assumption; left; reflexivity).
      destruct (IH _ _ _ _ _ Hw HE) as [w' [v' [Hw' Hv']]].
      exists (S2::w'),v'; split; [|exact Hv'].
      rewrite scan_cheap by (try assumption; lia). unfold prepend; rewrite Hw'; reflexivity.
Qed.
Lemma good_mono t x tail u : Good t x tail -> t<=u -> Good u x tail.
Proof.
  intros [w [v [H Hv]]] Htu.
  destruct (scan_mono _ _ _ _ _ _ H Htu) as [w' [v' [E Hv']]].
  exists w',v'; split; [exact E|lia].
Qed.

(** Separating machine semantics and lockstep from the frontier arithmetic. *)
Lemma nonhalt_of_fresh_exit : FreshExit -> ~halts tm c0.
Proof.
  intro exit. destruct seed as [w [Hw HR]].
  eapply multistep_nonhalt.
  - unfold boundary. execute.
  - eapply multistep_nonhalt; [exact Hw|].
    eapply progress_nonhalt_cond with (P:=WordRich) (i0:=w).
    + intros u Hu. destruct Hu as [u' [v [HE Hv]]]. exists u'; split.
      * eapply epoch_sound; exact HE.
      * eapply rich_step; [exact exit| |exact HE]. exists u',v; auto.
    + exact HR.
Qed.

(** Frontier-exit arithmetic. The equivalent recursion 2*postRun(n/3)
    permits a direct power-bound induction without valuations. *)
Open Scope N_scope.

Function postRun (n:N) {measure N.to_nat n} : N :=
  if n =? 0 then 0 else
  if n mod 3 =? 0 then 2*postRun (n/3) else n.
Proof.
  intros; apply Nnat_lt.
  repeat match goal with H : N.eqb _ _ = false |- _ => apply N.eqb_neq in H end.
  lia.
Defined.

Lemma postRun_zero : postRun 0=0.
Proof. rewrite postRun_equation; reflexivity. Qed.

Lemma postRun_free n : n mod 3<>0 -> postRun n=n.
Proof.
  intro H; rewrite postRun_equation.
  destruct (N.eqb_spec n 0); [subst; reflexivity|].
  destruct (N.eqb_spec (n mod 3) 0); [contradiction|reflexivity].
Qed.

Lemma postRun_div n : 0<n -> n mod 3=0 -> postRun n=2*postRun (n/3).
Proof.
  intros Hn Hd; rewrite postRun_equation.
  destruct (N.eqb_spec n 0); [lia|].
  rewrite Hd; reflexivity.
Qed.

Lemma postRun_double n : postRun (2*n)=2*postRun n.
Proof.
  induction n as [n IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  destruct (N.eq_dec n 0) as [->|Hn]; [rewrite postRun_zero; reflexivity|].
  destruct (N.eq_dec (n mod 3) 0) as [Hd|Hd].
  - assert (Hd2:(2*n) mod 3=0) by (rewrite N.Div0.mul_mod,Hd; reflexivity).
    rewrite (postRun_div (2*n) ltac:(lia) Hd2).
    replace (2*n/3) with (2*(n/3)) by lia.
    rewrite IH by (unfold ltof; apply Nnat_lt; lia).
    rewrite (postRun_div n ltac:(lia) Hd); reflexivity.
  - assert (Hd2:(2*n) mod 3<>0).
    { destruct (mod3 n) as [H|[H|H]]; [contradiction| |];
        rewrite N.Div0.mul_mod,H; discriminate. }
    rewrite (postRun_free _ Hd2),(postRun_free _ Hd); reflexivity.
Qed.

Lemma postRun_expensive n : 0<n -> n mod 3=0 -> postRun n=postRun (2*n/3).
Proof.
  intros Hn Hd; rewrite (postRun_div n Hn Hd).
  replace (2*n/3) with (2*(n/3)) by lia.
  symmetry; apply postRun_double.
Qed.

Lemma postRun_le n : postRun n<=n.
Proof.
  induction n as [n IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  destruct (N.eq_dec n 0) as [->|Hn]; [rewrite postRun_zero; reflexivity|].
  destruct (N.eq_dec (n mod 3) 0) as [Hd|Hd].
  - rewrite (postRun_div n ltac:(lia) Hd).
    pose proof (IH (n/3) ltac:(unfold ltof; apply Nnat_lt; lia)); lia.
  - rewrite (postRun_free _ Hd); reflexivity.
Qed.

Lemma postRun_power_bound n : n^17 <= (postRun n)^27.
Proof.
  induction n as [n IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  destruct (N.eq_dec n 0) as [->|Hn]; [rewrite postRun_zero; reflexivity|].
  destruct (N.eq_dec (n mod 3) 0) as [Hd|Hd].
  - rewrite (postRun_div n ltac:(lia) Hd).
    replace n with (3*(n/3)) at 1 by lia.
    rewrite !N.pow_mul_l.
    apply N.mul_le_mono.
    + vm_compute; discriminate.
    + apply IH; unfold ltof; apply Nnat_lt; lia.
  - rewrite (postRun_free _ Hd); apply N.pow_le_mono_r; lia.
Qed.

Lemma le_postRun n k : k^27<=n^17 -> k<=postRun n.
Proof.
  intro H.
  apply (N.pow_le_mono_l_iff k (postRun n) 27); [discriminate|].
  eapply N.le_trans; [exact H|apply postRun_power_bound].
Qed.

Lemma freshW_mod v : 0<v -> freshW v=
  (if v mod 3 =? 0 then S3 else if v mod 3 =? 1 then S1 else S0)
    ::freshW (v-1-v/3).
Proof.
  intro Hv; rewrite freshW_equation.
  destruct (N.eqb_spec v 0); [lia|]. unfold stDigit.
  destruct (mod3 v) as [H|[H|H]]; rewrite H;
    replace ((v+1) mod 3) with ((v mod 3+1) mod 3)
      by lia;
    rewrite H; reflexivity.
Qed.

Lemma postRun_step v : 0<v -> v mod 3=0 ->
  postRun (v+3)=postRun (v-1-v/3+3).
Proof.
  intros Hv Hr. rewrite postRun_expensive by lia.
  f_equal; lia.
Qed.

Ltac exit_arith :=
  lazy beta iota delta [pen hcost chT expT frT] in *;
  rewrite ?cycE_0,?cycE_1,?cycE_2 in *; lia.

Lemma rich_exit v : forall b u, valid b=true ->
  14*(v+3)+3*pen b<=u+3 -> Good u b (freshW v).
Proof.
  induction v as [v IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros b u Hb Hinv. destruct b; try discriminate;
    cbn [pen] in Hinv.
  all: destruct (N.eq_dec v 0) as [->|Hv].
  all: try (rewrite freshW_zero; unfold Good; eexists; eexists; split;
    [apply scan_last; [lia|reflexivity]|exit_arith]).
  all: assert (Hlt:ltof N N.to_nat (v-1-v/3) v)
    by (unfold ltof; apply Nnat_lt; lia).
  all: rewrite freshW_mod by lia;
    destruct (mod3 v) as [Hr|[Hr|Hr]]; rewrite Hr; cbn [N.eqb Pos.eqb].
  all: first
    [ eapply good_exp; [lia|reflexivity|apply IH; [exact Hlt|reflexivity|exit_arith]]
    | eapply good_cheap; [lia|reflexivity|reflexivity|
        apply IH; [exact Hlt|reflexivity|exit_arith]] ].
Qed.

Lemma phase2_exit v : forall b u, valid b=true -> 4<=postRun (v+3) ->
  7*(v+3)+3*pen b<=u+3 -> Good u b (freshW v).
Proof.
  induction v as [v IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros b u Hb Hside Hinv. pose proof (postRun_le (v+3)) as Hle.
  assert (Hv:0<v) by lia.
  assert (Hlt:ltof N N.to_nat (v-1-v/3) v)
    by (unfold ltof; apply Nnat_lt; lia).
  destruct b; try discriminate; cbn [pen] in Hinv;
    rewrite freshW_mod by lia;
    destruct (mod3 v) as [Hr|[Hr|Hr]]; rewrite Hr; cbn [N.eqb Pos.eqb].
  all: first
    [ eapply good_exp; [lia|reflexivity|apply IH; [exact Hlt|reflexivity|
        rewrite <-postRun_step by assumption; exact Hside|exit_arith]]
    | eapply good_cheap; [lia|reflexivity|reflexivity|
        apply rich_exit; [reflexivity|exit_arith]] ].
Qed.

Lemma phase1_exit v : forall b u, valid b=true -> 30<=postRun (v+3) ->
  5*(v+3)+6*pen b<=2*(u+3) -> Good u b (freshW v).
Proof.
  induction v as [v IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros b u Hb Hside Hinv. pose proof (postRun_le (v+3)) as Hle.
  assert (Hv:27<=v) by lia.
  assert (Hlt:ltof N N.to_nat (v-1-v/3) v)
    by (unfold ltof; apply Nnat_lt; lia).
  assert (Hs:4<=postRun (v-1-v/3+3)).
  { apply le_postRun. eapply N.le_trans with (m:=20^17).
    - vm_compute; discriminate.
    - apply N.pow_le_mono_l; lia. }
  destruct b; try discriminate; cbn [pen] in Hinv;
    rewrite freshW_mod by lia;
    destruct (mod3 v) as [Hr|[Hr|Hr]]; rewrite Hr; cbn [N.eqb Pos.eqb].
  all: first
    [ eapply good_exp; [lia|reflexivity|apply IH; [exact Hlt|reflexivity|
        rewrite <-postRun_step by lia; exact Hside|exit_arith]]
    | eapply good_cheap; [lia|reflexivity|reflexivity|
        apply phase2_exit; [reflexivity|exact Hs|exit_arith]] ].
Qed.

Lemma phase0_exit v : forall b u, valid b=true -> 400<=postRun (v+3) ->
  v+2*v*pen b<=u -> Good u b (freshW v).
Proof.
  induction v as [v IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros b u Hb Hside Hinv. pose proof (postRun_le (v+3)) as Hle.
  assert (Hv:397<=v) by lia.
  assert (Hlt:ltof N N.to_nat (v-1-v/3) v)
    by (unfold ltof; apply Nnat_lt; lia).
  assert (Hs:30<=postRun (v-1-v/3+3)).
  { apply le_postRun. eapply N.le_trans with (m:=266^17).
    - vm_compute; discriminate.
    - apply N.pow_le_mono_l; lia. }
  destruct b; try discriminate; cbn [pen] in Hinv;
    rewrite freshW_mod by lia;
    destruct (mod3 v) as [Hr|[Hr|Hr]]; rewrite Hr; cbn [N.eqb Pos.eqb].
  all: first
    [ eapply good_exp; [lia|reflexivity|apply IH; [exact Hlt|reflexivity|
        rewrite <-postRun_step by lia; exact Hside|exit_arith]]
    | eapply good_cheap; [lia|reflexivity|reflexivity|
        apply phase1_exit; [reflexivity|exact Hs|exit_arith]] ].
Qed.

Lemma fresh_exit_large v b u : valid b=true -> 14000<=v ->
  v+2*v*pen b<=u -> Good u b (freshW v).
Proof.
  intros Hb Hv Hu; apply phase0_exit; [exact Hb| |exact Hu].
  apply le_postRun; eapply N.le_trans with (m:=14003^17).
  - vm_compute; discriminate.
  - apply N.pow_le_mono_l; lia.
Qed.

(** Frontier-only evaluation: the fresh input is unfolded on demand and the
    output tape is not constructed. Only a [Some] answer is used. *)
Fixpoint exitFuel (fuel:nat) (v:N) (b:Sym) (u:N) : option N :=
  match fuel with
  | O=>None
  | S fuel=>
      if u =? 0 then None else if valid b then
      if v =? 0 then Some (frT b u) else
      if v mod 3 =? 0 then
        if u <? 2 then None else exitFuel fuel (v-1-v/3) S0 (expT b u)
      else exitFuel fuel (v-1-v/3)
        (if v mod 3 =? 1 then S1 else S0) (chT b u)
      else None
  end.

Lemma exitFuel_good fuel : forall v b u z,
  exitFuel fuel v b u=Some z ->25<=z ->Good u b (freshW v).
Proof.
  induction fuel as [|fuel IH]; intros v b u z H Hz;
    cbn [exitFuel] in H; [discriminate|].
  destruct (N.eqb_spec u 0) as [Hu|Hu]; [discriminate|].
  destruct (valid b) eqn:Hb; [|discriminate].
  destruct (N.eqb_spec v 0) as [->|Hv].
  - inversion H; subst z; rewrite freshW_zero; unfold Good.
    eexists; eexists; split; [apply scan_last; [lia|exact Hb]|exact Hz].
  - rewrite freshW_mod by lia.
    destruct (v mod 3 =? 0) eqn:Hr.
    + destruct (N.ltb_spec u 2); [discriminate|].
      apply good_exp; [lia|exact Hb|eapply IH; eassumption].
    + apply good_cheap; [lia|exact Hb| |eapply IH; eassumption].
      destruct (v mod 3 =? 1); reflexivity.
Qed.

Definition exitOK (v:N) (b:Sym) (u:N) : bool :=
  match exitFuel 64 v b u with Some z=>25<=?z | None=>false end.
Lemma exitOK_good v b u : exitOK v b u=true ->Good u b (freshW v).
Proof.
  unfold exitOK; destruct (exitFuel 64 v b u) as [z|] eqn:H;
    [|discriminate]. intro Hz; apply N.leb_le in Hz.
  eapply exitFuel_good; eassumption.
Qed.
Definition exitCheck v := (v<?25) ||
  (exitOK v S0 v && exitOK v S2 v && exitOK v S1 (3*v)).
Fixpoint exitRange (count:nat) (start:N) : bool :=
  match count with O=>true | S count=>exitCheck start && exitRange count (start+1) end.

Lemma exitRange_spec count : forall start v,
  exitRange count start=true ->start<=v<start+N.of_nat count ->exitCheck v=true.
Proof.
  induction count as [|count IH]; intros start v H Hv; [cbn in Hv; lia|].
  cbn [exitRange] in H; apply Bool.andb_true_iff in H as [Hs Hrest].
  destruct (N.eq_dec v start) as [->|Hne]; [exact Hs|].
  apply (IH (start+1)); [exact Hrest|]. rewrite Nat2N.inj_succ in Hv; lia.
Qed.

Lemma exit_small_check : exitRange 14000 0=true.
Proof. vm_compute; reflexivity. Qed.

Lemma fresh_exit_small v b u : valid b=true ->25<=v ->v<14000 ->
  v+2*v*pen b<=u ->Good u b (freshW v).
Proof.
  intros Hb Hv Hlt Hu.
  assert (Ecount : N.of_nat 14000=14000) by (vm_compute; reflexivity).
  pose proof (exitRange_spec 14000 0 v exit_small_check ltac:(rewrite Ecount; lia)) as H.
  unfold exitCheck in H. apply Bool.orb_true_iff in H as [H|H].
  - apply N.ltb_lt in H; lia.
  - apply Bool.andb_true_iff in H as [H02 H1].
    apply Bool.andb_true_iff in H02 as [H0 H2].
    destruct b; try discriminate; cbn [pen] in Hu.
    + eapply good_mono; [apply exitOK_good; exact H0|lia].
    + eapply good_mono; [apply exitOK_good; exact H1|lia].
    + eapply good_mono; [apply exitOK_good; exact H2|lia].
Qed.

Theorem fresh_exit : FreshExit.
Proof.
  intros v b u Hb Hv Hu. destruct (N.le_gt_cases 14000 v) as [Hlarge|Hsmall].
  - apply fresh_exit_large; assumption.
  - apply fresh_exit_small; assumption.
Qed.


Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_of_fresh_exit, fresh_exit. Qed.

End TM55.


Print Assumptions TM28.nonhalt.
Print Assumptions TM32.nonhalt.
Print Assumptions TM38.nonhalt.
Print Assumptions TM54.nonhalt.
Print Assumptions TM55.nonhalt.
