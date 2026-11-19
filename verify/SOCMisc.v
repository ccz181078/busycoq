(* SOC A1--A7: independent nonhalting proofs, with shared arithmetic.
   TM1, TM5 and TM6 use literal L/R mirrors; the others use the originals.
   Each machine and its final theorem are in the same TM1--TM7 module.
   This standalone file requires only BusyCoq and the Coq standard library. *)
From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3 Longitudinal.
Require Import String Bool List Arith PeanoNat ZifyNat Lia Wf_nat.
Import ListNotations.

(* A1/A2 shared guards and machine proofs. *)
(* Shared: soc_pair_a123_word_rules.v/PairWord. *)
Module PairWord.
Definition bit (b:bool) : sym := if b then 1 else 0.
Fixpoint pairs (w:list bool) : list sym := match w with
  | [] => [] | b::u => bit b::1::pairs u end.
Definition data (w:list bool) : side := 0inf <* [1] <* pairs w.
Definition insert (b:bool) (r:side) := if b then [1] *> r else r.
Fixpoint inc (w:list bool) : list bool*bool := match w with
  | [] => ([false],false)
  | false::u => (true::u,false)
  | true::[] => ([false],true)
  | true::false::u => (false::true::u,false)
  | true::true::[] => ([false;false],true)
  | true::true::b::u => let '(v,e):=inc u in (false::false::false::v,e)
  end.
Definition push0 n w := repeat false n ++ w.
Lemma pairs_push0 n w : pairs (push0 n w)=<[1;0]^^n++pairs w.
Proof.
  unfold push0; induction n; cbn [repeat app pairs bit lpow];
    [reflexivity|now rewrite IHn].
Qed.
Lemma data_push0 n w : data (push0 n w)=data w <* <[1;0]^^n.
Proof. unfold data; rewrite pairs_push0; st; reflexivity. Qed.
Lemma ones4_twice n : [1;1;1;1]^^n=[1;1]^^(n*2).
Proof. rewrite lpow_mul; reflexivity. Qed.
Lemma insert_scan b n r : insert b ([1;1]^^n *> r)=[1;1]^^n *> insert b r.
Proof.
  destruct b; [|reflexivity].
  change (1 >> [1;1]^^n *> r=[1;1]^^n *> 1 >> r).
  apply lpow_shift21e.
Qed.
End PairWord.

(* Shared: SOCPair12Guard.v/PairGuard. *)
Module PairGuard.
Open Scope nat_scope.

Definition bit_value (b:bool) : nat := if b then 1 else 0.
Definition zero_bit (b:bool) : nat := if b then 0 else 1.

(* Each plane picks one residue of the original pair word, at radix four.
   Only positions 0 and 1 in a triple are numerical; position 2 is a marker. *)
Fixpoint digit_plane (f:bool->nat) (i:nat) (w:list bool) : nat :=
  match w with
  | [] => 0
  | b::u => match i with
            | 0 => f b + 4*digit_plane f 2 u
            | S j => digit_plane f j u
            end
  end.

Fixpoint width (w:list bool) : nat :=
  match w with
  | [] => 0
  | [_] => 1
  | [_;_] => 2
  | _::_::_::u => 2+width u
  end.

Definition value (w:list bool) : nat :=
  digit_plane bit_value 0 w + 2*digit_plane bit_value 1 w.
Definition gap0 (w:list bool) : nat :=
  1 + digit_plane zero_bit 0 w + 2*digit_plane zero_bit 1 w.
Definition gap1 (w:list bool) : nat :=
  2 + 2*digit_plane zero_bit 0 w + 4*digit_plane zero_bit 2 w.
Definition gap2 (w:list bool) : nat :=
  4 + 4*digit_plane zero_bit 1 w + 8*digit_plane zero_bit 2 w.

Lemma gap_bounds w : 1<=gap0 w /\ 2<=gap1 w /\ 4<=gap2 w.
Proof. unfold gap0,gap1,gap2; lia. Qed.

Lemma gap2_four w :
  gap2 w=4*(1+digit_plane zero_bit 1 w+2*digit_plane zero_bit 2 w).
Proof. unfold gap2; lia. Qed.

Lemma value_gap0 w : value w+gap0 w=2^width w.
Proof.
  revert w; fix IH 1; intros w.
  destruct w as [|a [|b [|c u]]].
  - reflexivity.
  - destruct a; reflexivity.
  - destruct a,b; reflexivity.
  - pose proof (IH u) as H.
    unfold value,gap0 in *.
    cbn [digit_plane width Nat.pow].
    destruct a,b; cbn [bit_value zero_bit]; rewrite Nat.pow_add_r; cbn; lia.
Qed.

(* The retention bounds also hold at the finite left boundary.  Keeping
   this lemma unconditional makes it reusable independently of capacity. *)
Lemma inc_half w v e : PairWord.inc w=(v,e) ->
  gap1 w<=2*gap1 v /\ gap2 w<=2*gap2 v.
Proof.
  revert w v e; fix IH 1; intros w v e E.
  destruct w as [|b0 w].
  - cbn [PairWord.inc] in E; inversion E; subst.
    unfold gap1,gap2; cbn [digit_plane zero_bit]; lia.
  - destruct b0.
    + destruct w as [|b1 w].
      * cbn [PairWord.inc] in E; inversion E; subst.
        unfold gap1,gap2; cbn [digit_plane zero_bit]; lia.
      * destruct b1.
        -- destruct w as [|b w].
           ++ cbn [PairWord.inc] in E; inversion E; subst.
              unfold gap1,gap2; cbn [digit_plane zero_bit]; lia.
           ++ cbn [PairWord.inc] in E.
              destruct (PairWord.inc w) as [u d] eqn:F.
              inversion E; subst v e.
              pose proof (IH w u d F) as [H1 H2].
              unfold gap1,gap2 in *.
              cbn [digit_plane] in *.
              destruct b; cbn [zero_bit] in *; lia.
        -- cbn [PairWord.inc] in E; inversion E; subst.
           unfold gap1,gap2; cbn [digit_plane zero_bit]; lia.
    + cbn [PairWord.inc] in E; inversion E; subst.
      unfold gap1,gap2; cbn [digit_plane zero_bit]; lia.
Qed.

Lemma inc_interior w v e : PairWord.inc w=(v,e) -> 1<gap0 w ->
  e=false /\ length v=length w /\ gap0 v+1=gap0 w.
Proof.
  revert w v e; fix IH 1; intros w v e E H.
  destruct w as [|b0 w].
  - unfold gap0 in H; cbn [digit_plane] in H; lia.
  - destruct b0.
    + destruct w as [|b1 w].
      * unfold gap0 in H; cbn [digit_plane zero_bit] in H; lia.
      * destruct b1.
        -- destruct w as [|b w].
           ++ unfold gap0 in H; cbn [digit_plane zero_bit] in H; lia.
           ++ assert (Hu:1<gap0 w).
              { unfold gap0 in *; cbn [digit_plane zero_bit] in *; lia. }
              cbn [PairWord.inc] in E.
              destruct (PairWord.inc w) as [u d] eqn:F.
              inversion E; subst v e.
              destruct (IH w u d F Hu) as [Hd [Hl Hg]].
              subst d; split; [reflexivity|].
              split; [cbn [length]; lia|].
              unfold gap0 in *; cbn [digit_plane zero_bit] in *; lia.
        -- cbn [PairWord.inc] in E; inversion E; subst.
           split; [reflexivity|].
           split; [reflexivity|].
           unfold gap0; cbn [digit_plane zero_bit]; lia.
    + cbn [PairWord.inc] in E; inversion E; subst.
      split; [reflexivity|].
      split; [reflexivity|].
      unfold gap0; cbn [digit_plane zero_bit]; lia.
Qed.

(* Exactly q calls of the existing word operation, with no inserted right
   bit.  The capacity hypothesis below also rules out left extension. *)
Inductive inc_steps : nat -> list bool -> list bool -> Prop :=
| inc_steps_zero w : inc_steps 0 w w
| inc_steps_succ q w u v :
    PairWord.inc w=(u,false) -> inc_steps q u v -> inc_steps (S q) w v.

Lemma inc_steps_interior q w : q<gap0 w ->
  exists v, inc_steps q w v /\ length v=length w /\ gap0 v+q=gap0 w.
Proof.
  revert w; induction q as [|q IH]; intros w H.
  - exists w; split; [constructor|]; split; [reflexivity|lia].
  - destruct (PairWord.inc w) as [u e] eqn:E.
    assert (Hint:1<gap0 w) by lia.
    destruct (inc_interior w u e E Hint) as [He [Hl Hg]].
    subst e.
    assert (Hu:q<gap0 u) by lia.
    destruct (IH u Hu) as [v [Hsteps [Hlen Hgap]]].
    exists v; split.
    + econstructor; eassumption.
    + split; lia.
Qed.

End PairGuard.

(* Shared: SOCPair12Carry.v/PairCarry. *)
Module PairCarry.
Import PairGuard.
Open Scope nat_scope.

Lemma value_triple a b marker w :
  value (a::b::marker::w)=bit_value a+2*bit_value b+4*value w.
Proof. unfold value; cbn [digit_plane]; lia. Qed.

Lemma prefix_value_bound t rho :
  length rho=3*t -> value rho<4^t.
Proof.
  revert rho; induction t as [|t IH]; intros rho Hlen.
  - destruct rho.
    + change (0<1); lia.
    + cbn in Hlen; lia.
  - destruct rho as [|a [|b [|marker rho]]]; cbn [length] in Hlen;
      try lia.
    assert (Htail:length rho=3*t) by lia.
    pose proof (IH rho Htail) as H.
    rewrite value_triple; cbn [Nat.pow].
    destruct a,b; cbn [bit_value]; lia.
Qed.

Lemma inc_steps_trans p q w u v :
  inc_steps p w u -> inc_steps q u v -> inc_steps (p+q) w v.
Proof.
  intros H; induction H; intro K; cbn [Nat.add].
  - exact K.
  - econstructor; [eassumption|apply IHinc_steps; exact K].
Qed.

Lemma inc_steps_add_inv p q w v :
  inc_steps (p+q) w v ->
  exists u, inc_steps p w u /\ inc_steps q u v.
Proof.
  revert w v; induction p as [|p IH]; intros w v Hsteps.
  - exists w; split; [constructor|exact Hsteps].
  - cbn [Nat.add] in Hsteps.
    inversion Hsteps as [|q0 w0 mid v0 E Hrest]; subst.
    destruct (IH mid v Hrest) as [u [Hp Hq]].
    exists u; split; [econstructor; eassumption|exact Hq].
Qed.

Lemma inc_split t rho u v :
  length rho=3*t -> PairWord.inc (rho++u)=(v,false) ->
  exists rho' u' c,
    v=rho'++u' /\ length rho'=3*t /\
    inc_steps c u u' /\ c<=1 /\
    c*4^t+value rho'=value rho+1.
Proof.
  revert rho u v; induction t as [|t IH]; intros rho u v Hlen E.
  - destruct rho; [|cbn in Hlen; lia].
    exists (@nil bool),v,1; cbn [app length Nat.pow value digit_plane] in *.
    repeat split; try lia.
    econstructor; [exact E|constructor].
  - destruct rho as [|a [|b [|marker rho]]]; cbn [length] in Hlen;
      try lia.
    assert (Htail:length rho=3*t) by lia.
    destruct a.
    + destruct b.
      * cbn [app PairWord.inc] in E.
        destruct (PairWord.inc (rho++u)) as [v0 e] eqn:E0.
        inversion E; subst v e.
        destruct (IH rho u v0 Htail E0) as
          [rho' [u' [c [Hv [Hl [Hs [Hc Hval]]]]]]].
        subst v0.
        exists (false::false::false::rho'),u',c.
        split; [reflexivity|].
        split; [cbn [length]; lia|].
        split; [exact Hs|].
        split; [exact Hc|].
        rewrite !value_triple; cbn [bit_value Nat.pow]; nia.
      * cbn [app PairWord.inc] in E; inversion E; subst v.
        exists (false::true::marker::rho),u,0.
        split; [reflexivity|].
        split; [cbn [length]; lia|].
        split; [constructor|].
        split; [lia|].
        rewrite !value_triple; cbn [bit_value]; lia.
    + cbn [app PairWord.inc] in E; inversion E; subst v.
      exists (true::b::marker::rho),u,0.
      split; [reflexivity|].
      split; [cbn [length]; lia|].
      split; [constructor|].
      split; [lia|].
      rewrite !value_triple; cbn [bit_value]; lia.
Qed.

Lemma inc_steps_split t q rho u v :
  length rho=3*t -> inc_steps q (rho++u) v ->
  exists rho' u' c,
    v=rho'++u' /\ length rho'=3*t /\
    inc_steps c u u' /\ c*4^t+value rho'=value rho+q.
Proof.
  revert rho u v; induction q as [|q IH]; intros rho u v Hlen Hsteps.
  - inversion Hsteps; subst.
    exists rho,u,0; repeat split; try assumption; try lia; constructor.
  - inversion Hsteps as [|q0 w mid v0 E Hrest]; subst.
    destruct (inc_split t rho u mid Hlen E) as
      [rho1 [u1 [c1 [Hmid [Hl1 [Hs1 [Hc1 Hv1]]]]]]].
    subst mid.
    destruct (IH rho1 u1 v Hl1 Hrest) as
      [rho2 [u2 [c2 [Hv [Hl2 [Hs2 Hv2]]]]]].
    exists rho2,u2,(c1+c2).
    split; [exact Hv|].
    split; [exact Hl2|].
    split; [eapply inc_steps_trans; eassumption|nia].
Qed.

Lemma carry_bound t rho rho' c q h :
  length rho=3*t ->
  c*4^t+value rho'=value rho+q -> q<=h*4^t -> c<=h.
Proof.
  intros Hlen Hval Hq.
  pose proof (prefix_value_bound t rho Hlen).
  assert (4^t<>0) by (apply Nat.pow_nonzero; lia).
  nia.
Qed.

Lemma inc_steps_split_bounded t q h rho u v :
  length rho=3*t -> inc_steps q (rho++u) v -> q<=h*4^t ->
  exists rho' u' c,
    v=rho'++u' /\ length rho'=3*t /\ inc_steps c u u' /\
    c<=h /\ c*4^t+value rho'=value rho+q.
Proof.
  intros Hlen Hsteps Hq.
  destruct (inc_steps_split t q rho u v Hlen Hsteps) as
    [rho' [u' [c [Hv [Hl [Hs He]]]]]].
  exists rho',u',c; repeat split; try assumption.
  exact (carry_bound t rho rho' c q h Hlen He Hq).
Qed.

End PairCarry.

(* Shared: SOCPair12Prefix.v/PairPrefix. *)
Module PairPrefix.
Import PairGuard.
Open Scope nat_scope.

Lemma zero_bit_bound b : zero_bit b<=1.
Proof. destruct b; cbn [zero_bit]; lia. Qed.

(* One near-head bit rotates the three phases; the third phase scales. *)
Lemma gap_cons b w :
  gap0 (b::w)+1=gap1 w+zero_bit b /\
  gap1 (b::w)+2=gap2 w+2*zero_bit b /\
  gap2 (b::w)=4*gap0 w.
Proof. unfold gap0,gap1,gap2; cbn [digit_plane]; lia. Qed.

Lemma gap_triple a b c w :
  gap0 (a::b::c::w)+3=4*gap0 w+zero_bit a+2*zero_bit b /\
  gap1 (a::b::c::w)+6=4*gap1 w+2*zero_bit a+4*zero_bit c /\
  gap2 (a::b::c::w)+12=4*gap2 w+4*zero_bit b+8*zero_bit c.
Proof. unfold gap0,gap1,gap2; cbn [digit_plane]; lia. Qed.

Lemma gap_triple_upper a b c w :
  gap0 (a::b::c::w)<=4*gap0 w /\
  gap1 (a::b::c::w)<=4*gap1 w /\
  gap2 (a::b::c::w)<=4*gap2 w.
Proof.
  pose proof (gap_triple a b c w).
  pose proof (zero_bit_bound a); pose proof (zero_bit_bound b).
  pose proof (zero_bit_bound c); lia.
Qed.

(* This is the aligned-prefix inequality needed before the high carry cut.
   The prefix may contain arbitrary markers and a completely full value. *)
Lemma prefix_triples_upper t z w : length z=3*t ->
  gap0 (z++w)<=4^t*gap0 w /\
  gap1 (z++w)<=4^t*gap1 w /\
  gap2 (z++w)<=4^t*gap2 w.
Proof.
  revert z; induction t as [|t IH]; intros z Hl.
  - destruct z; cbn in Hl; [cbn; lia|lia].
  - destruct z as [|a [|b [|c z]]]; cbn [length] in Hl; try lia.
    pose proof (IH z ltac:(lia)) as HH.
    pose proof (gap_triple_upper a b c (z++w)) as HT.
    cbn [app Nat.pow]; nia.
Qed.

Lemma triple_preserve H a b c w : 4<=H ->
  H<=gap0 w -> H<=gap1 w -> H<=gap2 w ->
  H<=gap0 (a::b::c::w) /\ H<=gap1 (a::b::c::w) /\
  H<=gap2 (a::b::c::w).
Proof. intros; pose proof (gap_triple a b c w); lia. Qed.

(* Exact short-prefix identities from the n=0 shifted branch. *)
Lemma gap_01 w :
  gap0 (false::true::w)+2=gap2 w /\
  gap1 (false::true::w)=4*gap0 w /\
  gap2 (false::true::w)+4=4*gap1 w.
Proof. unfold gap0,gap1,gap2; cbn [digit_plane zero_bit]; lia. Qed.

Lemma gap_zero4 w :
  gap0 (false::false::false::false::w)=4*gap1 w /\
  gap1 (false::false::false::false::w)=4*gap2 w /\
  gap2 (false::false::false::false::w)=16*gap0 w.
Proof. unfold gap0,gap1,gap2; cbn [digit_plane zero_bit]; lia. Qed.

Lemma zero4_eight w :
  8<=gap0 (false::false::false::false::w) /\
  8<=gap1 (false::false::false::false::w) /\
  8<=gap2 (false::false::false::false::w).
Proof. pose proof (gap_zero4 w); pose proof (gap_bounds w); lia. Qed.

(* Seven or more arbitrary bits amplify the suffix guard.  Stripping
   triples leaves only the lengths 7, 8, and 9 as arithmetic base cases. *)
Lemma long_prefix H z w : 4<=H -> 7<=length z ->
  H+1<=gap0 w -> H+1<=gap1 w -> H+1<=gap2 w ->
  2*H<=gap0 (z++w) /\ 2*H<=gap1 (z++w) /\ 2*H<=gap2 (z++w).
Proof.
  intro HP; revert z; fix IH 1; intros z Hl H0 H1 H2.
  destruct z as [|a [|b [|c z]]]; cbn [length] in Hl; try lia.
  destruct (Nat.le_gt_cases 7 (length z)) as [HL|HS].
  - destruct (IH z HL H0 H1 H2) as [HH0 [HH1 HH2]].
    cbn [app]; apply triple_preserve; lia.
  - destruct z as [|d [|e [|f [|g [|h [|i [|j q]]]]]]];
      cbn [length] in Hl,HS; try lia.
    all: unfold gap0,gap1,gap2 in *; cbn [app digit_plane] in *; lia.
Qed.

Lemma short_01_guard H w v e : PairWord.inc w=(v,e) ->
  4*H+2<=gap0 w -> 4*H+2<=gap1 w -> 4*H+2<=gap2 w ->
  2*H<=gap0 (false::true::v) /\
  2*H<=gap1 (false::true::v) /\
  2*H<=gap2 (false::true::v).
Proof.
  intros E H0 H1 H2.
  pose proof (inc_half w v e E) as HH.
  pose proof (inc_interior w v e E ltac:(lia)) as HI.
  pose proof (gap2_four w) as HF.
  pose proof (gap_01 v) as HP; lia.
Qed.

(* The marker contribution used by ordinary entry needs neither a
   particular numerical encoding nor an exact final length residue. *)
Lemma zero_marker_bounds k w : 3*k<=length w ->
  digit_plane bit_value 2 w=0 ->
  4^k+1<=gap1 w /\ 2*4^k+2<=gap2 w.
Proof.
  revert w; induction k as [|k IH]; intros w Hl Hz.
  - pose proof (gap_bounds w); cbn [Nat.pow]; lia.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    cbn [digit_plane] in Hz; destruct c; cbn [bit_value] in Hz; try lia.
    pose proof (IH w ltac:(lia) ltac:(lia)) as HH.
    pose proof (gap_triple a b false w) as HT.
    cbn [zero_bit] in HT; cbn [Nat.pow]; lia.
Qed.
End PairPrefix.

(* Shared: SOCPair12Overflow.v/PairOverflow. *)
Module PairOverflow.
Import PairGuard.
Open Scope nat_scope.

Lemma width_length k p w : p<=2 -> length w=3*k+p -> width w=2*k+p.
Proof.
  revert w; induction k as [|k IH]; intros w Hp Hl.
  - destruct p as [|[|[|p]]]; try lia;
      destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia;
      reflexivity.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    cbn [width]; rewrite (IH w Hp ltac:(lia)); lia.
Qed.

Lemma digit_plane_zeros n i : digit_plane bit_value i (repeat false n)=0.
Proof.
  revert i; induction n as [|n IH]; intros [|i]; cbn [repeat digit_plane bit_value];
    rewrite ?IH; reflexivity.
Qed.

Lemma value_zeros n : value (repeat false n)=0.
Proof. unfold value; rewrite !digit_plane_zeros; reflexivity. Qed.

Lemma width_zeros k p : p<=2 -> width (repeat false (3*k+p))=2*k+p.
Proof. intro Hp; apply width_length; [exact Hp|apply repeat_length]. Qed.

Lemma gap0_zeros k p : p<=2 -> gap0 (repeat false (3*k+p))=2^(2*k+p).
Proof.
  intro Hp; pose proof (value_gap0 (repeat false (3*k+p))) as H.
  rewrite value_zeros, (width_zeros k p Hp) in H; exact H.
Qed.

(* The only operation on old marker bits is clearing them during a carry. *)
Lemma inc_marker_monotone w v e : PairWord.inc w=(v,e) ->
  digit_plane bit_value 2 v<=digit_plane bit_value 2 w.
Proof.
  revert w v e; fix IH 1; intros w v e E.
  destruct w as [|a w].
  - cbn [PairWord.inc] in E; inversion E; subst; reflexivity.
  - destruct a.
    + destruct w as [|b w].
      * cbn [PairWord.inc] in E; inversion E; subst; reflexivity.
      * destruct b.
        -- destruct w as [|c w].
           ++ cbn [PairWord.inc] in E; inversion E; subst; reflexivity.
           ++ cbn [PairWord.inc] in E.
              destruct (PairWord.inc w) as [u d] eqn:F; inversion E; subst v e.
              pose proof (IH w u d F).
              cbn [digit_plane bit_value]; lia.
        -- cbn [PairWord.inc] in E; inversion E; subst; reflexivity.
    + cbn [PairWord.inc] in E; inversion E; subst; reflexivity.
Qed.

Lemma inc_marker_zero w v e : PairWord.inc w=(v,e) ->
  digit_plane bit_value 2 w=0 -> digit_plane bit_value 2 v=0.
Proof. intros E H; pose proof (inc_marker_monotone w v e E); lia. Qed.

Lemma inc_steps_marker_zero q w v : inc_steps q w v ->
  digit_plane bit_value 2 w=0 -> digit_plane bit_value 2 v=0.
Proof.
  intro H; induction H; intro Hz; [exact Hz|].
  apply IHinc_steps; eapply inc_marker_zero; eassumption.
Qed.

(* At capacity, every numerical bit is full.  The complete carry erases
   every marker as well, including markers initially equal to one. *)
Lemma inc_at_capacity k p w : p<=2 -> length w=3*k+p -> gap0 w=1 ->
  PairWord.inc w=
  match p with
  | 0 => (repeat false (3*k+1),false)
  | _ => (repeat false (3*k+p),true)
  end.
Proof.
  revert w; induction k as [|k IH]; intros w Hp Hl Hg.
  - destruct p as [|[|[|p]]]; try lia;
      destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    all: repeat match goal with b:bool |- _ => destruct b end;
      unfold gap0 in Hg; cbn [digit_plane zero_bit] in Hg; try lia; reflexivity.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    assert (Ha:a=true /\ b=true /\ gap0 w=1).
    { unfold gap0 in *; cbn [digit_plane] in Hg.
      destruct a,b; cbn [zero_bit] in Hg; lia. }
    destruct Ha as [-> [-> Htail]].
    cbn [PairWord.inc]; rewrite (IH w Hp ltac:(lia) Htail).
    destruct p.
    + replace (3*S k+1) with (3+(3*k+1)) by lia; reflexivity.
    + replace (3*S k+S p) with (3+(3*k+S p)) by lia; reflexivity.
Qed.

(* gap0(w)-1 earlier calls are strictly interior; the next call is exactly
   the phase-dependent capacity event just characterized. *)
Lemma first_capacity k p w : p<=2 -> length w=3*k+p -> exists u,
  inc_steps (gap0 w-1) w u /\ length u=length w /\ gap0 u=1 /\
  PairWord.inc u=
  match p with
  | 0 => (repeat false (3*k+1),false)
  | _ => (repeat false (3*k+p),true)
  end.
Proof.
  intros Hp Hl; pose proof (gap_bounds w) as HB.
  destruct (inc_steps_interior (gap0 w-1) w ltac:(lia))
    as [u [HS [Hlen Hgap]]].
  assert (Hu:gap0 u=1) by lia.
  exists u; split; [exact HS|]; split; [exact Hlen|]; split; [exact Hu|].
  apply inc_at_capacity; [exact Hp|lia|exact Hu].
Qed.
End PairOverflow.

(* Shared: SOCPair12Right.v/Pair12Right. *)
Module Pair12Right.
Import PairWord PairGuard.
Local Open Scope sym_scope.
Definition d0 : list sym := [0;0;0;0].
Definition d1 : list sym := [1;0;0;0].
Definition ds : list sym := [0;0;0;1].
Definition C (QR:Q) w (r:side) := data w <* <[1;0] {{QR}}> r.

Inductive RC (one:list sym) : nat -> side -> Prop :=
| RC_zero : RC one 0 (0inf)%sym
| RC_d0 n r : RC one n r -> RC one (n*2) (d0 *> r)
| RC_d1 n r : RC one n r -> RC one (1+n*2) (one *> r).

Inductive FC (one:list sym) (tail:side) : nat -> nat -> side -> Prop :=
| FC_nil : FC one tail 0 0 tail
| FC_d0 k n r : FC one tail k n r -> FC one tail (S k) (n*2) (d0 *> r)
| FC_d1 k n r : FC one tail k n r -> FC one tail (S k) (1+n*2) (one *> r).

Lemma RC_zero_unique one r : RC one 0 r -> r=(0inf)%sym.
Proof.
  intro H; remember 0%nat as n eqn:E; induction H; try lia.
  - reflexivity.
  - assert (n=0%nat) by lia; subst; rewrite IHRC by reflexivity.
    unfold d0; st; reflexivity.
Qed.

Lemma RC_unique one n r s : RC one n r -> RC one n s -> r=s.
Proof.
  intro H; revert s; induction H; intros s Hs.
  { symmetry; now apply RC_zero_unique in Hs. }
  all: inversion Hs; subst; try lia.
  all: try (assert (n=0%nat) by lia; subst;
    rewrite (RC_zero_unique _ _ H); unfold d0; st; reflexivity).
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma FC_unique one tail k n r s : FC one tail k n r -> FC one tail k n s -> r=s.
Proof.
  intro H; revert s; induction H; intros s Hs;
    inversion Hs; subst; try lia; try reflexivity.
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma FC_zero one tail k : FC one tail k 0 (d0^^k *> tail).
Proof.
  induction k; cbn [lpow]; [constructor|].
  rewrite Str_app_assoc; change (FC one tail (S k) (0*2) (d0 *> d0^^k *> tail)).
  now constructor.
Qed.

Lemma FC_full one tail k : FC one tail k (2^k-1) (one^^k *> tail).
Proof.
  induction k; cbn [lpow Nat.pow]; [constructor|].
  rewrite Str_app_assoc.
  replace (2*2^k-1) with (1+(2^k-1)*2)
    by (pose proof (Nat.pow_nonzero 2 k); lia).
  now constructor.
Qed.

Lemma FC_full_unique one tail k r :
  FC one tail k (2^k-1) r -> r=one^^k *> tail.
Proof. intro H; eapply FC_unique; [exact H|apply FC_full]. Qed.

Lemma FC_RC one tail k n r m : FC one tail k n r -> RC one m tail ->
  RC one (n+2^k*m) r.
Proof.
  intros H Hr; induction H; cbn [Nat.pow] in *.
  - replace (0+1*m) with m by lia; exact Hr.
  - replace (n*2+2*2^k*m) with ((n+2^k*m)*2) by nia; now constructor.
  - replace (1+n*2+2*2^k*m) with (1+(n+2^k*m)*2) by nia; now constructor.
Qed.

Lemma RC_zeros one n r k : RC one n r -> RC one (2^k*n) (d0^^k *> r).
Proof. exact (FC_RC one r k 0 (d0^^k *> r) n (FC_zero one r k)). Qed.

Lemma RC_carry one n r : RC one n r -> exists k s,
  r=one^^k *> d0 *> s /\ RC one (S n) (d0^^k *> one *> s).
Proof.
  intro H; induction H.
  - exists 0%nat,(0inf)%sym; split; [unfold d0; st; reflexivity|].
    change (RC one (1+0*2) (one *> (0inf)%sym)); constructor; constructor.
  - exists 0%nat,r; split; [reflexivity|].
    change (RC one (1+n*2) (one *> r)); now constructor.
  - destruct IHRC as [k [s [Er Hr]]]; exists (S k),s.
    split; cbn [lpow]; rewrite Str_app_assoc.
    + now rewrite Er.
    + replace (S (1+n*2)) with (S n*2) by lia; now constructor.
Qed.

Lemma RC_positive_split one n r : RC one n r -> 0<n -> exists t q s,
  r=d0^^t *> one *> s /\ RC one q s /\ n=2^t*(1+q*2) /\ q<n.
Proof.
  intro H; induction H; intro Hn; [lia| |].
  - assert (Hpos:0<n) by lia.
    destruct (IHRC Hpos) as [t [q [s [Er [Hs [En Hq]]]]]].
    exists (S t),q,s; split.
    + cbn [lpow]; rewrite Str_app_assoc; now rewrite Er.
    + split; [exact Hs|]; split; [cbn [Nat.pow]; nia|lia].
  - exists 0%nat,n,r; split; [reflexivity|].
    split; [exact H|]; split; [cbn; lia|lia].
Qed.

Lemma FC_carry one tail k n r : FC one tail k n r -> S n<2^k -> exists j s,
  j<k /\ r=one^^j *> d0 *> s /\ FC one tail k (S n) (d0^^j *> one *> s).
Proof.
  intro H; induction H; intro Hb.
  - cbn in Hb; lia.
  - exists 0%nat,r; split; [lia|]; split; [reflexivity|].
    change (FC one tail (S k) (1+n*2) (one *> r)); now constructor.
  - assert (Hn:S n<2^k) by (cbn [Nat.pow] in Hb; lia).
    destruct (IHFC Hn) as [j [s [Hj [Er Hr]]]]; exists (S j),s.
    split; [lia|]; split; cbn [lpow]; rewrite Str_app_assoc.
    + now rewrite Er.
    + replace (S (1+n*2)) with (S n*2) by lia; now constructor.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis RZero : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^n *> [0] *> r) -[tm]->+
  C QR v (insert e (d0^^n *> [1] *> r)).

Lemma right_step w v e n r : inc w=(v,e) -> RC d1 n r ->
  exists s, RC d1 (S n) s /\ C QR w r -[tm]->+ C QR v (insert e s).
Proof.
  intros E Hr; destruct (RC_carry _ _ _ Hr) as [k [s [-> Hs]]].
  exists (d0^^k *> d1 *> s); split; [exact Hs|].
  pose proof (RZero w ([0;0;0] *> s) k) as H; rewrite E in H.
  applys_eq H; unfold d0,d1; st; reflexivity.
Qed.

Lemma finite_step w v n r tail k : inc w=(v,false) ->
  FC d1 tail k n r -> S n<2^k -> exists s,
  FC d1 tail k (S n) s /\ C QR w r -[tm]->+ C QR v s.
Proof.
  intros E Hr Hb; destruct (FC_carry _ _ _ _ _ Hr Hb) as [j [s [_ [-> Hs]]]].
  exists (d0^^j *> d1 *> s); split; [exact Hs|].
  pose proof (RZero w ([0;0;0] *> s) j) as H; rewrite E in H.
  applys_eq H; unfold insert,d0,d1; st; reflexivity.
Qed.

Lemma right_steps q w v n r : inc_steps q w v -> RC d1 n r ->
  exists s, RC d1 (n+q) s /\ C QR w r -[tm]->* C QR v s.
Proof.
  intro H; revert n r; induction H; intros n r Hr.
  - exists r; split; [now rewrite Nat.add_0_r|apply evstep_refl].
  - destruct (right_step _ _ _ _ _ H Hr) as [s [Hs HS]].
    destruct (IHinc_steps _ _ Hs) as [s' [Hs' HT]].
    exists s'; split; [applys_eq Hs'; flia|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.

Lemma finite_steps q w v n r tail k : inc_steps q w v ->
  FC d1 tail k n r -> n+q<2^k -> exists s,
  FC d1 tail k (n+q) s /\ C QR w r -[tm]->* C QR v s.
Proof.
  intro H; revert n r; induction H; intros n r Hr Hb.
  - exists r; split; [now rewrite Nat.add_0_r|apply evstep_refl].
  - destruct (finite_step _ _ _ _ _ _ H Hr ltac:(lia)) as [s [Hs HS]].
    destruct (IHinc_steps _ _ Hs ltac:(lia)) as [s' [Hs' HT]].
    exists s'; split; [applys_eq Hs'; flia|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.
End Semantics.
End Pair12Right.

(* Shared: SOCPair12ShiftGuard.v/PairShiftGuard. *)
Module PairShiftGuard.
Import PairGuard PairCarry PairPrefix.
Open Scope nat_scope.

Lemma inc_steps_gaps q w v : inc_steps q w v -> q<gap0 w ->
  gap0 v+q=gap0 w /\ gap1 w<=2^q*gap1 v /\ gap2 w<=2^q*gap2 v.
Proof.
  intro HS; induction HS; intro HC.
  - cbn [Nat.pow]; lia.
  - pose proof (inc_interior w u false H ltac:(lia)) as [_ [_ HG]].
    pose proof (inc_half w u false H) as [H1 H2].
    pose proof (IHHS ltac:(lia)) as [G0 [G1 G2]].
    cbn [Nat.pow]; nia.
Qed.

Lemma small_carry_guard H e c u v :
  1<=H -> e<=1 -> c<=2^e -> inc_steps c u v ->
  (2*H+1)*2^e<=gap0 u -> (2*H+1)*2^e<=gap1 u ->
  (2*H+1)*2^e<=gap2 u ->
  H+1<=gap0 v /\ H+1<=gap1 v /\ H+1<=gap2 v.
Proof.
  intros HH HE HC HS H0 H1 H2.
  assert (2^e<>0) by (apply Nat.pow_nonzero; lia).
  pose proof (inc_steps_gaps c u v HS ltac:(nia)) as [G0 [G1 G2]].
  destruct e as [|[|e]]; try lia;
    cbn [Nat.pow] in HC,H0,H1,H2;
    destruct c as [|[|[|c]]]; cbn [Nat.pow] in G1,G2; lia.
Qed.

Lemma gap0_short t w : length w<=3*t -> gap0 w<=4^t.
Proof.
  revert w; induction t as [|t IH]; intros w HL.
  - destruct w; cbn [length] in HL; [|lia].
    change (1<=1); lia.
  - assert (0<4^t) by (pose proof (Nat.pow_nonzero 4 t ltac:(lia)); lia).
    destruct w as [|a [|b [|marker w]]]; cbn [length] in HL.
    + change (1<=4^(S t)); cbn [Nat.pow]; nia.
    + unfold gap0; cbn [digit_plane Nat.pow].
      destruct a; cbn [zero_bit]; nia.
    + unfold gap0; cbn [digit_plane Nat.pow].
      destruct a,b; cbn [zero_bit]; nia.
    + pose proof (IH w ltac:(lia)).
      pose proof (gap_triple_upper a b marker w) as [HU _].
      cbn [Nat.pow]; nia.
Qed.

Lemma pow_two_four t : 2^(2*t)=4^t.
Proof.
  induction t as [|t IH]; [reflexivity|].
  replace (2*S t) with (2+2*t) by lia.
  rewrite Nat.pow_add_r,IH; cbn [Nat.pow]; lia.
Qed.

Lemma preserve_bits a b H w v :
  1<=a -> 1<=H -> (a=1 -> b=true) -> (a=2 -> b=false) ->
  (2*H+1)*2^a<=gap0 w -> (2*H+1)*2^a<=gap1 w ->
  (2*H+1)*2^a<=gap2 w ->
  inc_steps (2^a-bit_value b) w v ->
  2*H<=gap0 (repeat false (2*a-1)++b::v) /\
  2*H<=gap1 (repeat false (2*a-1)++b::v) /\
  2*H<=gap2 (repeat false (2*a-1)++b::v).
Proof.
  intros HA HH HB1 HB2 H0 H1 H2 HS.
  destruct (Nat.eq_dec a 1) as [EA|EA].
  - subst a; specialize (HB1 eq_refl); subst b.
    cbn [Nat.pow bit_value Nat.sub] in HS.
    inversion HS as [|q w0 mid v0 E HT]; subst.
    inversion HT; subst.
    cbn [repeat app Nat.mul Nat.sub].
    eapply short_01_guard; [exact E| | |];
      cbn [Nat.pow] in H0,H1,H2; nia.
  - assert (HA2:2<=a) by lia.
    set (t:=a/2).
    set (e:=a mod 2).
    assert (HE:e<=1) by (unfold e; pose proof (Nat.mod_upper_bound a 2 ltac:(lia)); lia).
    assert (HAT:a=2*t+e) by (unfold t,e; pose proof (Nat.div_mod a 2 ltac:(lia)); nia).
    assert (HT:1<=t) by lia.
    assert (HP:2^a=2^e*4^t).
    { rewrite HAT,Nat.pow_add_r,pow_two_four; nia. }
    assert (HF:0<4^t) by (pose proof (Nat.pow_nonzero 4 t ltac:(lia)); lia).
    assert (HEP:0<2^e) by (pose proof (Nat.pow_nonzero 2 e ltac:(lia)); lia).
    assert (HL:3*t<=length w).
    { destruct (Nat.le_gt_cases (3*t) (length w)); [assumption|].
      pose proof (gap0_short t w ltac:(lia)); rewrite HP in H0; nia. }
    set (rho:=firstn (3*t) w).
    set (u:=skipn (3*t) w).
    assert (HW:w=rho++u) by (unfold rho,u; symmetry; apply firstn_skipn).
    assert (HLR:length rho=3*t) by (unfold rho; rewrite length_firstn; lia).
    rewrite HW in H0,H1,H2,HS.
    destruct (prefix_triples_upper t rho u HLR) as [HU0 [HU1 HU2]].
    assert (HG0:(2*H+1)*2^e<=gap0 u) by (rewrite HP in H0; nia).
    assert (HG1:(2*H+1)*2^e<=gap1 u) by (rewrite HP in H1; nia).
    assert (HG2:(2*H+1)*2^e<=gap2 u) by (rewrite HP in H2; nia).
    assert (HQ:2^a-bit_value b<=2^e*4^t) by (rewrite HP; lia).
    destruct (inc_steps_split_bounded t (2^a-bit_value b) (2^e) rho u v HLR HS HQ)
      as [rho' [u' [c [HV [HLR' [HC [HCB HVAL]]]]]]].
    destruct (small_carry_guard H e c u u' HH HE HCB HC HG0 HG1 HG2)
      as [HG0' [HG1' HG2']].
    destruct (Nat.le_gt_cases 4 H) as [HH4|HH4].
    + subst v.
      replace (repeat false (2*a-1)++b::rho'++u') with
        ((repeat false (2*a-1)++b::rho')++u') by (rewrite <- app_assoc; reflexivity).
      apply long_prefix; try assumption.
      rewrite length_app,repeat_length; cbn [length]; lia.
    + assert (HH3:H<=3) by lia.
      destruct (Nat.eq_dec a 2) as [EA2|EA2].
      * specialize (HB2 EA2); subst b; rewrite EA2.
        cbn [repeat Nat.mul Nat.sub Nat.add app].
        pose proof (zero4_eight v); lia.
      * assert (HP4:4<=2*a-1) by lia.
        replace (2*a-1) with (4+(2*a-1-4)) by lia.
        rewrite repeat_app; cbn [repeat app].
        pose proof (zero4_eight (repeat false (2*a-1-4)++b::v)); lia.
Qed.

Lemma preserve a b H w v :
  1<=a -> 1<=H -> b=negb (Nat.eqb (a mod 3) 2) ->
  (2*H+1)*2^a<=gap0 w -> (2*H+1)*2^a<=gap1 w ->
  (2*H+1)*2^a<=gap2 w ->
  inc_steps (2^a-bit_value b) w v ->
  2*H<=gap0 (repeat false (2*a-1)++b::v) /\
  2*H<=gap1 (repeat false (2*a-1)++b::v) /\
  2*H<=gap2 (repeat false (2*a-1)++b::v).
Proof.
  intros HA HH HB; apply preserve_bits; try assumption;
    intro E; subst a; exact HB.
Qed.

End PairShiftGuard.

(* Shared: SOCPair12Shift.v/PairShift. *)
Module PairShift.
Import PairWord PairGuard PairCarry Pair12Right.
Local Open Scope sym_scope.

Definition last_bit n := negb (Nat.eqb ((1+n) mod 3) 2).
Definition output n b v := push0 (2*n+1) (b::v).

Lemma push0_cons n v : push0 n (false::v)=push0 (S n) v.
Proof.
  unfold push0; induction n; cbn [repeat app]; [reflexivity|].
  now rewrite IHn.
Qed.

Lemma C_push QR m w r : C QR (push0 m w) r =
  data w <* <[1;0]^^(1+m) {{QR}}> r.
Proof. unfold C; rewrite data_push0; cbn [lpow]; st; reflexivity. Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis RZero : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^n *> [0] *> r) -[tm]->+
  C QR v (insert e (d0^^n *> [1] *> r)).
Hypothesis R1001_0 : forall l r n,
  l <* <[1;0] {{QR}}> d1^^(n*3) *> [1;0;0;1] *> r -[tm]->+
  l <* <[1;1] <* <[1;0]^^(n*6+2) {{QR}}> r.
Hypothesis R1001_2 : forall l r n,
  l <* <[1;0] {{QR}}> d1^^(n*3+2) *> [1;0;0;1] *> r -[tm]->+
  l <* <[1;1] <* <[1;0]^^(n*6+6) {{QR}}> r.
Hypothesis R1001_call : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^(n*3+1) *> [1;0;0;1] *> r) -[tm]->+
  C QR (push0 (n*6+4) v) (insert e r).

Lemma shifted_prefix n w v r : inc_steps (2^(1+n)-1) w v ->
  C QR w (d0^^n *> ds *> r) -[tm]->+
  C QR v (d1^^n *> [1;0;0;1] *> r).
Proof.
  intro H; pose proof (Nat.pow_nonzero 2 n) as HP.
  replace (2^(1+n)-1) with ((2^n-1)+S (2^n-1)) in H
    by (cbn [Nat.pow Nat.add]; lia).
  destruct (inc_steps_add_inv _ _ _ _ H) as [u [Hwu Huv]].
  inversion Huv as [|q u0 u1 v0 EI Hu1v]; subst.
  destruct (finite_steps tm QR RZero _ _ _ _ _ _ _ Hwu
    (FC_zero d1 (ds *> r) n) ltac:(lia)) as [s [Hs HS]].
  assert (Es:s=d1^^n *> ds *> r).
  { eapply FC_full_unique; exact Hs. }
  subst s.
  destruct (finite_steps tm QR RZero _ _ _ _ _ _ _ Hu1v
    (FC_zero d1 ([1;0;0;1] *> r) n) ltac:(lia)) as [s [Hs2 HT]].
  assert (Es:s=d1^^n *> [1;0;0;1] *> r).
  { eapply FC_full_unique; exact Hs2. }
  subst s.
  pose proof (RZero u ([0;0;1] *> r) n) as HM; rewrite EI in HM.
  eapply evstep_progress_trans; [exact HS|].
  eapply progress_evstep_trans; [|exact HT].
  applys_eq HM; unfold ds,insert; st; reflexivity.
Qed.

Lemma finish_signal n w v r :
  (if last_bit n then w=v else inc w=(v,false)) ->
  C QR w (d1^^n *> [1;0;0;1] *> r) -[tm]->+
  C QR (output n (last_bit n) v) r.
Proof.
  pose proof (Nat.div_mod n 3 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as Hb.
  destruct (n mod 3) as [|[|[|k]]] eqn:E; try lia.
  - assert (EB:last_bit n=true).
    { unfold last_bit; rewrite Nat.Div0.add_mod,E; reflexivity. }
    rewrite EB; intros ->; unfold output; rewrite C_push.
    applys_eq (R1001_0 (data v) r (n/3)); unfold C,data,pairs,bit; flia.
  - assert (EB:last_bit n=false).
    { unfold last_bit; rewrite Nat.Div0.add_mod,E; reflexivity. }
    rewrite EB; intro EI.
    pose proof (R1001_call w r (n/3)) as HS; rewrite EI in HS.
    unfold output; rewrite push0_cons.
    applys_eq HS; unfold insert; flia.
  - assert (EB:last_bit n=true).
    { unfold last_bit; rewrite Nat.Div0.add_mod,E; reflexivity. }
    rewrite EB; intros ->; unfold output; rewrite C_push.
    applys_eq (R1001_2 (data v) r (n/3)); unfold C,data,pairs,bit; flia.
Qed.

Lemma shifted n w v r : inc_steps (2^(1+n)-bit_value (last_bit n)) w v ->
  C QR w (d0^^n *> ds *> r) -[tm]->+
  C QR (output n (last_bit n) v) r.
Proof.
  intro H; destruct (last_bit n) eqn:E.
  - cbn [bit_value] in H.
    eapply progress_trans; [apply shifted_prefix; exact H|].
    rewrite <-E; apply finish_signal; now rewrite E.
  - cbn [bit_value] in H; rewrite Nat.sub_0_r in H.
    replace (2^(1+n)) with ((2^(1+n)-1)+1) in H
      by (pose proof (Nat.pow_nonzero 2 (1+n)); lia).
    destruct (inc_steps_add_inv _ _ _ _ H) as [u [Hwu Huv]].
    inversion Huv as [|q u0 v0 v1 EI Hlast]; subst.
    inversion Hlast; subst.
    eapply progress_trans; [apply shifted_prefix; exact Hwu|].
    rewrite <-E; apply finish_signal; now rewrite E.
Qed.
End Semantics.
End PairShift.

(* Shared: SOCPair12Region.v/PairRegion. *)
Module PairRegion.
Import PairWord PairGuard Pair12Right PairShift.
Local Open Scope sym_scope.

Definition guard n w := 2*n<=gap0 w /\ 2*n<=gap1 w /\ 2*n<=gap2 w.
Inductive Allowed (QR:Q) : (Q*(side*sym*side))%type -> Prop :=
| Blank w : Allowed QR (C QR w (0inf)%sym)
| One w : w<>[] -> Nat.Even (value w) ->
    Allowed QR (C QR w ([1] *> (0inf)%sym))
| Shifted w n r : 0<n -> RC ds n r -> guard n w -> Allowed QR (C QR w r).

Lemma zero_prefix_even n w : 1<=n -> Nat.Even (value (push0 n w)).
Proof.
  destruct n; [lia|]; intro H.
  unfold push0,value; cbn [repeat app digit_plane bit_value].
  exists (2*digit_plane bit_value 2 (repeat false n++w)+
    digit_plane bit_value 0 (repeat false n++w)); lia.
Qed.

Lemma last_bit_false n : last_bit n=false -> n mod 3=1%nat.
Proof.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as Hb.
  unfold last_bit; rewrite Nat.Div0.add_mod.
  destruct (n mod 3) as [|[|[|k]]]; cbn; intros; try discriminate; lia.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis Prefix : forall n w v r, inc_steps (2^(1+n)-1) w v ->
  C QR w (d0^^n *> ds *> r) -[tm]->+ C QR v (d1^^n *> [1;0;0;1] *> r).
Hypothesis Finish : forall n w v r,
  (if last_bit n then w=v else inc w=(v,false)) ->
  C QR w (d1^^n *> [1;0;0;1] *> r) -[tm]->+
  C QR (output n (last_bit n) v) r.
Hypothesis Shift : forall n w v r,
  inc_steps (2^(1+n)-bit_value (last_bit n)) w v ->
  C QR w (d0^^n *> ds *> r) -[tm]->+ C QR (output n (last_bit n) v) r.
Hypothesis Call : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^(n*3+1) *> [1;0;0;1] *> r) -[tm]->+
  C QR (push0 (n*6+4) v) (insert e r).

Lemma last_signal n w : exists c', Allowed QR c' /\
  C QR w (d1^^n *> [1;0;0;1] *> (0inf)%sym) -[tm]->+ c'.
Proof.
  destruct (last_bit n) eqn:E.
  - exists (C QR (output n (last_bit n) w) (0inf)%sym); split; [constructor|].
    apply Finish; now rewrite E.
  - pose proof (last_bit_false n E) as En.
    pose proof (Nat.div_mod n 3 ltac:(lia)) as Hn; rewrite En in Hn.
    pose proof (Call w (0inf)%sym (n/3)) as HS.
    destruct (inc w) as [v e] eqn:EI; destruct e.
    + exists (C QR (push0 (n/3*6+4) v) ([1] *> (0inf)%sym)); split.
      * apply One; [|apply zero_prefix_even; lia].
        intro H; apply (f_equal (@length bool)) in H.
        unfold push0 in H; rewrite length_app, repeat_length in H; cbn in H; lia.
      * applys_eq HS; unfold insert; flia.
    + exists (C QR (push0 (n/3*6+4) v) (0inf)%sym); split; [constructor|].
      applys_eq HS; unfold insert; flia.
Qed.

Lemma last_shift n w : 2^(1+n)<=gap0 w -> exists c', Allowed QR c' /\
  C QR w (d0^^n *> ds *> (0inf)%sym) -[tm]->+ c'.
Proof.
  intro Hg; pose proof (Nat.pow_nonzero 2 (1+n)) as HP.
  destruct (inc_steps_interior (2^(1+n)-1) w ltac:(lia)) as [v [HV _]].
  destruct (last_signal n v) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  eapply progress_trans; [apply Prefix; exact HV|exact HS].
Qed.

Lemma shifted_step n w r : 0<n -> RC ds n r -> guard n w ->
  exists c', Allowed QR c' /\ C QR w r -[tm]->+ c'.
Proof.
  intros Hn Hr [H0 [H1 H2]].
  destruct (RC_positive_split _ _ _ Hr Hn)
    as [t [q [s [Er [Hs [En Hqn]]]]]].
  destruct q as [|q].
  - apply RC_zero_unique in Hs; subst s; rewrite Er.
    apply last_shift; rewrite En in H0; cbn [Nat.pow Nat.add] in *; nia.
  - set (b:=last_bit t).
    assert (HB:bit_value b<=1) by (unfold bit_value; destruct b; lia).
    assert (HP:2^(1+t)<>0%nat) by (apply Nat.pow_nonzero; lia).
    assert (HQ:2^(1+t)-bit_value b<gap0 w).
    { rewrite En in H0; cbn [Nat.pow Nat.add] in *; nia. }
    destruct (inc_steps_interior _ _ HQ) as [v [HV _]].
    assert (HG:guard (S q) (output t b v)).
    { unfold guard,output,push0.
      replace (2*t+1) with (2*(1+t)-1) by lia.
      apply (PairShiftGuard.preserve (1+t) b (S q) w v);
        try (unfold b,last_bit; reflexivity); try eassumption;
        rewrite ?En in *; cbn [Nat.pow Nat.add] in *; nia. }
    exists (C QR (output t b v) s); split.
    + eapply Shifted with (n:=S q); [lia|exact Hs|exact HG].
    + rewrite Er; apply Shift; exact HV.
Qed.
End Semantics.
End PairRegion.

(* Shared: SOCPair12EntryGuard.v/PairEntryGuard. *)
Module PairEntryGuard.
Import PairGuard PairPrefix PairOverflow.
Open Scope nat_scope.

Lemma pow24 k : 2^(2*k)=4^k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (2*S k) with (2+2*k) by lia.
  rewrite Nat.pow_add_r,IH; cbn [Nat.pow]; lia.
Qed.

Lemma ones_triples t w :
  gap0 (repeat true (3*t)++w)+4^t=4^t*gap0 w+1 /\
  gap1 (repeat true (3*t)++w)+2*4^t=4^t*gap1 w+2 /\
  gap2 (repeat true (3*t)++w)+4*4^t=4^t*gap2 w+4.
Proof.
  induction t as [|t IH].
  - cbn [repeat app Nat.pow Nat.mul Nat.add]; lia.
  - replace (3*S t) with (3+3*t) by lia.
    rewrite repeat_app; cbn [repeat app].
    pose proof (gap_triple true true true (repeat true (3*t)++w)) as HG.
    cbn [zero_bit Nat.pow] in *; nia.
Qed.

Lemma zero_word w : value w=0 -> digit_plane bit_value 2 w=0 ->
  w=repeat false (length w).
Proof.
  revert w; fix IH 1; intros w HV HM.
  destruct w as [|a [|b [|c w]]].
  - reflexivity.
  - destruct a; [unfold value in HV; cbn [digit_plane bit_value] in HV; lia|reflexivity].
  - destruct a,b; unfold value in HV; cbn [digit_plane bit_value] in HV;
      try lia; reflexivity.
  - unfold value in HV; cbn [digit_plane] in HV,HM.
    destruct a,b,c; cbn [bit_value] in HV,HM; try lia.
    assert (HT:value w=0) by (unfold value; lia).
    pose proof (IH w HT ltac:(lia)) as HE.
    cbn [length repeat]; now rewrite HE at 1.
Qed.

Lemma zero_entry k p : (p=1 \/ p=2) ->
  4*4^k<=gap0 (false::repeat false (3*k+p)) /\
  4*4^k<=gap1 (false::repeat false (3*k+p)) /\
  4*4^k<=gap2 (false::repeat false (3*k+p)).
Proof.
  intro HP; induction k as [|k IH].
  - destruct HP as [-> | ->]; unfold gap0,gap1,gap2;
      cbn [repeat digit_plane zero_bit Nat.pow Nat.mul Nat.add]; lia.
  - replace (3*S k+p) with (3+(3*k+p)) by lia.
    rewrite repeat_app; cbn [repeat app].
    pose proof (gap_triple false false false
      (false::repeat false (3*k+p))) as HG.
    cbn [zero_bit Nat.pow] in *; nia.
Qed.

Lemma prefix_residue t r E : r<=2 ->
  let W:=repeat true (3*t+r)++false::E in
  match r with
  | 0 => gap0 W+4^t=4^t*gap1 E+1 /\
         gap1 W+2*4^t=4^t*gap2 E+2 /\
         gap2 W+4*4^t=4*4^t*gap0 E+4
  | 1 => gap0 W+2*4^t=4^t*gap2 E+1 /\
         gap1 W+4*4^t=4*4^t*gap0 E+2 /\
         gap2 W+4*4^t=4*4^t*gap1 E+4
  | _ => gap0 W+4*4^t=4*4^t*gap0 E+1 /\
         gap1 W+4*4^t=4*4^t*gap1 E+2 /\
         gap2 W+8*4^t=4*4^t*gap2 E+4
  end.
Proof.
  intro HR; cbn zeta; rewrite repeat_app,<-app_assoc.
  pose proof (ones_triples t (repeat true r++false::E)) as HT.
  destruct r as [|[|[|r]]]; try lia;
    cbn [repeat app] in *;
    pose proof (gap_cons false E) as H0;
    pose proof (gap_cons true (false::E)) as H1;
    pose proof (gap_cons true (true::false::E)) as H2;
    cbn [zero_bit] in *; nia.
Qed.

Lemma strong k p z E :
  (p=1 \/ p=2) -> length E=3*k+p ->
  digit_plane bit_value 2 E=0 -> value E=2^(z+1)-2 -> z<2*k+p ->
  2^(2*k+2-z)<=gap0 (repeat true (2*z)++false::E) /\
  2^(2*k+2-z)<=gap1 (repeat true (2*z)++false::E) /\
  2^(2*k+2-z)<=gap2 (repeat true (2*z)++false::E).
Proof.
  intros HP HL HM HV HZ.
  assert (HPB:1<=p /\ p<=2) by lia.
  destruct (Nat.eq_dec z 0) as [EZ|EZ].
  - subst z.
    assert (EV:value E=0) by (rewrite HV; reflexivity).
    rewrite (zero_word E EV HM),HL.
    rewrite Nat.sub_0_r.
    change (2^(2*k+2)<=gap0 (false::repeat false (3*k+p)) /\
      2^(2*k+2)<=gap1 (false::repeat false (3*k+p)) /\
      2^(2*k+2)<=gap2 (false::repeat false (3*k+p))).
    rewrite Nat.pow_add_r,pow24; cbn [Nat.pow].
    pose proof (zero_entry k p HP); nia.
  - assert (HZP:1<=z) by lia.
    assert (Cpos:0<4^k) by (pose proof (Nat.pow_nonzero 4 k ltac:(lia)); lia).
    assert (PZ:2<=2^(z+1)).
    { replace 2 with (2^1) by reflexivity.
      apply Nat.pow_le_mono_r; lia. }
    assert (PC:2^(2*k+p)=2^p*4^k).
    { rewrite Nat.pow_add_r,pow24; nia. }
    pose proof (value_gap0 E) as HG.
    rewrite (width_length k p E ltac:(lia) HL),HV in HG.
    assert (HGexact:gap0 E+2^(z+1)=2^p*4^k+2) by (rewrite PC in HG; lia).
    pose proof (zero_marker_bounds k E ltac:(lia) HM) as [HG1 HG2].
    assert (HB:2^(2*k+2-z)<=2*4^k).
    { replace (2*4^k) with (2^(2*k+1)).
      - apply Nat.pow_le_mono_r; lia.
      - rewrite Nat.pow_add_r,pow24; cbn [Nat.pow]; nia. }
    assert (HG0:4^k+2<=gap0 E \/
      (2<=gap0 E /\ 2^(2*k+2-z)<=4)).
    { destruct (Nat.eq_dec (z+1) (2*k+p)) as [HE|HE].
      - right; split.
        + rewrite HE,PC in HGexact; lia.
        + replace (2*k+2-z) with (3-p) by lia.
          destruct HP as [-> | ->]; cbn [Nat.sub Nat.pow]; lia.
      - left.
        assert (Hpower:2*2^(z+1)<=2^(2*k+p)).
        { replace (2*2^(z+1)) with (2^(S (z+1))) by reflexivity.
          apply Nat.pow_le_mono_r; lia. }
        rewrite PC in Hpower.
        destruct HP as [-> | ->]; cbn [Nat.pow] in HGexact,Hpower; nia. }
    set (t:=(2*z)/3).
    set (r:=(2*z) mod 3).
    assert (HR:r<=2) by (unfold r; pose proof (Nat.mod_upper_bound (2*z) 3 ltac:(lia)); lia).
    assert (HZR:2*z=3*t+r) by
      (unfold t,r; pose proof (Nat.div_mod (2*z) 3 ltac:(lia)); nia).
    assert (Kpos:1<=4^t) by (pose proof (Nat.pow_nonzero 4 t ltac:(lia)); lia).
    assert (Kbig:r<=1 -> 4<=4^t).
    { intro H; assert (1<=t) by lia.
      replace 4 with (4^1) by reflexivity.
      apply Nat.pow_le_mono_r; lia. }
    pose proof (prefix_residue t r E HR) as HF.
    rewrite <-HZR in HF.
    clear - HF HG0 HG1 HG2 HB Kpos Kbig Cpos HR.
    destruct r as [|[|[|r]]]; try lia;
      cbn zeta in HF; destruct HG0 as [HG0|[HG0 HB4]];
      try specialize (Kbig ltac:(lia)); nia.
Qed.

Lemma actual k p z E H :
  (p=1 \/ p=2) -> length E=3*k+p ->
  digit_plane bit_value 2 E=0 -> value E=2^(z+1)-2 -> z<2*k+p ->
  2^z*(1+2*H)<=(if Nat.eqb p 1 then 3 else 4)*4^k ->
  2*H<gap0 (repeat true (2*z)++false::E) /\
  2*H<gap1 (repeat true (2*z)++false::E) /\
  2*H<gap2 (repeat true (2*z)++false::E).
Proof.
  intros HP HL HM HV HZ HT.
  pose proof (strong k p z E HP HL HM HV HZ) as [HG0 [HG1 HG2]].
  assert (HZB:z<=2*k+2) by lia.
  assert (HB:2^(2*k+2-z)*2^z=4*4^k).
  { rewrite <-Nat.pow_add_r.
    replace (2*k+2-z+z) with (2*k+2) by lia.
    rewrite Nat.pow_add_r,pow24; cbn [Nat.pow]; nia. }
  assert (PZ:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).
  destruct HP as [-> | ->]; cbn [Nat.eqb] in HT; nia.
Qed.

End PairEntryGuard.

(* Shared: SOCPair12Entry.v/Pair12Entry. *)
Module Pair12Entry.
Import PairWord PairGuard PairOverflow Pair12Right.
Local Open Scope sym_scope.

Lemma phase1_zero_gap k : gap0 (repeat false (3*k+1))=2*4^k.
Proof.
  rewrite gap0_zeros by lia.
  rewrite Nat.pow_add_r, Nat.pow_mul_r; change (4^k*2=2*4^k); lia.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis RZero : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^n *> [0] *> r) -[tm]->+
  C QR v (insert e (d0^^n *> [1] *> r)).

Let Step := Pair12Right.right_step tm QR RZero.
Let Steps := Pair12Right.right_steps tm QR RZero.

(* A one/two-bit high fragment inserts immediately at the capacity event. *)
Lemma phase12 k p w x r : 1<=p -> p<=2 -> length w=3*k+p -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w) s /\
  C QR w r -[tm]->+ C QR (repeat false (3*k+p)) ([1] *> s).
Proof.
  intros Hp HP Hl Hr.
  destruct (first_capacity k p w HP Hl) as [u [HS [Hlen [Hgap HE]]]].
  destruct (Steps _ _ _ _ _ HS Hr) as [s1 [Hr1 HR1]].
  destruct p; [lia|].
  destruct (Step _ _ _ _ _ HE Hr1) as [s2 [Hr2 HR2]].
  exists s2; split.
  - pose proof (gap_bounds w); applys_eq Hr2; flia.
  - eapply evstep_progress_trans; [exact HR1|exact HR2].
Qed.

(* Phase zero first extends the all-zero word and does not insert. *)
Lemma phase0_extend k w x r : length w=3*k -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w) s /\
  C QR w r -[tm]->+ C QR (repeat false (3*k+1)) s.
Proof.
  intros Hl Hr.
  destruct (first_capacity k 0 w ltac:(lia) ltac:(lia))
    as [u [HS [Hlen [Hgap HE]]]].
  destruct (Steps _ _ _ _ _ HS Hr) as [s1 [Hr1 HR1]].
  destruct (Step _ _ _ _ _ HE Hr1) as [s2 [Hr2 HR2]].
  exists s2; split.
  - pose proof (gap_bounds w); applys_eq Hr2; flia.
  - eapply evstep_progress_trans; [exact HR1|exact HR2].
Qed.

(* The new phase-one word makes one complete additional round. *)
Lemma phase0 k w x r : length w=3*k -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w+2*4^k) s /\
  C QR w r -[tm]->+ C QR (repeat false (3*k+1)) ([1] *> s).
Proof.
  intros Hl Hr; destruct (phase0_extend k w x r Hl Hr) as [s1 [Hr1 HS1]].
  destruct (phase12 k 1 (repeat false (3*k+1)) _ s1
    ltac:(lia) ltac:(lia) (repeat_length _ _) Hr1) as [s2 [Hr2 HS2]].
  rewrite phase1_zero_gap in Hr2.
  exists s2; split; [exact Hr2|].
  eapply progress_trans; [exact HS1|exact HS2].
Qed.
End Semantics.
End Pair12Entry.

(* Shared: SOCPair12Ordinary.v/PairOrdinary. *)
Module PairOrdinary.
Import PairWord PairGuard PairCarry Pair12Right.
Local Open Scope sym_scope.

Lemma FC_leading_one t r :
  FC d1 ([0] *> d1 *> r) (S t) 1 ([1] *> d0^^(S t) *> d1 *> r).
Proof.
  applys_eq (FC_d1 d1 _ _ _ _ (FC_zero d1 ([0] *> d1 *> r) t)).
  unfold d0,d1; st; simpl_rotate; reflexivity.
Qed.

Lemma pairs_ones n w : pairs (repeat true n++w)=[1;1]^^n++pairs w.
Proof.
  induction n; cbn [repeat app pairs bit lpow]; [reflexivity|].
  now rewrite IHn.
Qed.

Lemma data_ones n w : data (repeat true n++w)=data w <* [1;1]^^n.
Proof. unfold data; rewrite pairs_ones; st; reflexivity. Qed.

Lemma RC_shift3 n r : RC d1 n r -> RC ds n ([0;0;0] *> r).
Proof.
  intro H; induction H.
  - applys_eq (RC_zero ds); st; reflexivity.
  - applys_eq (RC_d0 ds _ _ IHRC); unfold d0; st; reflexivity.
  - applys_eq (RC_d1 ds _ _ IHRC); unfold d1,ds; st; reflexivity.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis RZero : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^n *> [0] *> r) -[tm]->+
  C QR v (insert e (d0^^n *> [1] *> r)).

Lemma one_cross z w v r : 1<=z -> inc_steps (2^z-1) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR v (d0^^z *> [1;1;0;0;0] *> r).
Proof.
  intros Hz H; destruct z as [|t]; [lia|].
  assert (HP:2<=2^(S t)) by
    (cbn [Nat.pow]; pose proof (Nat.pow_nonzero 2 t); lia).
  replace (2^(S t)-1) with ((2^(S t)-2)+1) in H by lia.
  destruct (inc_steps_add_inv _ _ _ _ H) as [u [HW HU]].
  inversion HU as [|q u0 mid v0 EI Hlast]; subst.
  inversion Hlast; subst.
  destruct (finite_steps tm QR RZero _ _ _ _ _ _ _ HW
    (FC_leading_one t r) ltac:(lia)) as [s [Hs HS]].
  assert (Es:s=d1^^(S t) *> [0] *> d1 *> r).
  { eapply FC_full_unique; applys_eq Hs; flia. }
  subst s.
  pose proof (RZero u (d1 *> r) (S t)) as HC; rewrite EI in HC.
  eapply evstep_progress_trans; [exact HS|].
  applys_eq HC; unfold insert,d1; st; reflexivity.
Qed.

Lemma prefix z w v r : inc_steps (2^(z+1)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->*
  C QR v (d1^^z *> [1;1;0;0;0] *> r).
Proof.
  intro H; destruct z as [|t].
  - cbn [Nat.pow] in H; inversion H; subst.
    unfold d1; apply evstep_refl.
  - pose proof (Nat.pow_nonzero 2 (S t)) as HP.
    replace (2^(S t+1)-2) with ((2^(S t)-1)+(2^(S t)-1)) in H
      by (rewrite Nat.pow_add_r; cbn [Nat.pow]; lia).
    destruct (inc_steps_add_inv _ _ _ _ H) as [u [HW HV]].
    destruct (finite_steps tm QR RZero _ _ _ _ _ _ _ HV
      (FC_zero d1 ([1;1;0;0;0] *> r) (S t)) ltac:(lia)) as [s [Hs HS]].
    assert (Es:s=d1^^(S t) *> [1;1;0;0;0] *> r).
    { apply FC_full_unique; exact Hs. }
    subst s; follow100 (one_cross (S t) w u r ltac:(lia) HW); exact HS.
Qed.

Hypothesis REleven : forall l r n,
  l <* <[1;0] {{QR}}> d1^^n *> [1;1] *> r -[tm]->+
  l <* <[1;0] <* [1;1]^^(n*2) <* <[1;0] {{QR}}> r.

Lemma eleven_word z w r :
  C QR w (d1^^z *> [1;1] *> r) -[tm]->+
  C QR (repeat true (2*z)++false::w) r.
Proof.
  unfold C; rewrite data_ones.
  applys_eq (REleven (data w) r z); unfold data; cbn [pairs bit]; flia.
Qed.

Lemma ordinary z w v r : inc_steps (2^(z+1)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR (repeat true (2*z)++false::v) ([0;0;0] *> r).
Proof.
  intro H; eapply evstep_progress_trans; [apply prefix; exact H|].
  exact (eleven_word z v ([0;0;0] *> r)).
Qed.
End Semantics.
End PairOrdinary.

(* Shared: SOCPair12Exceptional.v/PairExceptional. *)
Module PairExceptional.
Import PairWord PairGuard Pair12Right PairShift PairRegion PairOverflow.
Local Open Scope sym_scope.

Lemma zero3_d0 n r :
  [0;0;0] *> d0^^n *> r=d0^^n *> [0;0;0] *> r.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [lpow]; rewrite !Str_app_assoc.
  change (d0 *> [0;0;0] *> d0^^n *> r=
    d0 *> d0^^n *> [0;0;0] *> r).
  now rewrite IH.
Qed.

Lemma one_allowed QR n w : 1<=n ->
  Allowed QR (C QR (push0 n w) ([1] *> (0inf)%sym)).
Proof.
  intro Hn; apply One; [|apply zero_prefix_even; exact Hn].
  intro E; apply (f_equal (@length bool)) in E.
  unfold push0 in E; rewrite length_app,repeat_length in E; cbn in E; lia.
Qed.

Lemma RC_power a : RC d1 (2^a) (d0^^a *> d1 *> (0inf)%sym).
Proof.
  replace (2^a) with (2^a*1) by lia.
  apply RC_zeros.
  change (RC d1 (1+0*2) (d1 *> (0inf)%sym)); constructor; constructor.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis RZero : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^n *> [0] *> r) -[tm]->+
  C QR v (insert e (d0^^n *> [1] *> r)).
Hypothesis REleven : forall l r n,
  l <* <[1;0] {{QR}}> d1^^n *> [1;1] *> r -[tm]->+
  l <* <[1;0] <* [1;1]^^(n*2) <* <[1;0] {{QR}}> r.
Hypothesis Finish : forall n w v r,
  (if last_bit n then w=v else inc w=(v,false)) ->
  C QR w (d1^^n *> [1;0;0;1] *> r) -[tm]->+
  C QR (output n (last_bit n) v) r.
Hypothesis Call : forall w r n, let '(v,e):=inc w in
  C QR w (d1^^(n*3+1) *> [1;0;0;1] *> r) -[tm]->+
  C QR (push0 (n*6+4) v) (insert e r).
Hypothesis OneCross : forall z w v r, 1<=z ->
  inc_steps (2^z-1) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR v (d0^^z *> [1;1;0;0;0] *> r).

Lemma eleven0 w r :
  C QR w ([1;1] *> r) -[tm]->+ C QR (push0 1 w) r.
Proof.
  rewrite C_push.
  applys_eq (REleven (data w) r 0); unfold C; st; reflexivity.
Qed.

Lemma last_signal_one n w : exists c', Allowed QR c' /\
  C QR w (d1^^n *> [1;0;0;1] *> [1] *> (0inf)%sym) -[tm]->+ c'.
Proof.
  destruct (last_bit n) eqn:E.
  - exists (C QR (output n (last_bit n) w) ([1] *> (0inf)%sym)); split.
    + unfold output; apply one_allowed; lia.
    + apply Finish; now rewrite E.
  - pose proof (last_bit_false n E) as En.
    pose proof (Nat.div_mod n 3 ltac:(lia)) as Hn; rewrite En in Hn.
    pose proof (Call w ([1] *> (0inf)%sym) (n/3)) as HS.
    destruct (inc w) as [v e] eqn:EI; destruct e.
    + exists (C QR (push0 1 (push0 (n/3*6+4) v)) (0inf)%sym); split.
      * constructor.
      * eapply progress_trans; [|apply eleven0].
        applys_eq HS; unfold insert; flia.
    + exists (C QR (push0 (n/3*6+4) v) ([1] *> (0inf)%sym)); split.
      * apply one_allowed; lia.
      * applys_eq HS; unfold insert; flia.
Qed.

Lemma last_shift_one n w : 2^(1+n)<=gap0 w -> exists c', Allowed QR c' /\
  C QR w (d0^^n *> ds *> [1] *> (0inf)%sym) -[tm]->+ c'.
Proof.
  intro Hg; pose proof (Nat.pow_nonzero 2 (1+n)) as HP.
  destruct (inc_steps_interior (2^(1+n)-1) w ltac:(lia)) as [v [HV _]].
  destruct (last_signal_one n v) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  eapply progress_trans; [apply (shifted_prefix tm QR RZero); exact HV|exact HS].
Qed.

Lemma exceptional k p r : (p=1%nat \/ p=2%nat) ->
  RC d1 (2^(2*k+p)) r -> exists c', Allowed QR c' /\
  C QR (repeat false (3*k+p)) ([1] *> r) -[tm]->+ c'.
Proof.
  intros HP Hr.
  assert (Ha:1<=2*k+p) by lia.
  assert (Er:r=d0^^(2*k+p) *> d1 *> (0inf)%sym).
  { eapply RC_unique; [exact Hr|apply RC_power]. }
  rewrite Er.
  assert (HG:gap0 (repeat false (3*k+p))=2^(2*k+p))
    by (apply gap0_zeros; lia).
  assert (HC:2^(2*k+p)<>0%nat) by (apply Nat.pow_nonzero; lia).
  destruct (inc_steps_interior (2^(2*k+p)-1)
    (repeat false (3*k+p)) ltac:(lia)) as [v [HV [HL HGv]]].
  rewrite repeat_length in HL.
  assert (HGV:gap0 v=1%nat) by lia.
  assert (EI:inc v=(repeat false (3*k+p),true)).
  { pose proof (inc_at_capacity k p v ltac:(lia) HL HGV) as HI.
    destruct HP as [-> | ->]; exact HI. }
  assert (Hnew:2^(1+(2*k+p-1))<=
    gap0 (push0 1 (repeat false (3*k+p)))).
  { replace (1+(2*k+p-1)) with (2*k+p) by lia.
    pose proof (PairEntryGuard.zero_entry k p HP) as [H0 _].
    change (2^(2*k+p)<=gap0 (false::repeat false (3*k+p))).
    rewrite Nat.pow_add_r,PairEntryGuard.pow24.
    destruct HP as [-> | ->]; cbn [Nat.pow]; nia. }
  destruct (last_shift_one (2*k+p-1)
    (push0 1 (repeat false (3*k+p))) Hnew) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  eapply progress_trans.
  - exact (OneCross (2*k+p) (repeat false (3*k+p)) v (0inf)%sym Ha HV).
  - eapply progress_trans.
    + pose proof (RZero v
        ([0;0;0] *> d0^^(2*k+p-1) *> [1;1] *> (0inf)%sym) 0) as HZ.
      rewrite EI in HZ.
      applys_eq HZ; unfold C,insert.
      * replace (2*k+p) with (S (2*k+p-1)) by lia.
        cbn [lpow]; unfold d0; st; flia.
    + eapply progress_trans; [apply eleven0|].
      applys_eq HS.
      rewrite zero3_d0; unfold ds; st; reflexivity.
Qed.
End Semantics.
End PairExceptional.

(* Shared: SOCPair12PostEntry.v/PairPostEntry. *)
Module PairPostEntry.
Import PairWord PairGuard Pair12Right PairRegion PairOverflow PairPrefix.
Local Open Scope sym_scope.

Definition limit k p := (if Nat.eqb p 1 then 3 else 4)*4^k.

Lemma capacity_limit k p : (p=1%nat \/ p=2%nat) ->
  limit k p<2*2^(2*k+p).
Proof.
  intros [-> | ->]; unfold limit; rewrite Nat.pow_add_r, PairEntryGuard.pow24;
    cbn [Nat.eqb Nat.pow]; pose proof (Nat.pow_nonzero 4 k); nia.
Qed.

Lemma valuation_bound k p t q : (p=1%nat \/ p=2%nat) ->
  2^t*(1+q*2)<=limit k p -> 2^t*(1+q*2)<>2^(2*k+p) -> t<2*k+p.
Proof.
  intros Hp Hlim Hne; pose proof (capacity_limit k p Hp) as Hcap.
  pose proof (Nat.pow_nonzero 2 t) as HT.
  destruct (Nat.lt_ge_cases t (2*k+p)); [assumption|].
  destruct (Nat.eq_dec t (2*k+p)) as [->|Hneq].
  - assert (q=0%nat) by nia; subst; nia.
  - pose proof (Nat.pow_le_mono_r 2 (2*k+p+1) t ltac:(lia) ltac:(lia)) as Hpow.
    rewrite Nat.pow_add_r in Hpow; cbn [Nat.pow] in Hpow; nia.
Qed.

Lemma zero_gap_order m :
  gap0 (repeat false m)<=gap1 (repeat false m) /\
  gap1 (repeat false m)<=gap2 (repeat false m) /\
  gap2 (repeat false m)<=4*gap0 (repeat false m).
Proof.
  induction m; [change (1<=2 /\ 2<=4 /\ 4<=4*1); lia|].
  pose proof (gap_cons false (repeat false m)) as HC.
  cbn [zero_bit] in HC; cbn [repeat]; lia.
Qed.

Lemma even_gap w : w<>[] -> Nat.Even (value w) -> Nat.Even (gap0 w).
Proof.
  intros Hlen [v Hv]; pose proof (value_gap0 w) as Hg.
  assert (HW:0<width w).
  { destruct w as [|a [|b [|c w]]]; cbn [width]; try lia; contradiction. }
  destruct (width w) as [|k] eqn:Ek; [lia|].
  cbn [Nat.pow] in Hg.
  destruct (Nat.Even_or_Odd (gap0 w)) as [H|[u Hu]]; [exact H|nia].
Qed.

Lemma RC_odd_inv one n r : RC one (1+n*2) r ->
  exists s, RC one n s /\ r=one *> s.
Proof.
  intro H; inversion H; subst; try lia.
  assert (n=n0) by lia; subst n0; eauto.
Qed.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis Ordinary : forall z w v r, inc_steps (2^(1+z)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR (repeat true (2*z)++false::v) ([0;0;0] *> r).
Hypothesis ShiftDigits : forall n r, RC d1 n r -> RC ds n ([0;0;0] *> r).
Hypothesis Exceptional : forall k p r, (p=1%nat \/ p=2%nat) ->
  RC d1 (2^(2*k+p)) r -> exists c', Allowed QR c' /\
  C QR (repeat false (3*k+p)) ([1] *> r) -[tm]->+ c'.
Hypothesis Eleven : forall n w r,
  C QR w (d1^^n *> [1;1] *> r) -[tm]->+
  C QR (repeat true (2*n)++false::w) r.

Lemma post_first k p T r : (p=1%nat \/ p=2%nat) ->
  RC d1 T r -> 0<T -> T<=limit k p -> exists c', Allowed QR c' /\
  C QR (repeat false (3*k+p)) ([1] *> r) -[tm]->+ c'.
Proof.
  intros Hp Hr HT Hlim.
  destruct (Nat.eq_dec T (2^(2*k+p))) as [->|Hne]; [eapply Exceptional; eauto|].
  destruct (RC_positive_split _ _ _ Hr HT)
    as [z [q [s [Er [Hs [Et Hqt]]]]]].
  assert (Hz:z<2*k+p).
  { apply (valuation_bound k p z q Hp); now rewrite <-Et. }
  assert (HG:gap0 (repeat false (3*k+p))=2^(2*k+p)).
  { apply gap0_zeros; lia. }
  assert (HQ:2^(1+z)-2<gap0 (repeat false (3*k+p))).
  { rewrite HG; pose proof (Nat.pow_le_mono_r 2 (1+z) (2*k+p)
      ltac:(lia) ltac:(lia)); pose proof (Nat.pow_nonzero 2 (1+z)); nia. }
  destruct (inc_steps_interior _ _ HQ) as [v [HV [Hl Hgap]]].
  assert (HM:digit_plane bit_value 2 v=0%nat).
  { eapply inc_steps_marker_zero; [exact HV|apply digit_plane_zeros]. }
  assert (Hlen:length v=3*k+p) by (rewrite Hl, repeat_length; reflexivity).
  assert (Hval:value v=2^(z+1)-2).
  { pose proof (value_gap0 v) as HX.
    rewrite (width_length k p v ltac:(lia) Hlen) in HX; rewrite HG in Hgap.
    replace (z+1) with (1+z) by lia; lia. }
  pose proof (PairEntryGuard.actual k p z v q Hp Hlen HM Hval Hz
    ltac:(unfold limit in Hlim; rewrite Et in Hlim; nia)) as [G0 [G1 G2]].
  pose proof (Ordinary z _ _ s HV) as HS; rewrite <-Er in HS.
  pose proof (ShiftDigits _ _ Hs) as HR.
  destruct q as [|q].
  - apply RC_zero_unique in HR; rewrite HR in HS.
    eexists; split; [apply Blank|exact HS].
  - eexists; split; [|exact HS].
    eapply Shifted with (n:=S q); [lia|exact HR|unfold guard; lia].
Qed.

Lemma odd_entry m n r : RC d1 (1+n*2) r ->
  2*n<=gap0 (repeat false (1+m)) -> exists c', Allowed QR c' /\
  C QR (repeat false m) ([1] *> r) -[tm]->+ c'.
Proof.
  intros Hr Hb; destruct (RC_odd_inv _ _ _ Hr) as [s [Hs ->]].
  pose proof (Eleven 0 (repeat false m) ([0;0;0] *> s)) as HS.
  pose proof (ShiftDigits _ _ Hs) as HR.
  assert (HE:C QR (repeat false m) ([1] *> d1 *> s) -[tm]->+
    C QR (repeat false (1+m)) ([0;0;0] *> s)).
  { applys_eq HS; unfold d1; st; reflexivity. }
  destruct n as [|n].
  - apply RC_zero_unique in HR; rewrite HR in HE.
    eexists; split; [apply Blank|exact HE].
  - eexists; split; [|exact HE].
    eapply Shifted with (n:=S n); [lia|exact HR|].
    unfold guard; pose proof (zero_gap_order (1+m)); lia.
Qed.
End Semantics.
End PairPostEntry.

(* Shared: SOCPair12Closure.v/Pair12Closure. *)
Module Pair12Closure.
Import PairWord PairGuard PairOverflow Pair12Right PairRegion PairPostEntry.
Local Open Scope sym_scope.

Lemma length_split (w:list bool) : exists k p, p<=2 /\ length w=3*k+p.
Proof.
  exists (length w/3),(length w mod 3).
  pose proof (Nat.div_mod (length w) 3 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (length w) 3 ltac:(lia)); lia.
Qed.

Lemma capacity_bound k p w : p<=2 -> length w=3*k+p -> gap0 w<=2^p*4^k.
Proof.
  intros HP HL; pose proof (value_gap0 w) as H.
  rewrite (width_length k p w HP HL), Nat.pow_add_r, PairEntryGuard.pow24 in H.
  nia.
Qed.

Lemma right_one : RC d1 1 ([1] *> (0inf)%sym).
Proof. applys_eq (RC_d1 d1 0 _ (RC_zero d1)); unfold d1; st; reflexivity. Qed.

Section OrdinaryOrder.
Variables (tm:TM) (QR:Q).
Hypothesis Ordinary : forall z w v r, inc_steps (2^(z+1)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR (repeat true (2*z)++false::v) ([0;0;0] *> r).
Lemma ordinary_order z w v r : inc_steps (2^(1+z)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -[tm]->+
  C QR (repeat true (2*z)++false::v) ([0;0;0] *> r).
Proof. replace (1+z) with (z+1) by lia; apply Ordinary. Qed.
End OrdinaryOrder.

Section Semantics.
Variables (tm:TM) (QR:Q).
Hypothesis Entry0 : forall k w x r, length w=3*k -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w+2*4^k) s /\
  C QR w r -[tm]->+ C QR (repeat false (3*k+1)) ([1] *> s).
Hypothesis Entry12 : forall k p w x r,
  1<=p -> p<=2 -> length w=3*k+p -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w) s /\
  C QR w r -[tm]->+ C QR (repeat false (3*k+p)) ([1] *> s).
Hypothesis PostFirst : forall k p T r, (p=1%nat \/ p=2%nat) ->
  RC d1 T r -> 0<T -> T<=limit k p -> exists c', Allowed QR c' /\
  C QR (repeat false (3*k+p)) ([1] *> r) -[tm]->+ c'.
Hypothesis OddEntry : forall m n r, RC d1 (1+n*2) r ->
  2*n<=gap0 (repeat false (1+m)) -> exists c', Allowed QR c' /\
  C QR (repeat false m) ([1] *> r) -[tm]->+ c'.
Hypothesis ShiftedStep : forall n w r,
  0<n -> RC ds n r -> guard n w -> exists c', Allowed QR c' /\
  C QR w r -[tm]->+ c'.

Lemma blank_step w : exists c', Allowed QR c' /\
  C QR w (0inf)%sym -[tm]->+ c'.
Proof.
  destruct (length_split w) as [k [p [HP HL]]].
  pose proof (capacity_bound k p w HP HL) as HB.
  pose proof (gap_bounds w) as HG.
  destruct (Nat.eq_dec p 0) as [->|HN].
  - rewrite Nat.add_0_r in HL; cbn [Nat.pow] in HB.
    destruct (Entry0 k w 0 _ HL (RC_zero d1)) as [s [HR HS]].
    destruct (PostFirst k 1 _ s ltac:(lia) HR ltac:(lia)
      ltac:(unfold limit; cbn [Nat.eqb]; lia)) as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
  - assert (HF:p=1%nat \/ p=2%nat) by lia.
    assert (HB':gap0 w<=limit k p).
    { unfold limit; destruct HF as [->| ->]; cbn [Nat.eqb Nat.pow] in *; nia. }
    destruct (Entry12 k p w 0 _ ltac:(lia) HP HL (RC_zero d1)) as [s [HR HS]].
    destruct (PostFirst k p _ s HF HR ltac:(lia) HB') as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
Qed.

Lemma one_step w : w<>[] -> Nat.Even (value w) -> exists c', Allowed QR c' /\
  C QR w ([1] *> (0inf)%sym) -[tm]->+ c'.
Proof.
  intros HW HV; destruct (even_gap w HW HV) as [a HA].
  destruct (length_split w) as [k [p [HP HL]]].
  pose proof (capacity_bound k p w HP HL) as HB.
  destruct (Nat.eq_dec p 0) as [->|HN].
  - rewrite Nat.add_0_r in HL; cbn [Nat.pow] in HB.
    destruct (Entry0 k w 1 _ HL right_one) as [s [HR HS]].
    replace (1+gap0 w+2*4^k) with (1+(a+4^k)*2) in HR by lia.
    assert (HG:2*(a+4^k)<=gap0 (repeat false (1+(3*k+1)))).
    { pose proof (PairEntryGuard.zero_entry k 1 ltac:(lia)) as [HZ _].
      change (2*(a+4^k)<=gap0 (false::repeat false (3*k+1))); nia. }
    destruct (OddEntry (3*k+1) (a+4^k) s HR HG) as [c' [HC HT]].
    exists c'; split; [exact HC|eapply progress_trans; eassumption].
  - assert (HF:p=1%nat \/ p=2%nat) by lia.
    assert (HB':gap0 w<=4*4^k).
    { destruct HF as [->| ->]; cbn [Nat.pow] in *; nia. }
    destruct (Entry12 k p w 1 _ ltac:(lia) HP HL right_one) as [s [HR HS]].
    replace (1+gap0 w) with (1+a*2) in HR by lia.
    assert (HG:2*a<=gap0 (repeat false (1+(3*k+p)))).
    { pose proof (PairEntryGuard.zero_entry k p HF) as [HZ _].
      change (2*a<=gap0 (false::repeat false (3*k+p))); nia. }
    destruct (OddEntry (3*k+p) a s HR HG) as [c' [HC HT]].
    exists c'; split; [exact HC|eapply progress_trans; eassumption].
Qed.

Lemma step c : Allowed QR c -> exists c', Allowed QR c' /\ c -[tm]->+ c'.
Proof.
  intros [w|w HN HE|w n r HN HR HG].
  - apply blank_step.
  - apply one_step; assumption.
  - apply (ShiftedStep n w r); assumption.
Qed.

Lemma nonhalt c : Allowed QR c -> ~halts tm c.
Proof. apply (progress_nonhalt tm (Allowed QR) c step). Qed.
End Semantics.
End Pair12Closure.

Module TM1.
Local Open Scope sym_scope.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_1RA0LD_1RC---").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Definition d3 : list sym := <[1;0;1;1;1;1].

Lemma RInc4 l r n :
  l <* <[1;0] {{A}}> [1;0;0;0]^^n *> [0] *> r -->+
  l <* <[1;0] <{{B}} [0;0;0;0]^^n *> [1] *> r.
Proof. es. Qed.

Lemma LCarry l r n :
  l <* d3^^n <* <[1;0] <{{B}} r -->+
  l {{C}}> [1;1] *> [1;1;1;1;1;1]^^n *> r.
Proof. unfold d3; es. Qed.

Module A1Words.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Lemma ZCarryMarked (b:bool) l r :
  l <* (if b then <[1;1;1;1;1;1] else <[1;0;1;1;1;1]) {{C}}> [1] *> r -->+
  l {{C}}> [1;1;1;1;1;1;1] *> r.
Proof. destruct b; es. Qed.

Lemma ZInc w r : let '(v,e):=PairWord.inc w in
  PairWord.data w {{C}}> [1;1] *> r -->+
  PairWord.data v <* <[1;0] {{A}}> PairWord.insert e r.
Proof.
  revert w r; fix IH 1; intros w r.
  destruct w as [|b0 w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  destruct b0; [|cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es].
  destruct w as [|b1 w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  destruct b1; [|cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es].
  destruct w as [|b w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  cbn [PairWord.inc].
  destruct (PairWord.inc w) as [v e] eqn:E.
  eapply progress_trans.
  - applys_eq (ZCarryMarked b (PairWord.data w) ([1] *> r));
      cbn [PairWord.data PairWord.pairs PairWord.bit]; destruct b; st; reflexivity.
  - eapply progress_trans.
    + pose proof (IH w ([1;1;1;1;1;1] *> r)) as H.
      rewrite E in H; cbn in H. applys_eq H; st; reflexivity.
    + destruct e; cbn [PairWord.insert PairWord.data PairWord.pairs PairWord.bit]; es.
Qed.

Lemma LIncWord w r : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] <{{B}} r -->+
  PairWord.data v <* <[1;0] {{A}}> PairWord.insert e r.
Proof.
  pose proof (ZInc w r) as H; destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [|exact H].
  applys_eq (LCarry (PairWord.data w) r 0); st; reflexivity.
Qed.

Lemma R1001_mod0 l r n :
  l <* <[1;0] {{A}}> [1;0;0;0]^^(n*3) *> [1;0;0;1] *> r -->+
  l <* <[1;1] <* <[1;0]^^(n*6+2) {{A}}> r.
Proof. es' n & l r. Qed.

Lemma R1001_mod2 l r n :
  l <* <[1;0] {{A}}> [1;0;0;0]^^(n*3+2) *> [1;0;0;1] *> r -->+
  l <* <[1;1] <* <[1;0]^^(n*6+6) {{A}}> r.
Proof. es' n & l r. Qed.

Lemma R1001_call l r n :
  l <* <[1;0] {{A}}> [1;0;0;0]^^(n*3+1) *> [1;0;0;1] *> r -->+
  l {{C}}> [1;1] *> [1;1;1;1]^^(n*3+2) *> r.
Proof. es' n & l r. Qed.

Lemma R1001_return w r n : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] {{A}}>
    [1;0;0;0]^^(n*3+1) *> [1;0;0;1] *> r -->+
  PairWord.data (PairWord.push0 (n*6+4) v) <* <[1;0] {{A}}> PairWord.insert e r.
Proof.
  pose proof (ZInc w ([1;1;1;1]^^(n*3+2) *> r)) as H.
  destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [apply R1001_call|].
  eapply progress_trans; [exact H|].
  rewrite PairWord.data_push0.
  remember (PairWord.data v) as l eqn:El.
  rewrite PairWord.ones4_twice.
  replace ((n*3+2)*2) with (n*6+4) by lia.
  rewrite PairWord.insert_scan; es.
Qed.

Lemma RZero w r n : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] {{A}}> [1;0;0;0]^^n *> [0] *> r -->+
  PairWord.data v <* <[1;0] {{A}}>
    PairWord.insert e ([0;0;0;0]^^n *> [1] *> r).
Proof.
  pose proof (LIncWord w ([0;0;0;0]^^n *> [1] *> r)) as H.
  destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [apply RInc4|exact H].
Qed.

Lemma REleven l r n :
  l <* <[1;0] {{A}}> [1;0;0;0]^^n *> [1;1] *> r -->+
  l <* <[1;0] <* [1;1]^^(n*2) <* <[1;0] {{A}}> r.
Proof. es' n & l r. Qed.

Lemma init : c0 -[tm]->* PairWord.data [] <* <[1;0] {{A}}> 0inf.
Proof. cbn [PairWord.data PairWord.pairs]; esx. Qed.
End A1Words.

Module A1Right.
Definition step := Pair12Right.right_step tm A A1Words.RZero.
Definition steps := Pair12Right.right_steps tm A A1Words.RZero.
Definition finite_step := Pair12Right.finite_step tm A A1Words.RZero.
Definition finite_steps := Pair12Right.finite_steps tm A A1Words.RZero.
End A1Right.

Module A1Shift.
Definition shifted := PairShift.shifted tm A A1Words.RZero
  A1Words.R1001_mod0 A1Words.R1001_mod2 A1Words.R1001_return.
End A1Shift.

Module A1Region.
Definition shifted_step := PairRegion.shifted_step tm A
  (PairShift.shifted_prefix tm A A1Words.RZero)
  (PairShift.finish_signal tm A A1Words.R1001_mod0 A1Words.R1001_mod2 A1Words.R1001_return)
  A1Shift.shifted A1Words.R1001_return.
End A1Region.

Module A1Entry.
Definition phase12 := Pair12Entry.phase12 tm A A1Words.RZero.
Definition phase0_extend := Pair12Entry.phase0_extend tm A A1Words.RZero.
Definition phase0 := Pair12Entry.phase0 tm A A1Words.RZero.
End A1Entry.

Module A1Ordinary.
Definition one_cross := PairOrdinary.one_cross tm A A1Words.RZero.
Definition prefix := PairOrdinary.prefix tm A A1Words.RZero.
Definition eleven_word := PairOrdinary.eleven_word tm A A1Words.REleven.
Definition ordinary := PairOrdinary.ordinary tm A A1Words.RZero A1Words.REleven.
End A1Ordinary.

Module A1Exceptional.
Definition last_signal_one := PairExceptional.last_signal_one tm A A1Words.REleven
  (PairShift.finish_signal tm A A1Words.R1001_mod0 A1Words.R1001_mod2 A1Words.R1001_return)
  A1Words.R1001_return.
Definition exceptional := PairExceptional.exceptional tm A A1Words.RZero A1Words.REleven
  (PairShift.finish_signal tm A A1Words.R1001_mod0 A1Words.R1001_mod2 A1Words.R1001_return)
  A1Words.R1001_return A1Ordinary.one_cross.
End A1Exceptional.

Module A1PostEntry.
Definition post_first := PairPostEntry.post_first tm A
  (Pair12Closure.ordinary_order tm A A1Ordinary.ordinary)
  PairOrdinary.RC_shift3 A1Exceptional.exceptional.
Definition odd_entry := PairPostEntry.odd_entry tm A
  PairOrdinary.RC_shift3 A1Ordinary.eleven_word.
End A1PostEntry.

Definition closed := Pair12Closure.nonhalt tm A A1Entry.phase0 A1Entry.phase12
  A1PostEntry.post_first A1PostEntry.odd_entry A1Region.shifted_step.
Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact A1Words.init|apply closed; constructor].
Qed.
End TM1.

Module TM2.
Local Open Scope sym_scope.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Definition d3 : list sym := <[1;0;1;1;1;1].

Lemma RInc4 l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^n *> [0] *> r -->+
  l <* <[1;0] <{{D}} [0;0;0;0]^^n *> [1] *> r.
Proof. es. Qed.

Lemma LCarry l r n :
  l <* d3^^n <* <[1;0] <{{D}} r -->+
  l {{B}}> [1;1] *> [1;1;1;1;1;1]^^n *> r.
Proof. unfold d3; es. Qed.

Module A2Words.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Lemma ZCarryMarked (b:bool) l r :
  l <* (if b then <[1;1;1;1;1;1] else <[1;0;1;1;1;1]) {{B}}> [1] *> r -->+
  l {{B}}> [1;1;1;1;1;1;1] *> r.
Proof. destruct b; es. Qed.

Lemma ZInc w r : let '(v,e):=PairWord.inc w in
  PairWord.data w {{B}}> [1;1] *> r -->+
  PairWord.data v <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  revert w r; fix IH 1; intros w r.
  destruct w as [|b0 w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  destruct b0; [|cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es].
  destruct w as [|b1 w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  destruct b1; [|cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es].
  destruct w as [|b w]; [cbn [PairWord.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es|].
  cbn [PairWord.inc].
  destruct (PairWord.inc w) as [v e] eqn:E.
  eapply progress_trans.
  - applys_eq (ZCarryMarked b (PairWord.data w) ([1] *> r));
      cbn [PairWord.data PairWord.pairs PairWord.bit]; destruct b; st; reflexivity.
  - eapply progress_trans.
    + pose proof (IH w ([1;1;1;1;1;1] *> r)) as H.
      rewrite E in H; cbn in H. applys_eq H; st; reflexivity.
    + destruct e; cbn [PairWord.insert PairWord.data PairWord.pairs PairWord.bit]; es.
Qed.

Lemma LIncWord w r : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] <{{D}} r -->+
  PairWord.data v <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  pose proof (ZInc w r) as H; destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [|exact H].
  applys_eq (LCarry (PairWord.data w) r 0); st; reflexivity.
Qed.

Lemma R1001_mod0 l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^(n*3) *> [1;0;0;1] *> r -->+
  l <* <[1;1] <* <[1;0]^^(n*6+2) {{C}}> r.
Proof. es' n & l r. Qed.

Lemma R1001_mod2 l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^(n*3+2) *> [1;0;0;1] *> r -->+
  l <* <[1;1] <* <[1;0]^^(n*6+6) {{C}}> r.
Proof. es' n & l r. Qed.

Lemma R1001_call l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^(n*3+1) *> [1;0;0;1] *> r -->+
  l {{B}}> [1;1] *> [1;1;1;1]^^(n*3+2) *> r.
Proof. es' n & l r. Qed.

Lemma R1001_return w r n : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] {{C}}>
    [1;0;0;0]^^(n*3+1) *> [1;0;0;1] *> r -->+
  PairWord.data (PairWord.push0 (n*6+4) v) <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  pose proof (ZInc w ([1;1;1;1]^^(n*3+2) *> r)) as H.
  destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [apply R1001_call|].
  eapply progress_trans; [exact H|].
  rewrite PairWord.data_push0.
  remember (PairWord.data v) as l eqn:El.
  rewrite PairWord.ones4_twice.
  replace ((n*3+2)*2) with (n*6+4) by lia.
  rewrite PairWord.insert_scan; es.
Qed.

Lemma RZero w r n : let '(v,e):=PairWord.inc w in
  PairWord.data w <* <[1;0] {{C}}> [1;0;0;0]^^n *> [0] *> r -->+
  PairWord.data v <* <[1;0] {{C}}>
    PairWord.insert e ([0;0;0;0]^^n *> [1] *> r).
Proof.
  pose proof (LIncWord w ([0;0;0;0]^^n *> [1] *> r)) as H.
  destruct (PairWord.inc w) as [v e].
  eapply progress_trans; [apply RInc4|exact H].
Qed.

Lemma REleven l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^n *> [1;1] *> r -->+
  l <* <[1;0] <* [1;1]^^(n*2) <* <[1;0] {{C}}> r.
Proof. es' n & l r. Qed.

Lemma init : c0 -[tm]->* PairWord.data [] <* <[1;0] {{C}}> [0;1] *> 0inf.
Proof. cbn [PairWord.data PairWord.pairs]; esx. Qed.
End A2Words.

Module A2Right.
Definition step := Pair12Right.right_step tm C A2Words.RZero.
Definition steps := Pair12Right.right_steps tm C A2Words.RZero.
Definition finite_step := Pair12Right.finite_step tm C A2Words.RZero.
Definition finite_steps := Pair12Right.finite_steps tm C A2Words.RZero.
End A2Right.

Module A2Shift.
Definition shifted := PairShift.shifted tm C A2Words.RZero
  A2Words.R1001_mod0 A2Words.R1001_mod2 A2Words.R1001_return.
End A2Shift.

Module A2Region.
Definition shifted_step := PairRegion.shifted_step tm C
  (PairShift.shifted_prefix tm C A2Words.RZero)
  (PairShift.finish_signal tm C A2Words.R1001_mod0 A2Words.R1001_mod2 A2Words.R1001_return)
  A2Shift.shifted A2Words.R1001_return.
End A2Region.

Module A2Entry.
Definition phase12 := Pair12Entry.phase12 tm C A2Words.RZero.
Definition phase0_extend := Pair12Entry.phase0_extend tm C A2Words.RZero.
Definition phase0 := Pair12Entry.phase0 tm C A2Words.RZero.
End A2Entry.

Module A2Ordinary.
Definition one_cross := PairOrdinary.one_cross tm C A2Words.RZero.
Definition prefix := PairOrdinary.prefix tm C A2Words.RZero.
Definition eleven_word := PairOrdinary.eleven_word tm C A2Words.REleven.
Definition ordinary := PairOrdinary.ordinary tm C A2Words.RZero A2Words.REleven.
End A2Ordinary.

Module A2Exceptional.
Definition last_signal_one := PairExceptional.last_signal_one tm C A2Words.REleven
  (PairShift.finish_signal tm C A2Words.R1001_mod0 A2Words.R1001_mod2 A2Words.R1001_return)
  A2Words.R1001_return.
Definition exceptional := PairExceptional.exceptional tm C A2Words.RZero A2Words.REleven
  (PairShift.finish_signal tm C A2Words.R1001_mod0 A2Words.R1001_mod2 A2Words.R1001_return)
  A2Words.R1001_return A2Ordinary.one_cross.
End A2Exceptional.

Module A2PostEntry.
Definition post_first := PairPostEntry.post_first tm C
  (Pair12Closure.ordinary_order tm C A2Ordinary.ordinary)
  PairOrdinary.RC_shift3 A2Exceptional.exceptional.
Definition odd_entry := PairPostEntry.odd_entry tm C
  PairOrdinary.RC_shift3 A2Ordinary.eleven_word.
End A2PostEntry.

Local Open Scope sym_scope.
Definition closed := Pair12Closure.nonhalt tm C A2Entry.phase0 A2Entry.phase12
  A2PostEntry.post_first A2PostEntry.odd_entry A2Region.shifted_step.
Lemma init : c0 -[tm]->* Pair12Right.C C [false;false] (0inf)%sym.
Proof.
  follow A2Words.init.
  follow100 (A2Words.RZero [] ([1] *> (0inf)%sym) 0).
  apply progress_evstep; exact (A2Ordinary.eleven_word 0 [false] (0inf)%sym).
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init|apply closed; constructor]. Qed.
End TM2.

(* A3 shares PairWord, Pair12Right and PairOrdinary with A1/A2.
   Their duplicate definitions and proofs have been removed. *)
(* Shared: SOCPair3Words.v/Pair3Word. *)
Module Pair3Word.
Fixpoint inc (w:list bool) : list bool*bool := match w with
  | [] => ([false],false)
  | a::[] => ([false;false],true)
  | a::false::u => (false::true::u,false)
  | a::true::[] => ([false;false],true)
  | a::true::b::u => let '(v,e):=inc u in (false::false::false::v,e)
  end.

Lemma pairs_ones n w : PairWord.pairs (repeat true n++w)=
  [1;1]^^n++PairWord.pairs w.
Proof.
  induction n; cbn [repeat app PairWord.pairs PairWord.bit lpow];
    [reflexivity|now rewrite IHn].
Qed.

Lemma data_ones n w : PairWord.data (repeat true n++w)=
  PairWord.data w <* [1;1]^^n.
Proof. unfold PairWord.data; rewrite pairs_ones; st; reflexivity. Qed.
End Pair3Word.

(* Shared: SOCPair3Guard.v/Pair3Guard. *)
Module Pair3Guard.
Open Scope nat_scope.
Definition bit_value (b:bool) : nat := if b then 1 else 0.
Definition zero_bit (b:bool) : nat := if b then 0 else 1.
Fixpoint plane (f:bool->nat) (i:nat) (w:list bool) : nat :=
  match w with [] => 0 | b::u => match i with
  | 0 => f b+2*plane f 2 u | S j => plane f j u end end.
Fixpoint width (w:list bool) : nat := match w with
  | [] | [_] => 0 | [_;_] => 1 | _::_::_::u => 1+width u end.
Definition value w := plane bit_value 1 w.
Definition gap0 w := 1+plane zero_bit 1 w.
Definition gap1 w := 1+plane zero_bit 0 w.
Definition gap2 w := 2+2*plane zero_bit 2 w.
Definition guard (n:nat) w := n<=gap0 w /\ n<=gap1 w /\ n<=gap2 w.

Lemma gap_bounds w : guard 1 w.
Proof. unfold guard,gap0,gap1,gap2; lia. Qed.

Lemma value_gap0 w : value w+gap0 w=2^width w.
Proof.
  revert w; fix IH 1; intros [|a [|b [|c u]]];
    try (unfold value,gap0; cbn [plane width Nat.pow zero_bit bit_value]; lia).
  - destruct b; reflexivity.
  - pose proof (IH u); unfold value,gap0 in *.
    destruct b; cbn [plane width Nat.add Nat.pow zero_bit bit_value]; lia.
Qed.

Lemma gap_cons b w :
  gap0 (b::w)=gap1 w /\ gap1 (b::w)+bit_value b=gap2 w /\
  gap2 (b::w)=2*gap0 w.
Proof.
  unfold gap0,gap1,gap2; destruct b;
    cbn [plane zero_bit bit_value]; lia.
Qed.

Lemma guard_zero n w : guard n w -> guard n (false::w).
Proof. unfold guard; pose proof (gap_cons false w); cbn [bit_value] in *; lia. Qed.

Lemma guard_one n w : guard (n+1) w -> guard n (true::w).
Proof. unfold guard; pose proof (gap_cons true w); cbn [bit_value] in *; lia. Qed.

Lemma inc_head w v e : Pair3Word.inc w=(v,e) -> exists u, v=false::u.
Proof.
  destruct w as [|a [|b [|c u]]]; cbn [Pair3Word.inc];
    try destruct b; try destruct (Pair3Word.inc u) as [v' e'];
    intros E; inversion E; eauto.
Qed.

Lemma inc_mono w v e : Pair3Word.inc w=(v,e) ->
  gap1 w<=gap1 v /\ gap2 w<=gap2 v.
Proof.
  revert w v e; fix IH 1; intros [|a [|b [|c u]]] v e E;
    cbn [Pair3Word.inc] in E.
  - inversion E; subst; unfold gap1,gap2; cbn [plane zero_bit]; lia.
  - inversion E; subst; unfold gap1,gap2; destruct a; cbn [plane zero_bit]; lia.
  - destruct b; inversion E; subst; unfold gap1,gap2;
      destruct a; cbn [plane zero_bit]; lia.
  - destruct b.
    + destruct (Pair3Word.inc u) as [v' e'] eqn:F; inversion E; subst v e.
      pose proof (IH u v' e' F); unfold gap1,gap2 in *.
      destruct a,c; cbn [plane zero_bit] in *; lia.
    + inversion E; subst; unfold gap1,gap2;
        destruct a; cbn [plane zero_bit]; lia.
Qed.

Lemma inc_interior w v e : Pair3Word.inc w=(v,e) -> 1<gap0 w ->
  e=false /\ length v=length w /\ gap0 v+1=gap0 w.
Proof.
  revert w v e; fix IH 1; intros [|a [|b [|c u]]] v e E H;
    cbn [Pair3Word.inc] in E.
  - unfold gap0 in H; cbn [plane] in H; lia.
  - unfold gap0 in H; cbn [plane] in H; lia.
  - destruct b.
    + unfold gap0 in H; cbn [plane zero_bit] in H; lia.
    + inversion E; subst; repeat split; try reflexivity.
  - destruct b.
    + assert (Hu:1<gap0 u) by
        (unfold gap0 in *; cbn [plane zero_bit] in *; lia).
      destruct (Pair3Word.inc u) as [v' e'] eqn:F; inversion E; subst v e.
      destruct (IH u v' e' F Hu) as [He [Hl Hg]]; subst e'.
      split; [reflexivity|]; split; [cbn [length]; lia|].
      unfold gap0 in *; cbn [plane zero_bit] in *; lia.
    + inversion E; subst; split; [reflexivity|]; split; [reflexivity|].
      unfold gap0; cbn [plane zero_bit]; lia.
Qed.

Inductive inc_steps : nat -> list bool -> list bool -> Prop :=
| inc_steps_zero w : inc_steps 0 w w
| inc_steps_succ q w u v :
    Pair3Word.inc w=(u,false) -> inc_steps q u v -> inc_steps (S q) w v.

Lemma inc_steps_interior q w : q<gap0 w -> exists v,
  inc_steps q w v /\ length v=length w /\ gap0 v+q=gap0 w.
Proof.
  revert w; induction q as [|q IH]; intros w H.
  - exists w; split; [constructor|]; split; [reflexivity|lia].
  - destruct (Pair3Word.inc w) as [u e] eqn:E.
    destruct (inc_interior w u e E ltac:(lia)) as [He [Hl Hg]]; subst e.
    destruct (IH u ltac:(lia)) as [v [Hs [Hv HG]]].
    exists v; split; [econstructor; eassumption|]; split; lia.
Qed.

Lemma inc_steps_mono q w v : inc_steps q w v ->
  gap1 w<=gap1 v /\ gap2 w<=gap2 v.
Proof. intro H; induction H; [lia|pose proof (inc_mono _ _ _ H); lia]. Qed.

Lemma inc_steps_add_inv p q w v : inc_steps (p+q) w v -> exists u,
  inc_steps p w u /\ inc_steps q u v.
Proof.
  revert w; induction p as [|p IH]; intros w H.
  - exists w; split; [constructor|exact H].
  - inversion H as [|q' w' u' v' E HS]; subst.
    destruct (IH _ HS) as [mid [Hp Hq]].
    exists mid; split; [econstructor; eassumption|exact Hq].
Qed.

Lemma guard_mono m n w : guard m w -> n<=m -> guard n w.
Proof. unfold guard; lia. Qed.

Lemma guard_two_ones n w : guard (n+1) w -> guard n (true::true::w).
Proof. unfold guard,gap0,gap1,gap2; cbn [plane zero_bit]; lia. Qed.

Lemma guard_three_ones n w : 2<=n -> guard n w ->
  guard n (true::true::true::w).
Proof. unfold guard,gap0,gap1,gap2; cbn [plane zero_bit]; lia. Qed.

Lemma guard_ones n k w : 1<=n -> guard (n+1) w ->
  guard n (repeat true k++w).
Proof.
  intro Hn; destruct n as [|[|n]]; [lia|intros; apply gap_bounds|].
  revert k w; fix IH 1; intros [|[|[|k]]] w H; cbn [repeat app].
  - eapply guard_mono; [exact H|lia].
  - now apply guard_one.
  - now apply guard_two_ones.
  - apply guard_three_ones; [lia|now apply IH].
Qed.

Lemma inc_guard n w v e : 1<=n -> guard (n+1) w ->
  Pair3Word.inc w=(v,e) -> e=false /\ guard n v.
Proof.
  intros Hn HG E; pose proof (inc_mono _ _ _ E).
  destruct (inc_interior _ _ _ E ltac:(unfold guard in HG; lia)) as [He [HL HD]].
  split; [exact He|unfold guard in *; lia].
Qed.
End Pair3Guard.

(* Shared: SOCPair3EntryGuard.v/Pair3EntryGuard. *)
Module Pair3EntryGuard.
Import Pair3Guard.
Open Scope nat_scope.

Lemma width_length k p w : p<=2 -> length w=3*k+p ->
  width w=k+(if Nat.eqb p 2 then 1 else 0).
Proof.
  revert w; induction k as [|k IH]; intros w Hp Hl.
  - destruct p as [|[|[|p]]]; try lia;
      destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia; reflexivity.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    cbn [width]; rewrite (IH w Hp ltac:(lia)); lia.
Qed.

Lemma plane_zeros n i : plane bit_value i (repeat false n)=0.
Proof.
  revert i; induction n as [|n IH]; intros [|i]; cbn [repeat plane bit_value];
    rewrite ?IH; reflexivity.
Qed.

Lemma value_zeros n : value (repeat false n)=0.
Proof. unfold value; apply plane_zeros. Qed.

Lemma width_zeros k p : p<=2 ->
  width (repeat false (3*k+p))=k+(if Nat.eqb p 2 then 1 else 0).
Proof. intro Hp; apply width_length; [exact Hp|apply repeat_length]. Qed.

Lemma gap0_zeros k p : p<=2 ->
  gap0 (repeat false (3*k+p))=2^(k+(if Nat.eqb p 2 then 1 else 0)).
Proof.
  intro Hp; pose proof (value_gap0 (repeat false (3*k+p))) as H.
  rewrite value_zeros,(width_zeros k p Hp) in H; exact H.
Qed.

Lemma inc_at_capacity k p w : p<=2 -> length w=3*k+p -> gap0 w=1 ->
  Pair3Word.inc w=
  match p with
  | 0 => (repeat false (3*k+1),false)
  | _ => (repeat false (3*k+2),true)
  end.
Proof.
  revert w; induction k as [|k IH]; intros w Hp Hl Hg.
  - destruct p as [|[|[|p]]]; try lia;
      destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    all: try destruct b; unfold gap0 in Hg;
      cbn [plane zero_bit] in Hg; try lia; reflexivity.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    assert (Hb:b=true /\ gap0 w=1).
    { unfold gap0 in *; cbn [plane] in Hg.
      destruct b; cbn [zero_bit] in Hg; lia. }
    destruct Hb as [-> Htail].
    cbn [Pair3Word.inc]; rewrite (IH w Hp ltac:(lia) Htail).
    destruct p.
    + replace (3*S k+1) with (3+(3*k+1)) by lia; reflexivity.
    + replace (3*S k+2) with (3+(3*k+2)) by lia; reflexivity.
Qed.

Lemma overflow12 k p w : 1<=p<=2 -> length w=3*k+p -> gap0 w=1 ->
  Pair3Word.inc w=(repeat false (3*k+2),true).
Proof.
  intros Hp Hl Hg; pose proof (inc_at_capacity k p w ltac:(lia) Hl Hg).
  destruct p; [lia|assumption].
Qed.

Lemma first_capacity k p w : p<=2 -> length w=3*k+p -> exists u,
  inc_steps (gap0 w-1) w u /\ length u=length w /\ gap0 u=1 /\
  Pair3Word.inc u=
  match p with
  | 0 => (repeat false (3*k+1),false)
  | _ => (repeat false (3*k+2),true)
  end.
Proof.
  intros Hp Hl; pose proof (gap_bounds w) as HB; unfold guard in HB.
  destruct (inc_steps_interior (gap0 w-1) w ltac:(lia))
    as [u [HS [Hlen Hgap]]].
  assert (Hu:gap0 u=1) by lia.
  exists u; split; [exact HS|]; split; [exact Hlen|]; split; [exact Hu|].
  apply inc_at_capacity; [exact Hp|lia|exact Hu].
Qed.

Lemma inc_markers_mono w v e : Pair3Word.inc w=(v,e) ->
  plane bit_value 0 v<=plane bit_value 0 w /\
  plane bit_value 2 v<=plane bit_value 2 w.
Proof.
  revert w v e; fix IH 1; intros [|a [|b [|c u]]] v e E;
    cbn [Pair3Word.inc] in E.
  - inversion E; subst; split; reflexivity.
  - inversion E; subst; cbn [plane bit_value]; lia.
  - destruct b; inversion E; subst; cbn [plane bit_value]; lia.
  - destruct b.
    + destruct (Pair3Word.inc u) as [v' e'] eqn:F; inversion E; subst.
      pose proof (IH u v' e F); cbn [plane bit_value]; lia.
    + inversion E; subst; cbn [plane bit_value]; lia.
Qed.

Lemma inc_steps_markers_zero q w v : inc_steps q w v ->
  plane bit_value 0 w=0 -> plane bit_value 2 w=0 ->
  plane bit_value 0 v=0 /\ plane bit_value 2 v=0.
Proof.
  intro HS; induction HS as [w|q w u v EI HS IH]; intros H0 H2; [tauto|].
  pose proof (inc_markers_mono w u false EI) as HM.
  apply IH; lia.
Qed.

Lemma marker_gaps k w : length w=3*k+2 ->
  plane bit_value 0 w=0 -> plane bit_value 2 w=0 ->
  gap1 w=2^(k+1) /\ gap2 w=2^(k+1).
Proof.
  revert w; induction k as [|k IH]; intros w Hl H0 H2.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    destruct a; cbn [plane bit_value] in H0; try lia.
    unfold gap1,gap2; split; reflexivity.
  - destruct w as [|a [|b [|c w]]]; cbn [length] in Hl; try lia.
    assert (Ha:a=false /\ c=false /\
      plane bit_value 0 w=0 /\ plane bit_value 2 w=0).
    { cbn [plane] in H0,H2; destruct a,c; cbn [bit_value] in H0,H2; lia. }
    destruct Ha as [-> [-> [Hw0 Hw2]]].
    destruct (IH w ltac:(lia) Hw0 Hw2) as [Hg1 Hg2].
    unfold gap1,gap2 in *; cbn [plane zero_bit].
    replace (S k+1) with (S (k+1)) by lia; cbn [Nat.pow]; lia.
Qed.

Lemma zero2_gaps k :
  gap0 (repeat false (3*k+2))=2^(k+1) /\
  gap1 (repeat false (3*k+2))=2^(k+1) /\
  gap2 (repeat false (3*k+2))=2^(k+1).
Proof.
  split; [exact (gap0_zeros k 2 ltac:(lia))|].
  apply marker_gaps; [apply repeat_length|apply plane_zeros|apply plane_zeros].
Qed.

Lemma zero3_gaps k :
  gap0 (repeat false (3*k+3))=2^(k+1) /\
  gap1 (repeat false (3*k+3))=2^(k+1) /\
  gap2 (repeat false (3*k+3))=2^(k+2).
Proof.
  replace (3*k+3) with (S (3*k+2)) by lia; cbn [repeat].
  pose proof (zero2_gaps k).
  pose proof (gap_cons false (repeat false (3*k+2))).
  cbn [bit_value] in *.
  replace (k+2) with (S (k+1)) by lia; cbn [Nat.pow]; lia.
Qed.

Lemma strong k z w : length w=3*k+2 ->
  plane bit_value 0 w=0 -> plane bit_value 2 w=0 ->
  value w=2^(z+1)-2 -> z<=k ->
  guard (2^(k+1-z)) (repeat true (2*z)++false::w).
Proof.
  intros Hl H0 H2 Hv Hz.
  destruct (marker_gaps k w Hl H0 H2) as [HG1 HG2].
  pose proof (value_gap0 w) as Hsum.
  rewrite (width_length k 2 w ltac:(lia) Hl),Hv in Hsum.
  assert (Pz:2<=2^(z+1)).
  { replace 2 with (2^1) by reflexivity; apply Nat.pow_le_mono_r; lia. }
  assert (HG:gap0 w+2^(z+1)=2^(k+1)+2) by (cbn [Nat.eqb] in Hsum; lia).
  pose proof (gap_cons false w) as HC; cbn [bit_value] in HC.
  destruct (Nat.eq_dec z 0) as [->|Hz0].
  - cbn [Nat.mul Nat.add repeat app]; rewrite Nat.sub_0_r.
    unfold guard; cbn [Nat.add Nat.pow] in HG; lia.
  - apply guard_ones.
    + pose proof (Nat.pow_nonzero 2 (k+1-z) ltac:(lia)); lia.
    + assert (HB:2*2^(k+1-z)<=2^(k+1)).
      { change (2^(S (k+1-z))<=2^(k+1)).
        apply Nat.pow_le_mono_r; lia. }
      assert (HP:1<=2^(k+1-z)) by
        (pose proof (Nat.pow_nonzero 2 (k+1-z) ltac:(lia)); lia).
      assert (HG0:2^(k+1-z)+1<=2*gap0 w).
      { destruct (Nat.eq_dec z k) as [->|Hneq].
        - replace (k+1-k) with 1 by lia; cbn [Nat.pow]; lia.
        - assert (HT:2*2^(z+1)<=2^(k+1)).
          { change (2^(S (z+1))<=2^(k+1)).
            apply Nat.pow_le_mono_r; lia. }
          lia. }
      unfold guard; lia.
Qed.

Lemma entry k z : z<=k -> exists w,
  inc_steps (2^(z+1)-2) (repeat false (3*k+2)) w /\
  guard (2^(k+1-z)) (repeat true (2*z)++false::w).
Proof.
  intro Hz; destruct (zero2_gaps k) as [HG _].
  assert (HP:2<=2^(z+1)).
  { replace 2 with (2^1) by reflexivity; apply Nat.pow_le_mono_r; lia. }
  assert (HC:2^(z+1)<=2^(k+1)) by (apply Nat.pow_le_mono_r; lia).
  destruct (inc_steps_interior (2^(z+1)-2) (repeat false (3*k+2)) ltac:(lia))
    as [w [HS [HL HW]]].
  rewrite repeat_length in HL.
  destruct (inc_steps_markers_zero _ _ _ HS (plane_zeros _ _) (plane_zeros _ _))
    as [H0 H2].
  exists w; split; [exact HS|].
  apply strong; try assumption.
  pose proof (value_gap0 w) as HV.
  rewrite (width_length k 2 w ltac:(lia) HL) in HV.
  cbn [Nat.eqb] in HV; lia.
Qed.

Lemma entry_actual k z h : z<=k -> 2^z*(1+2*h)<=2^(k+1) -> exists w,
  inc_steps (2^(z+1)-2) (repeat false (3*k+2)) w /\
  guard (2*h) (repeat true (2*z)++false::w).
Proof.
  intros Hz HT; destruct (entry k z Hz) as [w [HS HG]].
  assert (HE:2^(k+1-z)*2^z=2^(k+1)).
  { rewrite <-Nat.pow_add_r; f_equal; lia. }
  assert (HP:0<2^z) by (pose proof (Nat.pow_nonzero 2 z ltac:(lia)); lia).
  exists w; split; [exact HS|].
  unfold guard in *; nia.
Qed.

End Pair3EntryGuard.

Module TM3.
Local Open Scope sym_scope.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RB---").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma RInc4 l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^n *> [0] *> r -->+
  l <* <[1;0] <{{D}} [0;0;0;0]^^n *> [1] *> r.
Proof. es. Qed.

Lemma LStart l r : l <* <[1;0] <{{D}} r -->+ l {{B}}> [1;1] *> r.
Proof. es. Qed.

Lemma R1001_bridge l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^n *> [1;0;0;1] *> r -->+
  l <* <[1;0] <* [1;1]^^(n*2) {{B}}> [1;1;1;1] *> r.
Proof. es' n & l r. Qed.

Module A3Words.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* The low ignored bit a may be zero; A3 first changes it to one and
   repeats the same Z test, rather than returning as A1/A2 would. *)
Lemma ZCarryMarked (a b:bool) l r :
  l <* [PairWord.bit a;1;1;1;PairWord.bit b;1] {{B}}> [1] *> r -->+
  l {{B}}> [1;1;1;1;1;1;1] *> r.
Proof. destruct a,b; cbn [PairWord.bit]; es. Qed.

Lemma ZInc w r : let '(v,e):=Pair3Word.inc w in
  PairWord.data w {{B}}> [1;1] *> r -->+
  PairWord.data v <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  revert w r; fix IH 1; intros w r.
  destruct w as [|a w].
  - cbn [Pair3Word.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es.
  - destruct w as [|b1 w].
    + destruct a; cbn [Pair3Word.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es.
    + destruct b1.
      * destruct w as [|b w].
        -- destruct a; cbn [Pair3Word.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es.
        -- cbn [Pair3Word.inc].
           destruct (Pair3Word.inc w) as [v e] eqn:E.
           eapply progress_trans.
           ++ applys_eq (ZCarryMarked a b (PairWord.data w) ([1] *> r));
                cbn [PairWord.data PairWord.pairs PairWord.bit]; destruct a,b; st; reflexivity.
           ++ eapply progress_trans.
              ** pose proof (IH w ([1;1;1;1;1;1] *> r)) as H.
                 rewrite E in H; cbn in H; applys_eq H; st; reflexivity.
              ** destruct e; cbn [PairWord.insert PairWord.data PairWord.pairs PairWord.bit]; es.
      * destruct a; cbn [Pair3Word.inc PairWord.data PairWord.pairs PairWord.bit PairWord.insert]; es.
Qed.

Lemma LIncWord w r : let '(v,e):=Pair3Word.inc w in
  PairWord.data w <* <[1;0] <{{D}} r -->+
  PairWord.data v <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  pose proof (ZInc w r) as H; destruct (Pair3Word.inc w) as [v e].
  eapply progress_trans; [apply LStart|exact H].
Qed.

Lemma RZero w r n : let '(v,e):=Pair3Word.inc w in
  PairWord.data w <* <[1;0] {{C}}> [1;0;0;0]^^n *> [0] *> r -->+
  PairWord.data v <* <[1;0] {{C}}>
  PairWord.insert e ([0;0;0;0]^^n *> [1] *> r).
Proof.
  pose proof (LIncWord w ([0;0;0;0]^^n *> [1] *> r)) as H.
  destruct (Pair3Word.inc w) as [v e].
  eapply progress_trans; [apply RInc4|exact H].
Qed.

Lemma REleven l r n :
  l <* <[1;0] {{C}}> [1;0;0;0]^^n *> [1;1] *> r -->+
  l <* <[1;0] <* [1;1]^^(n*2) <* <[1;0] {{C}}> r.
Proof. es' n & l r. Qed.

Lemma R1001 w r n :
  let '(v,e):=Pair3Word.inc (repeat true (2*n)++false::w) in
  PairWord.data w <* <[1;0] {{C}}> [1;0;0;0]^^n *> [1;0;0;1] *> r -->+
  PairWord.data (false::v) <* <[1;0] {{C}}> PairWord.insert e r.
Proof.
  pose proof (ZInc (repeat true (2*n)++false::w) ([1;1] *> r)) as H.
  destruct (Pair3Word.inc (repeat true (2*n)++false::w)) as [v e].
  eapply progress_trans.
  - exact (R1001_bridge (PairWord.data w) r n).
  - eapply progress_trans.
    + applys_eq H.
      rewrite Pair3Word.data_ones; cbn [PairWord.data PairWord.pairs PairWord.bit]; flia.
    + destruct e; cbn [PairWord.insert PairWord.data PairWord.pairs PairWord.bit]; es.
Qed.

Lemma init31 : c0 -[tm]->> 31 /
  PairWord.data [false;false] <* <[1;0] {{C}}> (0inf)%sym.
Proof.
  do 31 (eapply multistep_S;
    [first [eapply step_left; reflexivity | eapply step_right; reflexivity]|cbn]).
  cbn [PairWord.data PairWord.pairs PairWord.bit]; st; constructor.
Qed.

Lemma init : c0 -->+ PairWord.data [false;false] <* <[1;0] {{C}}> (0inf)%sym.
Proof. eapply multistep_progress; exact init31. Qed.
End A3Words.

Module A3Right.
Local Notation QR := C.
Import PairWord Pair12Right Pair3Guard.
Local Open Scope sym_scope.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma right_step w v e n r : Pair3Word.inc w=(v,e) -> RC d1 n r ->
  exists s, RC d1 (S n) s /\ C QR w r -->+ C QR v (insert e s).
Proof.
  intros E Hr; destruct (RC_carry _ _ _ Hr) as [k [s [-> Hs]]].
  exists (d0^^k *> d1 *> s); split; [exact Hs|].
  pose proof (A3Words.RZero w ([0;0;0] *> s) k) as H; rewrite E in H.
  applys_eq H; unfold C,d0,d1; st; reflexivity.
Qed.

Lemma finite_step w v n r tail k : Pair3Word.inc w=(v,false) ->
  FC d1 tail k n r -> S n<2^k -> exists s,
  FC d1 tail k (S n) s /\ C QR w r -->+ C QR v s.
Proof.
  intros E Hr Hb; destruct (FC_carry _ _ _ _ _ Hr Hb) as [j [s [_ [-> Hs]]]].
  exists (d0^^j *> d1 *> s); split; [exact Hs|].
  pose proof (A3Words.RZero w ([0;0;0] *> s) j) as H; rewrite E in H.
  applys_eq H; unfold C,insert,d0,d1; st; reflexivity.
Qed.

Lemma right_steps q w v n r : inc_steps q w v -> RC d1 n r ->
  exists s, RC d1 (n+q) s /\ C QR w r -->* C QR v s.
Proof.
  intro H; revert n r; induction H; intros n r Hr.
  - exists r; split; [now rewrite Nat.add_0_r|apply evstep_refl].
  - destruct (right_step _ _ _ _ _ H Hr) as [s [Hs HS]].
    destruct (IHinc_steps _ _ Hs) as [s' [Hs' HT]].
    exists s'; split; [applys_eq Hs'; flia|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.

Lemma finite_steps q w v n r tail k : inc_steps q w v ->
  FC d1 tail k n r -> n+q<2^k -> exists s,
  FC d1 tail k (n+q) s /\ C QR w r -->* C QR v s.
Proof.
  intro H; revert n r; induction H; intros n r Hr Hb.
  - exists r; split; [now rewrite Nat.add_0_r|apply evstep_refl].
  - destruct (finite_step _ _ _ _ _ _ H Hr ltac:(lia)) as [s [Hs HS]].
    destruct (IHinc_steps _ _ Hs ltac:(lia)) as [s' [Hs' HT]].
    exists s'; split; [applys_eq Hs'; flia|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.

Lemma shifted_prefix n w v r : inc_steps (2^(1+n)-1) w v ->
  C QR w (d0^^n *> ds *> r) -->+
  C QR v (d1^^n *> [1;0;0;1] *> r).
Proof.
  intro H; pose proof (Nat.pow_nonzero 2 n) as HP.
  replace (2^(1+n)-1) with ((2^n-1)+S (2^n-1)) in H
    by (cbn [Nat.pow Nat.add]; lia).
  destruct (inc_steps_add_inv _ _ _ _ H) as [u [Hwu Huv]].
  inversion Huv as [|q u0 u1 v0 EI Hu1v]; subst.
  destruct (finite_steps _ _ _ _ _ _ _ Hwu
    (FC_zero d1 (ds *> r) n) ltac:(lia)) as [s [Hs HS]].
  assert (Es:s=d1^^n *> ds *> r).
  { eapply FC_full_unique; exact Hs. }
  subst s.
  destruct (finite_steps _ _ _ _ _ _ _ Hu1v
    (FC_zero d1 ([1;0;0;1] *> r) n) ltac:(lia)) as [s [Hs2 HT]].
  assert (Es:s=d1^^n *> [1;0;0;1] *> r).
  { eapply FC_full_unique; exact Hs2. }
  subst s.
  pose proof (A3Words.RZero u ([0;0;1] *> r) n) as HM; rewrite EI in HM.
  eapply evstep_progress_trans; [exact HS|].
  eapply progress_evstep_trans; [|exact HT].
  applys_eq HM; unfold C,ds,insert; st; reflexivity.
Qed.

Lemma one_cross z w v r : 1<=z -> inc_steps (2^z-1) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -->+
  C QR v (d0^^z *> [1;1;0;0;0] *> r).
Proof.
  intros Hz H; destruct z as [|t]; [lia|].
  assert (HP:2<=2^(S t)) by
    (cbn [Nat.pow]; pose proof (Nat.pow_nonzero 2 t); lia).
  replace (2^(S t)-1) with ((2^(S t)-2)+1) in H by lia.
  destruct (inc_steps_add_inv _ _ _ _ H) as [u [HW HU]].
  inversion HU as [|q u0 mid v0 EI Hlast]; subst.
  inversion Hlast; subst.
  destruct (finite_steps _ _ _ _ _ _ _ HW
    (PairOrdinary.FC_leading_one t r) ltac:(lia)) as [s [Hs HS]].
  assert (Es:s=d1^^(S t) *> [0] *> d1 *> r).
  { eapply FC_full_unique; applys_eq Hs; flia. }
  subst s.
  pose proof (A3Words.RZero u (d1 *> r) (S t)) as HC; rewrite EI in HC.
  eapply evstep_progress_trans; [exact HS|].
  applys_eq HC; unfold C,insert,d1; st; reflexivity.
Qed.

Lemma prefix z w v r : inc_steps (2^(z+1)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -->*
  C QR v (d1^^z *> [1;1;0;0;0] *> r).
Proof.
  intro H; destruct z as [|t].
  - cbn [Nat.pow] in H; inversion H; subst.
    unfold d1; apply evstep_refl.
  - pose proof (Nat.pow_nonzero 2 (S t)) as HP.
    replace (2^(S t+1)-2) with ((2^(S t)-1)+(2^(S t)-1)) in H
      by (rewrite Nat.pow_add_r; cbn [Nat.pow]; lia).
    destruct (inc_steps_add_inv _ _ _ _ H) as [u [HW HV]].
    destruct (finite_steps _ _ _ _ _ _ _ HV
      (FC_zero d1 ([1;1;0;0;0] *> r) (S t)) ltac:(lia)) as [s [Hs HS]].
    assert (Es:s=d1^^(S t) *> [1;1;0;0;0] *> r).
    { apply FC_full_unique; exact Hs. }
    subst s; follow100 (one_cross (S t) w u r ltac:(lia) HW); exact HS.
Qed.

Lemma eleven_word z w r :
  C QR w (d1^^z *> [1;1] *> r) -->+
  C QR (repeat true (2*z)++false::w) r.
Proof.
  unfold C; rewrite Pair3Word.data_ones.
  applys_eq (A3Words.REleven (data w) r z); unfold data; cbn [pairs bit]; flia.
Qed.

Lemma ordinary z w v r : inc_steps (2^(z+1)-2) w v ->
  C QR w ([1] *> d0^^z *> d1 *> r) -->+
  C QR (repeat true (2*z)++false::v) ([0;0;0] *> r).
Proof.
  intro H; eapply evstep_progress_trans; [apply prefix; exact H|].
  exact (eleven_word z v ([0;0;0] *> r)).
Qed.

(* This alias is purely a digit-alignment fact and contains no TM rule. *)
Definition RC_shift3 := PairOrdinary.RC_shift3.
End A3Right.

Module A3Entry.
Local Notation QR := C.
Import PairWord Pair12Right Pair3Guard Pair3EntryGuard.
Local Open Scope sym_scope.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma phase1_zero_gap k : gap0 (repeat false (3*k+1))=2^k.
Proof. rewrite gap0_zeros by lia; cbn [Nat.eqb]; now rewrite Nat.add_0_r. Qed.

(* Both partial high fragments finish with phase two, and insert one. *)
Lemma phase12 k p w x r : 1<=p -> p<=2 -> length w=3*k+p -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w) s /\
  C QR w r -->+ C QR (repeat false (3*k+2)) ([1] *> s).
Proof.
  intros Hp HP Hl Hr.
  destruct (first_capacity k p w HP Hl) as [u [HS [Hlen [Hgap HE]]]].
  destruct (A3Right.right_steps _ _ _ _ _ HS Hr) as [s1 [Hr1 HR1]].
  destruct p; [lia|].
  destruct (A3Right.right_step _ _ _ _ _ HE Hr1) as [s2 [Hr2 HR2]].
  exists s2; split.
  - pose proof (gap_bounds w) as HB; unfold guard in HB.
    applys_eq Hr2; flia.
  - eapply evstep_progress_trans; [exact HR1|exact HR2].
Qed.

Lemma phase0_extend k w x r : length w=3*k -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w) s /\
  C QR w r -->+ C QR (repeat false (3*k+1)) s.
Proof.
  intros Hl Hr.
  destruct (first_capacity k 0 w ltac:(lia) ltac:(lia))
    as [u [HS [Hlen [Hgap HE]]]].
  destruct (A3Right.right_steps _ _ _ _ _ HS Hr) as [s1 [Hr1 HR1]].
  destruct (A3Right.right_step _ _ _ _ _ HE Hr1) as [s2 [Hr2 HR2]].
  exists s2; split.
  - pose proof (gap_bounds w) as HB; unfold guard in HB.
    applys_eq Hr2; flia.
  - eapply evstep_progress_trans; [exact HR1|exact HR2].
Qed.

Lemma phase0 k w x r : length w=3*k -> RC d1 x r ->
  exists s, RC d1 (x+gap0 w+2^k) s /\
  C QR w r -->+ C QR (repeat false (3*k+2)) ([1] *> s).
Proof.
  intros Hl Hr; destruct (phase0_extend k w x r Hl Hr) as [s1 [Hr1 HS1]].
  destruct (phase12 k 1 (repeat false (3*k+1)) _ s1
    ltac:(lia) ltac:(lia) (repeat_length _ _) Hr1) as [s2 [Hr2 HS2]].
  rewrite phase1_zero_gap in Hr2.
  exists s2; split; [exact Hr2|].
  eapply progress_trans; [exact HS1|exact HS2].
Qed.
End A3Entry.

Module A3Region.
Definition Conf := Pair12Right.C (C:Q).
Import PairWord Pair12Right Pair3Guard.
Local Open Scope sym_scope.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Inductive Allowed : (Q*(side*sym*side))%type -> Prop :=
| Blank w : Allowed (Conf w (0inf)%sym)
| One w : Allowed (Conf (false::false::w) ([1] *> (0inf)%sym))
| Shifted w n r : 0<n -> RC ds n r -> guard (2*n) w -> Allowed (Conf w r).

Lemma last_signal n w b : exists c', Allowed c' /\
  Conf w (d1^^n *> [1;0;0;1] *> insert b (0inf)%sym) -->+ c'.
Proof.
  pose proof (A3Words.R1001 w (insert b (0inf)%sym) n) as HS.
  destruct (Pair3Word.inc (repeat true (2*n)++false::w)) as [v e] eqn:E.
  destruct (inc_head _ _ _ E) as [u ->].
  destruct b,e; cbn [insert] in HS.
  - exists (Conf (false::false::false::u) (0inf)%sym); split; [constructor|].
    eapply progress_trans; [exact HS|exact (A3Right.eleven_word 0 _ (0inf)%sym)].
  - exists (Conf (false::false::u) ([1] *> (0inf)%sym)); split; [constructor|exact HS].
  - exists (Conf (false::false::u) ([1] *> (0inf)%sym)); split; [constructor|exact HS].
  - exists (Conf (false::false::u) (0inf)%sym); split; [constructor|exact HS].
Qed.

Lemma last_shift n w b : 2^(1+n)<=gap0 w -> exists c', Allowed c' /\
  Conf w (d0^^n *> ds *> insert b (0inf)%sym) -->+ c'.
Proof.
  intro Hg; pose proof (Nat.pow_nonzero 2 (1+n)) as HP.
  destruct (inc_steps_interior (2^(1+n)-1) w ltac:(lia)) as [v [HV _]].
  destruct (last_signal n v b) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  eapply progress_trans; [apply A3Right.shifted_prefix; exact HV|exact HS].
Qed.

Lemma shifted_step n w r : 0<n -> RC ds n r -> guard (2*n) w ->
  exists c', Allowed c' /\ Conf w r -->+ c'.
Proof.
  intros Hn Hr HG.
  destruct (RC_positive_split _ _ _ Hr Hn)
    as [t [q [s [Er [Hs [En Hqn]]]]]].
  destruct q as [|q].
  - apply RC_zero_unique in Hs; subst s; rewrite Er.
    apply (last_shift t w false).
    unfold guard in HG; rewrite En in HG; cbn [Nat.pow Nat.add] in *; nia.
  - pose proof (Nat.pow_nonzero 2 t) as HP.
    assert (HQ:2^(1+t)-1<gap0 w).
    { unfold guard in HG; rewrite En in HG; cbn [Nat.pow Nat.add] in *; nia. }
    destruct (inc_steps_interior _ _ HQ) as [v [HV [HL HD]]].
    pose proof (inc_steps_mono _ _ _ HV) as HM.
    assert (HVg:guard (2*S q+2) v).
    { unfold guard in *; rewrite En in HG; cbn [Nat.pow Nat.add] in *; nia. }
    assert (HU:guard (2*S q+1) (repeat true (2*t)++false::v)).
    { apply guard_ones; [lia|apply guard_zero].
      eapply guard_mono; [exact HVg|lia]. }
    destruct (Pair3Word.inc (repeat true (2*t)++false::v)) as [u e] eqn:E.
    destruct (inc_guard (2*S q) _ _ _ ltac:(lia) HU E) as [He HU']; subst e.
    exists (Conf (false::u) s); split.
    + eapply Shifted with (n:=S q); [lia|exact Hs|now apply guard_zero].
    + rewrite Er; eapply progress_trans; [apply A3Right.shifted_prefix; exact HV|].
      pose proof (A3Words.R1001 v s t) as HS; rewrite E in HS; exact HS.
Qed.
End A3Region.

Module A3Closure.
Import PairWord Pair12Right Pair3Guard Pair3EntryGuard A3Region.
Local Open Scope sym_scope.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma RC_power a : RC d1 (2^a) (d0^^a *> d1 *> (0inf)%sym).
Proof.
  replace (2^a) with (2^a*1) by lia; apply RC_zeros.
  change (RC d1 (1+0*2) (d1 *> (0inf)%sym)); constructor; constructor.
Qed.

Lemma zero3_d0 n r : [0;0;0] *> d0^^n *> r=d0^^n *> [0;0;0] *> r.
Proof.
  induction n; [reflexivity|].
  cbn [lpow]; rewrite !Str_app_assoc.
  change (d0 *> [0;0;0] *> d0^^n *> r=d0 *> d0^^n *> [0;0;0] *> r).
  now rewrite IHn.
Qed.

Lemma exceptional k r : RC d1 (2^(k+1)) r -> exists c', Allowed c' /\
  Conf (repeat false (3*k+2)) ([1] *> r) -->+ c'.
Proof.
  intro Hr.
  assert (Er:r=d0^^(k+1) *> d1 *> (0inf)%sym)
    by (eapply RC_unique; [exact Hr|apply RC_power]).
  rewrite Er; destruct (zero2_gaps k) as [HG _].
  pose proof (Nat.pow_nonzero 2 (k+1)) as HP.
  destruct (inc_steps_interior (2^(k+1)-1)
    (repeat false (3*k+2)) ltac:(lia)) as [v [HV [HL HD]]].
  rewrite repeat_length in HL.
  assert (EI:Pair3Word.inc v=(repeat false (3*k+2),true)).
  { apply (overflow12 k 2 v); lia. }
  assert (HB:2^(1+k)<=gap0 (repeat false (3*k+3))).
  { rewrite (proj1 (zero3_gaps k)); replace (1+k) with (k+1) by lia; lia. }
  destruct (last_shift k (repeat false (3*k+3)) true HB) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  eapply progress_trans.
  - exact (A3Right.one_cross (k+1) _ v (0inf)%sym ltac:(lia) HV).
  - eapply progress_trans.
    + pose proof (A3Words.RZero v
        ([0;0;0] *> d0^^k *> [1;1] *> (0inf)%sym) 0) as HZ.
      rewrite EI in HZ; applys_eq HZ; unfold Conf,C,insert.
      replace (k+1) with (S k) by lia; cbn [lpow]; unfold d0; st; flia.
    + eapply progress_trans; [apply (A3Right.eleven_word 0)|].
      replace (3*k+3) with (S (3*k+2)) in HS by lia; cbn [repeat] in HS.
      applys_eq HS; rewrite zero3_d0; unfold ds,insert; st; reflexivity.
Qed.

Lemma post_first k T r : RC d1 T r -> 0<T -> T<=2^(k+1) ->
  exists c', Allowed c' /\ Conf (repeat false (3*k+2)) ([1] *> r) -->+ c'.
Proof.
  intros Hr HT HB; destruct (Nat.eq_dec T (2^(k+1))) as [->|HN].
  { now apply exceptional. }
  destruct (RC_positive_split _ _ _ Hr HT) as [z [h [s [Er [Hs [ET HH]]]]]].
  assert (Hz:z<=k).
  { destruct (Nat.le_gt_cases z k); [assumption|].
    assert (HP:2^(k+1)<=2^z) by (apply Nat.pow_le_mono_r; lia).
    nia. }
  destruct (entry_actual k z h Hz ltac:(nia)) as [w [HW HG]].
  exists (Conf (repeat true (2*z)++false::w) ([0;0;0] *> s)); split.
  - destruct h as [|h].
    + apply RC_zero_unique in Hs; subst s.
      applys_eq (Blank (repeat true (2*z)++false::w)); unfold Conf,C; st; reflexivity.
    + eapply Shifted with (n:=S h); [lia|now apply A3Right.RC_shift3|exact HG].
  - rewrite Er; exact (A3Right.ordinary z _ w s HW).
Qed.

Lemma RC_odd_inv h r : RC d1 (1+2*h) r -> exists s, RC d1 h s /\ r=d1 *> s.
Proof.
  intro HR; inversion HR as [|n s Hs|n s Hs]; subst; try lia.
  assert (n=h) by lia; subst n; exists s; split; [exact Hs|reflexivity].
Qed.

Lemma odd_entry k h r : RC d1 (1+2*h) r -> 2*h<=2^(k+1) ->
  exists c', Allowed c' /\ Conf (repeat false (3*k+2)) ([1] *> r) -->+ c'.
Proof.
  intros Hr HB; destruct (RC_odd_inv _ _ Hr) as [s [Hs ->]].
  exists (Conf (false::repeat false (3*k+2)) ([0;0;0] *> s)); split.
  - destruct h as [|h].
    + apply RC_zero_unique in Hs; subst s.
      applys_eq (Blank (false::repeat false (3*k+2))); unfold Conf,C; st; reflexivity.
    + eapply Shifted with (n:=S h); [lia|now apply A3Right.RC_shift3|].
      pose proof (zero3_gaps k) as HG.
      replace (3*k+3) with (S (3*k+2)) in HG by lia; cbn [repeat] in HG.
      unfold guard; replace (k+2) with (S (k+1)) in HG by lia; cbn [Nat.pow] in HG; lia.
  - exact (A3Right.eleven_word 0 _ ([0;0;0] *> s)).
Qed.
End A3Closure.

Import PairWord Pair12Right Pair3Guard Pair3EntryGuard A3Region.
Local Open Scope sym_scope.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma length_split (w:list bool) : exists k p, p<=2 /\ length w=3*k+p.
Proof.
  exists (length w/3),(length w mod 3).
  pose proof (Nat.div_mod (length w) 3 ltac:(lia)).
  pose proof (Nat.mod_upper_bound (length w) 3 ltac:(lia)); lia.
Qed.

Lemma capacity_bound k p w : p<=2 -> length w=3*k+p ->
  gap0 w<=2^(k+(if Nat.eqb p 2 then 1 else 0)).
Proof.
  intros HP HL; pose proof (value_gap0 w) as H.
  rewrite (width_length k p w HP HL) in H; lia.
Qed.

Lemma pow_twice k : 2^(k+1)=2*2^k.
Proof. rewrite Nat.pow_add_r; cbn [Nat.pow]; lia. Qed.

Lemma right_one : RC d1 1 ([1] *> (0inf)%sym).
Proof. applys_eq (RC_d1 d1 0 _ (RC_zero d1)); unfold d1; st; reflexivity. Qed.

Lemma blank_step w : exists c', Allowed c' /\ Conf w (0inf)%sym -->+ c'.
Proof.
  destruct (length_split w) as [k [p [HP HL]]].
  pose proof (capacity_bound k p w HP HL) as HB.
  pose proof (gap_bounds w) as HG; unfold guard in HG.
  destruct (Nat.eq_dec p 0) as [->|HN].
  - rewrite Nat.add_0_r in HL; cbn [Nat.eqb] in HB; rewrite Nat.add_0_r in HB.
    destruct (A3Entry.phase0 k w 0 _ HL (RC_zero d1)) as [s [HR HS]].
    destruct (A3Closure.post_first k _ s HR ltac:(lia)
      ltac:(rewrite pow_twice; lia)) as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
  - assert (HU:gap0 w<=2^(k+1)).
    { eapply Nat.le_trans; [exact HB|].
      apply Nat.pow_le_mono_r; [lia|destruct (Nat.eqb p 2); lia]. }
    destruct (A3Entry.phase12 k p w 0 _ ltac:(lia) HP HL (RC_zero d1))
      as [s [HR HS]].
    destruct (A3Closure.post_first k _ s HR ltac:(lia) ltac:(lia)) as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
Qed.

Lemma one_step u : exists c', Allowed c' /\
  Conf (false::false::u) ([1] *> (0inf)%sym) -->+ c'.
Proof.
  set (w:=false::false::u).
  set (a:=1+plane zero_bit 2 u).
  assert (EG:gap0 w=2*a).
  { unfold w,a,gap0; cbn [plane zero_bit]; lia. }
  destruct (length_split w) as [k [p [HP HL]]].
  pose proof (capacity_bound k p w HP HL) as HB.
  destruct (Nat.eq_dec p 0) as [->|HN].
  - rewrite Nat.add_0_r in HL; cbn [Nat.eqb] in HB; rewrite Nat.add_0_r in HB.
    assert (HK:1<=k) by (unfold w in HL; cbn [length] in HL; lia).
    destruct k as [|k]; [lia|].
    destruct (A3Entry.phase0 (S k) w 1 _ HL right_one) as [s [HR HS]].
    rewrite EG in HR.
    replace (1+2*a+2^(S k)) with (1+2*(a+2^k)) in HR by (cbn [Nat.pow]; lia).
    assert (HU:2*(a+2^k)<=2^(S k+1)).
    { rewrite pow_twice; cbn [Nat.pow] in HB |- *; lia. }
    destruct (A3Closure.odd_entry (S k) (a+2^k) s HR HU) as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
  - assert (HU:2*a<=2^(k+1)).
    { rewrite <-EG; eapply Nat.le_trans; [exact HB|].
      apply Nat.pow_le_mono_r; [lia|destruct (Nat.eqb p 2); lia]. }
    destruct (A3Entry.phase12 k p w 1 _ ltac:(lia) HP HL right_one) as [s [HR HS]].
    rewrite EG in HR.
    destruct (A3Closure.odd_entry k a s HR HU) as [c' [HA HT]].
    exists c'; split; [exact HA|eapply progress_trans; eassumption].
Qed.

Lemma step c : Allowed c -> exists c', Allowed c' /\ c -->+ c'.
Proof.
  intros [w|w|w n r Hn Hr Hg].
  - apply blank_step.
  - apply one_step.
  - apply (A3Region.shifted_step n w r); assumption.
Qed.

Lemma closed c : Allowed c -> ~halts tm c.
Proof. apply (progress_nonhalt tm Allowed c step). Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep; exact A3Words.init.
  - apply closed; constructor.
Qed.
End TM3.

(* A4/A5 shared half-counter model and machine proofs. *)
Notation ld0 := <[1;1;0;1;1;0].
Notation ld1 := <[1;1;1;1;1;0].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Definition Half (b:sym) := <[1;1;b].
Definition Opp (b:sym) := match b with S0 => S1 | S1 => S0 end.
Fixpoint Marked (bs:list sym) :=
  match bs with [] => [] | b::bs => Half b ++ Half 1 ++ Marked bs end.

(* Shared: Right/Pair45Right. *)
Module Pair45Right.
Open Scope nat_scope.

Inductive RC : nat -> side -> Prop :=
| RC_zero : RC 0 (0inf)%sym
| RC_d0 n r : RC n r -> RC (n*2) (rd0 *> r)
| RC_d1 n r : RC n r -> RC (1+n*2) (rd1 *> r).

Inductive FC (tail:side) : nat -> nat -> side -> Prop :=
| FC_nil : FC tail 0 0 tail
| FC_d0 k n r : FC tail k n r -> FC tail (S k) (n*2) (rd0 *> r)
| FC_d1 k n r : FC tail k n r -> FC tail (S k) (1+n*2) (rd1 *> r).

Lemma RC_zero_unique r : RC 0 r -> r=(0inf)%sym.
Proof.
  intro H; remember 0 as n eqn:E; induction H; try lia.
  - reflexivity.
  - assert (n=0) by lia; subst; rewrite IHRC by reflexivity; st; reflexivity.
Qed.

Lemma RC_unique n r s : RC n r -> RC n s -> r=s.
Proof.
  intro H; revert s; induction H; intros s Hs.
  { symmetry; now apply RC_zero_unique. }
  all: inversion Hs; subst; try lia.
  all: try (assert (n=0) by lia; subst;
    rewrite (RC_zero_unique _ H); st; reflexivity).
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma FC_unique tail k n r s : FC tail k n r -> FC tail k n s -> r=s.
Proof.
  intro H; revert s; induction H; intros s Hs;
    inversion Hs; subst; try lia; try reflexivity.
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma FC_bound tail k n r : FC tail k n r -> n<2^k.
Proof. intro H; induction H; cbn [Nat.pow]; lia. Qed.

Lemma FC_zero tail k : FC tail k 0 (rd0^^k *> tail).
Proof.
  induction k; cbn [lpow]; [constructor|].
  rewrite Str_app_assoc; change (FC tail (S k) (0*2) (rd0 *> rd0^^k *> tail)).
  now constructor.
Qed.

Lemma FC_full tail k : FC tail k (2^k-1) (rd1^^k *> tail).
Proof.
  induction k; cbn [lpow Nat.pow]; [constructor|].
  rewrite Str_app_assoc.
  replace (2*2^k-1) with (1+(2^k-1)*2)
    by (pose proof (Nat.pow_nonzero 2 k); lia).
  now constructor.
Qed.

Lemma FC_full_unique tail k r : FC tail k (2^k-1) r -> r=rd1^^k *> tail.
Proof. intro H; eapply FC_unique; [exact H|apply FC_full]. Qed.

Lemma FC_RC tail k n r m : FC tail k n r -> RC m tail -> RC (n+2^k*m) r.
Proof.
  intros H Hr; induction H; cbn [Nat.pow] in *.
  - replace (0+1*m) with m by lia; exact Hr.
  - replace (n*2+2*2^k*m) with ((n+2^k*m)*2) by nia.
    now constructor.
  - replace (1+n*2+2*2^k*m) with (1+(n+2^k*m)*2) by nia.
    now constructor.
Qed.

Lemma RC_zeros n r k : RC n r -> RC (2^k*n) (rd0^^k *> r).
Proof.
  intro Hr; pose proof (FC_RC r k 0 (rd0^^k *> r) n (FC_zero r k) Hr).
  exact H.
Qed.

(* Carry decomposition also supplies existence without choosing a bitlength. *)
Lemma RC_carry n r : RC n r -> exists k s,
  r=rd1^^k *> rd0 *> s /\ RC (S n) (rd0^^k *> rd1 *> s).
Proof.
  intro H; induction H.
  - exists 0,(0inf)%sym; split; [st; reflexivity|].
    change (RC (1+0*2) (rd1 *> (0inf)%sym)); constructor; constructor.
  - exists 0,r; split; [reflexivity|].
    change (RC (1+n*2) (rd1 *> r)); now constructor.
  - destruct IHRC as [k [s [Er Hr]]]; exists (S k),s.
    split; cbn [lpow]; rewrite Str_app_assoc.
    + now rewrite Er.
    + replace (S (1+n*2)) with (S n*2) by lia; now constructor.
Qed.

Lemma RC_positive_split n r : RC n r -> 0<n -> exists t q s,
  r=rd0^^t *> rd1 *> s /\ RC q s /\ n=2^t*(1+q*2) /\ q<n.
Proof.
  intro H; induction H; intro Hn; [lia| |].
  - assert (Hpos:0<n) by lia.
    destruct (IHRC Hpos) as [t [q [s [Er [Hs [En Hq]]]]]].
    exists (S t),q,s; split.
    + cbn [lpow]; rewrite Str_app_assoc; now rewrite Er.
    + split; [exact Hs|]; split; [cbn [Nat.pow]; nia|lia].
  - exists 0,n,r; split; [reflexivity|].
    split; [exact H|]; split; [cbn; lia|lia].
Qed.

Lemma FC_carry tail k n r : FC tail k n r -> S n<2^k -> exists j s,
  j<k /\ r=rd1^^j *> rd0 *> s /\ FC tail k (S n) (rd0^^j *> rd1 *> s).
Proof.
  intro H; induction H; intro Hb.
  - cbn in Hb; lia.
  - exists 0,r; split; [lia|]; split; [reflexivity|].
    change (FC tail (S k) (1+n*2) (rd1 *> r)); now constructor.
  - assert (Hn:S n<2^k) by (cbn [Nat.pow] in Hb; lia).
    destruct (IHFC Hn) as [j [s [Hj [Er Hr]]]]; exists (S j),s.
    split; [lia|]; split; cbn [lpow]; rewrite Str_app_assoc.
    + now rewrite Er.
    + replace (S (1+n*2)) with (S n*2) by lia; now constructor.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis scan : forall l r k,
  l {{QR}}> rd1^^k *> rd0 *> r -[tm]->+
  l <{{QL}} rd0^^k *> rd1 *> r.

Lemma RInc_ex n r : RC n r -> exists s, RC (S n) s /\
  forall l, l {{QR}}> r -[tm]->+ l <{{QL}} s.
Proof.
  intro H; destruct (RC_carry _ _ H) as [k [s [-> Hs]]].
  exists (rd0^^k *> rd1 *> s); split; [exact Hs|intro l; apply scan].
Qed.

Lemma FiniteRInc_ex tail k n r : FC tail k n r -> S n<2^k ->
  exists s, FC tail k (S n) s /\
  forall l, l {{QR}}> r -[tm]->+ l <{{QL}} s.
Proof.
  intros Hr Hb; destruct (FC_carry _ _ _ _ Hr Hb) as [j [s [_ [-> Hs]]]].
  exists (rd0^^j *> rd1 *> s); split; [exact Hs|intro l; apply scan].
Qed.

End Semantics.
End Pair45Right.

(* Shared: Model/HalfCounter. *)
Module HalfCounter.
(* Lists are nearest-head first; true is A=110 and false is B=111. *)
Definition digit (b:bool) := Half (if b then 0 else 1).
Fixpoint tape (w:list bool) :=
  match w with [] => [] | b::w => digit b ++ tape w end.

Inductive Num : nat -> nat -> nat -> list bool -> Prop :=
| Nnil : Num 0 0 0 []
| NA n e o w : Num n e o w -> Num (1+n) (1+o*2) e (true::w)
| NB n e o w : Num n e o w -> Num (1+n) (o*2) e (false::w).

Lemma Num_length n e o w : Num n e o w -> length w=n.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma Num_bounds n e o w : Num n e o w ->
  e<2^((n+1)/2) /\ o<2^(n/2).
Proof.
  intro H; induction H.
  - cbn; lia.
  - replace ((1+n+1)/2) with (1+n/2) by lia.
    replace ((1+n)/2) with ((n+1)/2) by lia.
    cbn [Nat.pow Nat.add]; lia.
  - replace ((1+n+1)/2) with (1+n/2) by lia.
    replace ((1+n)/2) with ((n+1)/2) by lia.
    cbn [Nat.pow Nat.add]; lia.
Qed.

(* E0 consumes a borrow and returns before the leading A of the result.
   This relation deliberately forgets the exact cleared-marker OR mask. *)
Inductive Borrow : list bool -> list bool -> Prop :=
| Bstop b w : Borrow (b::true::w) (false::w)
| Bcarry b w w' : Borrow w w' ->
    Borrow (b::false::w) (true::true::w').

Lemma Borrow_num w w' : Borrow w w' -> forall n e o,
  Num n e (1+o) w -> exists e',
  Num n e' o (true::w') /\ e<=e'.
Proof.
  intro B; induction B; intros n e o H.
  - destruct b; inversion H as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst;
      inversion H0 as [|n1 e1 o1 w1 H1|]; subst.
    all: eexists; split; [applys_eq (NA _ _ _ _ (NB _ _ _ _ H1)); flia|lia].
  - destruct b; inversion H as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst;
      inversion H0 as [ | |n1 e1 o1 w1 H1]; subst;
      replace o1 with (1+(o1-1)) in H1 by lia;
      destruct (IHB _ _ _ H1) as [e' [H' Le]].
    all: eexists; split; [applys_eq (NA _ _ _ _ (NA _ _ _ _ H')); flia|lia].
Qed.

Lemma Borrow_ex n e o w : Num n e (1+o) w -> exists w', Borrow w w'.
Proof.
  gen e o w. induction n using lt_wf_ind; intros e o w Hn.
  inversion Hn as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst; try lia;
    inversion H0 as [|n1 e1 o1 w1 H1|n1 e1 o1 w1 H1]; subst; try lia.
  all: try (eexists; apply Bstop).
  all: replace o1 with (1+(o1-1)) in H1 by lia.
  all: destruct (H n1 ltac:(lia) _ _ _ H1) as [w' Bw].
  all: exists (true::true::w'); apply Bcarry; exact Bw.
Qed.

Section Semantics.
Variable tm : TM.
Hypothesis ECarry : forall l r b,
  l <* Half 1 <* Half b <{{E}} [0] *> r -[tm]->+
  l <{{E}} [0] *> [1]^^6 *> r.
Hypothesis EStop : forall l r b,
  l <* Half 0 <* Half b <{{E}} [0] *> r -[tm]->+
  l <* Half 1 <* <[1;1;0;1] {{D}}> r.
Hypothesis SOnes : forall l r n,
  l <* <[1;1;0;1] {{D}}> [1]^^(n*6) *> r -[tm]->*
  l <* ld0^^n <* <[1;1;0;1] {{D}}> r.

Lemma Borrow_spec w w' : Borrow w w' -> forall l r,
  l <* tape w <{{E}} [0] *> r -[tm]->+
  l <* tape w' <* <[1;1;0;1] {{D}}> r.
Proof.
  intro B; induction B; intros l r; cbn [tape]; st.
  - destruct b; apply EStop.
  - follow10 (ECarry (l <* tape w) r (if b then 0 else 1)).
    follow100 (IHB l ([1]^^6 *> r)).
    follow (SOnes (l <* tape w') r 1); finish.
Qed.

Variables QL QR : Q.
Hypothesis LStop : forall l r,
  l <* ld0 <{{QL}} r -[tm]->+ l <* ld1 {{QR}}> r.
Hypothesis LCarry : forall l r,
  l <* Half 1 <* Half 0 <{{QL}} r -[tm]->+
  l <{{E}} [0] *> [1]^^5 *> r.
Hypothesis SFive : forall l r,
  l <* <[1;1;0;1] {{D}}> [1]^^5 *> r -[tm]->+
  l <* Half 0 <* Half 0 <* Half 0 {{QR}}> r.

Lemma L_borrow_spec w w' : Borrow (true::w) w' -> forall l r,
  l <* tape (true::w) <{{QL}} r -[tm]->+
  l <* tape (true::w') {{QR}}> r.
Proof.
  intro B; inversion B as [b v|b v u Hv]; subst;
    intros l r; cbn [tape digit]; st.
  - apply LStop.
  - follow10 (LCarry (l <* tape v) r).
    follow100 (Borrow_spec _ _ Hv l ([1]^^5 *> r)).
    apply progress_evstep, SFive.
Qed.

Lemma LInc n e o w : Num n e (1+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\ forall l r,
  l <* tape (true::w) <{{QL}} r -[tm]->+
  l <* tape (true::w') {{QR}}> r.
Proof.
  intro H; destruct (Borrow_ex _ _ _ _ H) as [w' B].
  destruct (Borrow_num _ _ B _ _ _ H) as [e' [H' Le]].
  exists e',w'; repeat split; auto. now apply L_borrow_spec.
Qed.
End Semantics.

(* One induction handles both an infinite right counter and a protected
   finite prefix.  The chosen bound is only used to authorize right calls. *)
Section Batch.
Variables (tm:TM) (QL QR:Q).
Hypothesis LStep : forall n e o w, Num n e (1+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\ forall l r,
  l <* tape (true::w) <{{QL}} r -[tm]->+
  l <* tape (true::w') {{QR}}> r.

Section Counter.
Variable RC : nat -> side -> Prop.
Variable cap : nat.
Hypothesis RStep : forall z r, RC z r -> z<cap ->
  exists r', RC (1+z) r' /\ forall l,
  l {{QR}}> r -[tm]->+ l <{{QL}} r'.

Lemma Pairs q n e o w z r :
  Num n e (q+o) (true::w) -> RC z r -> z+q<=cap ->
  exists e' w' r', Num n e' o (true::w') /\ e<=e' /\ RC (z+q) r' /\
  forall l, l <* tape (true::w) <{{QL}} r -[tm]->*
    l <* tape (true::w') <{{QL}} r'.
Proof.
  gen n e o w z r; induction q; intros n e o w z r Hn Hr Hb.
  - exists e,w,r; replace (z+0) with z by lia.
    repeat split; auto.
  - destruct (LStep _ _ _ _ Hn) as [e1 [w1 [Hn1 [Le1 HL]]]].
    destruct (RStep _ _ Hr ltac:(lia)) as [r1 [Hr1 HR]].
    destruct (IHq _ _ _ _ _ _ Hn1 Hr1 ltac:(lia))
      as [e2 [w2 [r2 [Hn2 [Le2 [Hr2 HS]]]]]].
    exists e2,w2,r2; repeat split; try assumption; try lia.
    + applys_eq Hr2; flia.
    + intro l. follow100 (HL l r).
      follow100 (HR (l <* tape (true::w1))).
      apply HS.
Qed.
End Counter.

Hypothesis RScan : forall l r k,
  l {{QR}}> rd1^^k *> rd0 *> r -[tm]->+
  l <{{QL}} rd0^^k *> rd1 *> r.

Lemma RC_pairs q n e o w z r :
  Num n e (q+o) (true::w) -> Pair45Right.RC z r ->
  exists e' w' r', Num n e' o (true::w') /\ e<=e' /\
  Pair45Right.RC (z+q) r' /\ forall l,
  l <* tape (true::w) <{{QL}} r -[tm]->*
  l <* tape (true::w') <{{QL}} r'.
Proof.
  intros Hn Hr; eapply (Pairs Pair45Right.RC (z+q)); try eassumption; try lia.
  intros a s Hs _; eapply Pair45Right.RInc_ex; eauto.
Qed.

Lemma FC_pairs tail k q n e o w z r :
  Num n e (q+o) (true::w) -> Pair45Right.FC tail k z r -> z+q<2^k ->
  exists e' w' r', Num n e' o (true::w') /\ e<=e' /\
  Pair45Right.FC tail k (z+q) r' /\ forall l,
  l <* tape (true::w) <{{QL}} r -[tm]->*
  l <* tape (true::w') <{{QL}} r'.
Proof.
  intros Hn Hr Hb; eapply (Pairs (Pair45Right.FC tail k) (2^k-1));
    try eassumption; try lia.
  intros a s Hs Ha; eapply Pair45Right.FiniteRInc_ex; eauto; lia.
Qed.

Hypothesis TEntry : forall l r h,
  l <* Half 0 <* (Half 1)^^h <* <[1;1;1;1] {{D}}> rd0 *> r -[tm]->+
  l <* Half 0 <{{QL}} rd0^^(h+2) *> [1] *> r.
Hypothesis TExit : forall l r h,
  l {{QR}}> rd1^^(h+2) *> [1] *> r -[tm]->+
  l <* (Half 1)^^(h+1) <* <[1;1;1;1] {{D}}> r.

Lemma TZero n e o w h l r : Num n e (2^(h+2)+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <* (Half 1)^^h <* <[1;1;1;1] {{D}}> rd0 *> r -[tm]->+
  l <* tape (true::w') <* (Half 1)^^(h+1) <* <[1;1;1;1] {{D}}> r.
Proof.
  intro Hn.
  (* A protected prefix has exactly 2^(h+2)-1 successful right returns.
     The final left call then exits through its all-one prefix. *)
  assert (Hp:0<2^(h+2)) by (pose proof (Nat.pow_nonzero 2 (h+2)); lia).
  replace (2^(h+2)+o) with ((2^(h+2)-1)+(1+o)) in Hn by lia.
  destruct (FC_pairs ([1] *> r) (h+2) (2^(h+2)-1) _ _ _ _ 0 _ Hn
    (Pair45Right.FC_zero ([1] *> r) (h+2)) ltac:(lia))
    as [e1 [w1 [r1 [H1 [Le1 [Hr1 HS]]]]]].
  destruct (LStep _ _ _ _ H1) as [e2 [w2 [H2 [Le2 HL]]]].
  assert (Er:r1=rd1^^(h+2) *> [1] *> r)
    by (apply Pair45Right.FC_full_unique; exact Hr1).
  subst r1. exists e2,w2; repeat split; try assumption; try lia.
  cbn [tape digit]; st.
  follow10 (TEntry (l <* tape w) r h).
  follow (HS l).
  follow100 (HL l (rd1^^(h+2) *> [1] *> r)).
  follow100 (TExit (l <* tape (true::w2)) r h); finish.
  rewrite lpow_add; cbn [tape digit Half]; st; reflexivity.
Qed.
End Batch.
End HalfCounter.

(* Shared: Normal/HalfNormal. *)
Module HalfNormal.
Import HalfCounter.

Inductive Normal : nat -> nat -> list bool -> Prop :=
| Normal_nil : Normal 0 0 []
| Normal_one n k w : Normal n k w ->
    Normal (S n) (1+2*k) (true::true::w)
| Normal_zero n k w : Normal n k w ->
    Normal (S n) (2*k) (true::false::w).

Lemma pow2_pos n : 0<2^n.
Proof. pose proof (Nat.pow_nonzero 2 n ltac:(lia)); lia. Qed.

Lemma normal_num n k w : Normal n k w -> Num (2*n) (2^n-1) k w.
Proof.
  intro H; induction H.
  - exact Nnil.
  - pose proof (pow2_pos n).
    applys_eq (NA _ _ _ _ (NA _ _ _ _ IHNormal)); cbn [Nat.pow]; flia.
  - pose proof (pow2_pos n).
    applys_eq (NA _ _ _ _ (NB _ _ _ _ IHNormal)); cbn [Nat.pow]; flia.
Qed.

Lemma normal_bound n k w : Normal n k w -> k<2^n.
Proof. intro H; induction H; cbn [Nat.pow]; lia. Qed.

Lemma normal_length n k w : Normal n k w -> length w=2*n.
Proof. intro H; apply (Num_length _ _ _ _ (normal_num _ _ _ H)). Qed.

Lemma normal_head n k w : Normal n k w -> n>0 -> exists v, w=true::v.
Proof. intros H Hp; destruct H; [lia|eauto|eauto]. Qed.

Lemma num_normal n k w : Num (2*n) (2^n-1) k w -> Normal n k w.
Proof.
  gen k w; induction n; intros k w H.
  - pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w; [inversion H; constructor|cbn in Hl; lia].
  - pose proof (Num_length _ _ _ _ H) as Hl.
    pose proof (pow2_pos n) as Hp.
    destruct w as [|b [|c w]]; cbn in Hl; try lia.
    cbn [Nat.pow] in H.
    destruct b,c;
      inversion H as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst;
      inversion H0 as [|n1 e1 o1 w1 H1|n1 e1 o1 w1 H1]; subst; try lia.
    all: assert (o0=2^n-1) by lia; subst o0.
    all: assert (n1=2*n) by lia; subst n1.
    + applys_eq (Normal_one _ _ _ (IHn _ _ H1)); flia.
    + applys_eq (Normal_zero _ _ _ (IHn _ _ H1)); flia.
Qed.

Lemma normal_full_tape n k w : Normal n k w -> k=2^n-1 -> tape w=ld0^^n.
Proof.
  intro H; induction H; intro Hk.
  - reflexivity.
  - pose proof (pow2_pos n).
    assert (Hfull:k=2^n-1) by (cbn [Nat.pow] in Hk; lia).
    cbn [tape digit]; rewrite (IHNormal Hfull); reflexivity.
  - pose proof (pow2_pos n); cbn [Nat.pow] in Hk; lia.
Qed.

Lemma normal_zero_tape n k w : Normal n k w -> k=0%nat -> tape w=ld1^^n.
Proof.
  intro H; induction H; intro Hk; [reflexivity|lia|].
  assert (Hzero:k=0%nat) by lia.
  cbn [tape digit]; rewrite (IHNormal Hzero); reflexivity.
Qed.

Lemma normal_full n : Normal n (2^n-1) (repeat true (2*n)).
Proof.
  induction n; [constructor|].
  pose proof (pow2_pos n).
  replace (2*S n) with (2+2*n) by lia; cbn [repeat].
  applys_eq (Normal_one _ _ _ IHn); cbn [Nat.pow]; flia.
Qed.

Lemma normal_zero n : exists w, Normal n 0 w.
Proof.
  induction n as [|n [w Hw]].
  - exists ([]:list bool); constructor.
  - exists (true::false::w); applys_eq (Normal_zero _ _ _ Hw); flia.
Qed.

Lemma tape_app u v : tape (u++v)=tape u++tape v.
Proof. induction u; cbn [tape app]; [reflexivity|now rewrite IHu, app_assoc]. Qed.

Lemma tape_A_prefix m w : tape (repeat true m++w)=(Half 0)^^m++tape w.
Proof. induction m; cbn [repeat app tape digit lpow]; [reflexivity|now rewrite IHm]. Qed.

Lemma Num_AA n e o w m : Num n e o w ->
  Num (n+2*m) ((e+1)*2^m-1) ((o+1)*2^m-1) (repeat true (2*m)++w).
Proof.
  intro H; induction m.
  - cbn [Nat.pow repeat app]; applys_eq H; flia.
  - pose proof (pow2_pos m).
    replace (2*S m) with (2+2*m) by lia; cbn [repeat app].
    applys_eq (NA _ _ _ _ (NA _ _ _ _ IHm)); cbn [Nat.pow]; nia.
Qed.

Lemma Num_Aodd n e o w m : Num n e o w ->
  Num (n+2*m+1) ((o+1)*2^(m+1)-1) ((e+1)*2^m-1)
    (repeat true (2*m+1)++w).
Proof.
  intro H; pose proof (pow2_pos m).
  pose proof (Num_AA _ _ _ _ m H) as HH.
  replace (2*m+1) with (1+2*m) by lia; cbn [repeat app].
  applys_eq (NA _ _ _ _ HH); rewrite ?Nat.pow_add_r; cbn [Nat.pow]; nia.
Qed.

Section Increment.
Variables (tm:TM) (QL QR:Q).
Hypothesis LStep : forall n e o w, Num n e (1+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\ forall l r,
  l <* tape (true::w) <{{QL}} r -[tm]->+
  l <* tape (true::w') {{QR}}> r.

Lemma normal_LInc n k w : Normal n (1+k) w ->
  exists w', Normal n k w' /\ forall l r,
  l <* tape w <{{QL}} r -[tm]->+ l <* tape w' {{QR}}> r.
Proof.
  intro H; pose proof (normal_bound _ _ _ H) as Hb.
  assert (0<n) by (destruct n; cbn in Hb; lia).
  destruct (normal_head _ _ _ H H0) as [v ->].
  destruct (LStep _ _ _ _ (normal_num _ _ _ H)) as [e' [v' [HN [He HS]]]].
  exists (true::v'); split; [|exact HS].
  destruct (Num_bounds _ _ _ _ HN) as [Hmax _].
  replace ((2*n+1)/2) with n in Hmax by lia.
  assert (e'=2^n-1) by lia; subst e'.
  now apply num_normal.
Qed.
End Increment.
End HalfNormal.

(* Shared: ZeroNum/HalfZero. *)
Module HalfZero.
Import HalfCounter.

Lemma zero_pair n e b c w : Num (2+n) e 0 (b::c::w) ->
  c=false /\ exists e', Num n e' 0 w.
Proof.
  intro H; destruct b,c;
    inversion H as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst;
    inversion H0 as [|n1 e1 o1 w1 H1|n1 e1 o1 w1 H1]; subst; try lia.
  all: split; [reflexivity|eexists; applys_eq H1; flia].
Qed.

Lemma zero_even m e w : Num (2*m) e 0 w ->
  exists bs, length bs=m /\ tape w=Marked bs.
Proof.
  gen e w; induction m; intros e w H.
  - pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w; [exists ([]:list sym); auto|cbn in Hl; lia].
  - pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w as [|b [|c w]]; cbn in Hl; try lia.
    replace (2*S m) with (2+2*m) in H by lia.
    destruct (zero_pair _ _ _ _ _ H) as [-> [e' Hw]].
    destruct (IHm _ _ Hw) as [bs [Hb Et]].
    exists ((if b then 0 else 1)::bs); split; [cbn; lia|].
    cbn [tape digit Marked]; now rewrite Et.
Qed.

Lemma zero_odd m e w : Num (2*m+1) e 0 w ->
  exists bs b, length bs=m /\ tape w=Marked bs++Half b.
Proof.
  gen e w; induction m; intros e w H.
  - pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w as [|b [|c w]]; cbn in Hl; try lia.
    exists ([]:list sym),(if b then 0 else 1); split; [reflexivity|].
    cbn [tape digit Marked]; now rewrite app_nil_r.
  - pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w as [|b [|c w]]; cbn in Hl; try lia.
    replace (2*S m+1) with (2+(2*m+1)) in H by lia.
    destruct (zero_pair _ _ _ _ _ H) as [-> [e' Hw]].
    destruct (IHm _ _ Hw) as [bs [d [Hb Et]]].
    exists ((if b then 0 else 1)::bs),d; split; [cbn; lia|].
    cbn [tape digit Marked]; rewrite Et; now rewrite app_assoc.
Qed.

Lemma zero_even_A m e w : Num (2*m) e 0 (true::w) ->
  exists bs, length bs+1=m /\
    tape (true::w)=Half 0++Half 1++Marked bs.
Proof.
  intro H; destruct m.
  { pose proof (Num_length _ _ _ _ H); cbn in *; lia. }
  destruct w as [|c w].
  { pose proof (Num_length _ _ _ _ H); cbn in *; lia. }
  replace (2*S m) with (2+2*m) in H by lia.
  destruct (zero_pair _ _ _ _ _ H) as [-> [e' Hw]].
  destruct (zero_even _ _ _ Hw) as [bs [Hb Et]].
  exists bs; split; [lia|cbn [tape digit]; now rewrite Et].
Qed.

Lemma zero_odd_A m e w : Num (2*m+1) e 0 (true::w) ->
  (m=0%nat /\ w=[]) \/ exists bs b, length bs+1=m /\
    tape (true::w)=Half 0++Half 1++Marked bs++Half b.
Proof.
  intro H; destruct m.
  - left; split; [reflexivity|].
    pose proof (Num_length _ _ _ _ H) as Hl.
    destruct w; [reflexivity|cbn in Hl; lia].
  - destruct w as [|c w].
    { pose proof (Num_length _ _ _ _ H); cbn in *; lia. }
    replace (2*S m+1) with (2+(2*m+1)) in H by lia.
    destruct (zero_pair _ _ _ _ _ H) as [-> [e' Hw]].
    destruct (zero_odd _ _ _ Hw) as [bs [b [Hb Et]]].
    right; exists bs,b; split; [lia|cbn [tape digit]; now rewrite Et].
Qed.
End HalfZero.

(* Shared: ZeroNum/HalfDrain. *)
Module HalfDrain.
Import HalfCounter Pair45Right.
Local Open Scope sym_scope.

Lemma RC_tail n r : RC n r -> exists (b:sym) s,
  RC (n/2) s /\ r=([b;0;0])%sym *> s.
Proof.
  intro H; destruct H.
  - exists 0,0inf; split; [constructor|st; reflexivity].
  - exists 0,r; split; [applys_eq H; flia|reflexivity].
  - exists 1,r; split; [applys_eq H; flia|reflexivity].
Qed.

Lemma S_even_bound m e o w : Num (2*(1+m)) e o w ->
  2*((2+e)/2)+1<=2^(2+m)-1.
Proof.
  intro H; destruct (Num_bounds _ _ _ _ H) as [He _].
  replace ((2*(1+m)+1)/2) with (1+m) in He by lia.
  cbn [Nat.pow Nat.add] in *; pose proof (Nat.pow_nonzero 2 m); lia.
Qed.

Lemma S_odd_bound m e o w : Num (2*m+1) e o w ->
  2+e<=2^(1+m)+1.
Proof.
  intro H; destruct (Num_bounds _ _ _ _ H) as [He _].
  replace ((2*m+1+1)/2) with (1+m) in He by lia; lia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis run : forall q n e o w z r,
  Num n e (q+o) (true::w) -> RC z r ->
  exists e' w' r', Num n e' o (true::w') /\ e<=e' /\ RC (z+q) r' /\
  forall l, l <* tape (true::w) <{{QL}} r -[tm]->*
    l <* tape (true::w') <{{QL}} r'.
Hypothesis zero_even : forall m e w r, Num (2*m) e 0 (true::w) ->
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^m {{QR}}> [1] *> r.
Hypothesis zero_odd : forall m e w r, Num (2*m+1) e 0 (true::w) ->
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^m <* Half 0 {{QR}}> [1;1] *> r.
Hypothesis R11Bit : forall l r b,
  l {{QR}}> [1;1;b;0;0] *> r -[tm]->+
  l <* Half 0 <{{QL}} [1;0] *> r.

Lemma even m e o w z r : Num (2*m) e o (true::w) -> RC z r ->
  exists r', RC (z+o) r' /\
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^m {{QR}}> [1] *> r'.
Proof.
  intros Hn Hr; replace o with (o+0) in Hn by lia.
  destruct (run o _ _ _ _ _ _ Hn Hr)
    as [e' [w' [r' [Hn' [_ [Hr' HS]]]]]].
  exists r'; split; [exact Hr'|].
  follow (HS ldh); eapply zero_even; eauto.
Qed.

Lemma odd m e o w z r : Num (2*m+1) e o (true::w) -> RC z r ->
  exists r', RC ((z+o)/2) r' /\
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'.
Proof.
  intros Hn Hr; replace o with (o+0) in Hn by lia.
  destruct (run o _ _ _ _ _ _ Hn Hr)
    as [e' [w' [s [Hn' [_ [Hs HS]]]]]].
  destruct (RC_tail _ _ Hs) as [b [r' [Hr' ->]]].
  exists r'; split; [exact Hr'|].
  follow (HS ldh).
  follow10 (zero_odd _ _ _ ([b;0;0] *> r') Hn').
  follow100 (R11Bit (ldh <* ld0^^m <* Half 0) r' b); finish.
Qed.

Hypothesis SZeroEntry : forall l r,
  l <* <[1;1;0;1] {{D}}> rd0 *> r -[tm]->+
  l <* Half 0 <{{QL}} [0;0;0;1] *> r.

Lemma S_even m e o w : Num (2*m) e o w ->
  exists r', RC ((2+e)/2) r' /\
  ldh <* tape w <* <[1;1;0;1] {{D}}> 0inf -[tm]->+
  ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'.
Proof.
  intro Hn.
  assert (Hn':Num (2*m+1) (1+o*2) e (true::w))
    by (applys_eq (NA _ _ _ _ Hn); flia).
  destruct (odd _ _ _ _ 2 _ Hn'
    (RC_d0 1 _ (RC_d1 0 _ RC_zero))) as [r' [Hr HS]].
  exists r'; split; [exact Hr|].
  eapply progress_trans.
  - applys_eq (SZeroEntry (ldh <* tape w) 0inf); st; reflexivity.
  - applys_eq HS; cbn [tape digit]; st; reflexivity.
Qed.

Lemma S_odd m e o w : Num (2*m+1) e o w ->
  exists r', RC (2+e) r' /\
  ldh <* tape w <* <[1;1;0;1] {{D}}> 0inf -[tm]->+
  ldh <* ld0^^(1+m) {{QR}}> [1] *> r'.
Proof.
  intro Hn.
  assert (Hn':Num (2*(1+m)) (1+o*2) e (true::w))
    by (applys_eq (NA _ _ _ _ Hn); flia).
  destruct (even _ _ _ _ 2 _ Hn'
    (RC_d0 1 _ (RC_d1 0 _ RC_zero))) as [r' [Hr HS]].
  exists r'; split; [exact Hr|].
  eapply progress_trans.
  - applys_eq (SZeroEntry (ldh <* tape w) 0inf); st; reflexivity.
  - applys_eq HS; cbn [tape digit]; st; reflexivity.
Qed.
End Semantics.
End HalfDrain.

(* Shared: STNum/HalfST. *)
Module HalfST.
Import HalfCounter.

Lemma S000_borrow n e o b v : Num n (2+e) o (b::v) ->
  exists e' u, Borrow v u /\
    Num (n+1) e' e (true::b::true::u) /\ 2*o+1<=e'.
Proof.
  intro H; destruct b;
    inversion H as [|n0 e0 o0 w0 H0|n0 e0 o0 w0 H0]; subst;
    replace o0 with (1+(o0-1)) in H0 by lia;
    destruct (Borrow_ex _ _ _ _ H0) as [u B];
    destruct (Borrow_num _ _ B _ _ _ H0) as [e' [HN Le]].
  all: exists (1+e'*2),u; split; [exact B|]; split.
  - applys_eq (NA _ _ _ _ (NA _ _ _ _ HN)); flia.
  - lia.
  - applys_eq (NA _ _ _ _ (NB _ _ _ _ HN)); flia.
  - lia.
Qed.

Section Semantics.
Variable tm : TM.
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Hypothesis BorrowSem : forall w w', Borrow w w' -> forall l r,
  l <* tape w <{{E}} [0] *> r -[tm]->+
  l <* tape w' |s> r.
Hypothesis SOne : forall l r, l |s> rd1 *> r -[tm]->+
  l <* Half 1 |s> r.
Hypothesis TOne : forall l r, l |t> rd1 *> r -[tm]->+
  l <{{E}} [0] *> [1]^^6 *> r.
Hypothesis SZero : forall l r b, l <* Half b |s> rd0 *> r -[tm]->+
  l <{{E}} [0] *> [1]^^5 *> [Opp b;0;0;1] *> r.
Hypothesis SZeroEnd : forall l r b,
  l |s> [1]^^5 *> [Opp b;0;0;1] *> r -[tm]->+
  l <* Half 0 <* Half b <* Half 0 |t> r.
Hypothesis SOnes : forall l r k, l |s> [1]^^(k*6) *> r -[tm]->*
  l <* ld0^^k |s> r.

Lemma S100 n e o w : Num n e o w ->
  Num (n+1) (2*o) e (false::w) /\ forall l r,
  l <* tape w |s> rd1 *> r -[tm]->+
  l <* tape (false::w) |s> r.
Proof.
  intro H; split; [applys_eq (NB _ _ _ _ H); flia|].
  intros l r; cbn [tape digit]; st; apply SOne.
Qed.

Lemma T100 n e o w : Num n e (1+o) w -> exists e' w',
  Num (n+1) (1+2*o) e' (true::w') /\ e<=e' /\ forall l r,
  l <* tape w |t> rd1 *> r -[tm]->+
  l <* tape (true::w') |s> r.
Proof.
  intro H; destruct (Borrow_ex _ _ _ _ H) as [u B].
  destruct (Borrow_num _ _ B _ _ _ H) as [e' [HN Le]].
  exists e',(true::u); split; [applys_eq (NA _ _ _ _ HN); flia|].
  split; [exact Le|intros l r].
  follow10 (TOne (l <* tape w) r).
  follow100 (BorrowSem _ _ B l ([1]^^6 *> r)).
  follow (SOnes (l <* tape u) r 1); finish.
Qed.

Lemma S000 n e o w : Num n (2+e) o w -> exists e' w',
  Num (n+1) e' e (true::w') /\ 2*o+1<=e' /\ forall l r,
  l <* tape w |s> rd0 *> r -[tm]->+
  l <* tape (true::w') |t> r.
Proof.
  intro H; destruct w as [|b v]; [inversion H; lia|].
  destruct (S000_borrow _ _ _ _ _ H) as [e' [u [B [HN Le]]]].
  exists e',(b::true::u); split; [exact HN|]; split; [exact Le|intros l r].
  cbn [tape digit]; st.
  follow10 (SZero (l <* tape v) r (if b then 0 else 1)).
  follow100 (BorrowSem _ _ B l
    ([1]^^5 *> [Opp (if b then 0 else 1);0;0;1] *> r)).
  apply progress_evstep, SZeroEnd.
Qed.
End Semantics.
End HalfST.

(* Shared: STClosure/STClosure. *)
Module STClosure.
Import HalfCounter Pair45Right.
Local Open Scope sym_scope.

Definition SC (w:list bool) (r:side) :=
  ldh <* tape w <* <[1;1;0;1] {{D}}> r.
Definition TC (w:list bool) h (r:side) :=
  ldh <* tape (true::w) <* (Half 1)^^h <* <[1;1;1;1] {{D}}> r.

Lemma tape_B h w : tape (repeat false h++w)=(Half 1)^^h++tape w.
Proof.
  induction h; cbn [repeat app tape digit lpow]; [reflexivity|].
  rewrite IHh; now rewrite app_assoc.
Qed.

Lemma TC_word w h r : TC w h r=
  ldh <* tape (repeat false h++true::w) <* <[1;1;1;1] {{D}}> r.
Proof. unfold TC; rewrite tape_B; st; reflexivity. Qed.

Lemma Num_B_lower h n e o w k : Num n e o w -> k<=e -> k<=o ->
  exists E O, Num (n+h) E O (repeat false h++w) /\ k<=E /\ k<=O.
Proof.
  intros Hn He Ho; induction h.
  - exists e,o; split; [applys_eq Hn; flia|auto].
  - destruct IHh as [E [O [HN [HE HO]]]].
    exists (O*2),E; split.
    + cbn [repeat app]; applys_eq (NB _ _ _ _ HN); flia.
    + lia.
Qed.

Lemma Num_positive_O n e o w : Num n e o w -> 0<o -> 2<=n.
Proof.
  intros Hn Ho; destruct (Num_bounds _ _ _ _ Hn) as [_ Hb].
  destruct n as [|[|n]]; cbn in Hb; lia.
Qed.

Lemma cap_succ h : 2^(h+1+2)=2*2^(h+2).
Proof. replace (h+1+2) with (S (h+2)) by lia; reflexivity. Qed.

Inductive Allowed : nat -> (Q*(side*sym*side))%type -> Prop :=
| AllowedS n e o w z r :
    Num n e o w -> 2<=n -> 2*z<=e -> z<=o -> RC z r ->
    Allowed z (SC w r)
| AllowedT n e o w h z r :
    Num n e o (true::w) -> 2<=n -> 0<z ->
    2^(h+2)*z+1<=e -> 2^(h+2)*(z-1)+2<=o -> RC z r ->
    Allowed z (TC w h r).

(* The explicit length guard of AllowedT follows from its original budget. *)
Lemma zero_shape c : Allowed 0 c -> exists n e o w,
  Num n e o w /\ 2<=n /\ c=SC w (0inf)%sym.
Proof.
  intro H; inversion H; subst; try lia.
  match goal with Hr:RC 0 ?r |- _ =>
    apply RC_zero_unique in Hr; subst r end.
  match goal with Hn:Num ?n ?e ?o ?w |- _ => exists n,e,o,w end.
  split; [assumption|]; split; [assumption|reflexivity].
Qed.

Section Semantics.
Variable tm : TM.
Hypothesis SOne : forall n e o w, Num n e o w ->
  Num (n+1) (2*o) e (false::w) /\ forall l r,
  l <* tape w <* <[1;1;0;1] {{D}}> rd1 *> r -[tm]->+
  l <* tape (false::w) <* <[1;1;0;1] {{D}}> r.
Hypothesis TOne : forall n e o w, Num n e (1+o) w -> exists e' w',
  Num (n+1) (1+2*o) e' (true::w') /\ e<=e' /\ forall l r,
  l <* tape w <* <[1;1;1;1] {{D}}> rd1 *> r -[tm]->+
  l <* tape (true::w') <* <[1;1;0;1] {{D}}> r.
Hypothesis SZero : forall n e o w, Num n (2+e) o w -> exists e' w',
  Num (n+1) e' e (true::w') /\ 2*o+1<=e' /\ forall l r,
  l <* tape w <* <[1;1;0;1] {{D}}> rd0 *> r -[tm]->+
  l <* tape (true::w') <* <[1;1;1;1] {{D}}> r.
Hypothesis TZero : forall n e o w h l r,
  Num n e (2^(h+2)+o) (true::w) -> exists e' w',
  Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <* (Half 1)^^h <* <[1;1;1;1] {{D}}> rd0 *> r -[tm]->+
  l <* tape (true::w') <* (Half 1)^^(h+1) <* <[1;1;1;1] {{D}}> r.

Lemma positive_step z c : Allowed z c -> 0<z -> exists c',
  Allowed (z/2) c' /\ c -[tm]->+ c'.
Proof.
  intros H Hz; destruct H as
    [n e o w z r Hn Hl He Ho Hr|n e o w h z r Hn Hl Hpos He Ho Hr].
  - destruct Hr as [|q s Hrc|q s Hrc]; try lia.
    + replace (q*2/2) with q by lia.
      assert (Hp:0<q) by lia.
      replace e with (2+(e-2)) in Hn by lia.
      destruct (SZero _ _ _ _ Hn) as [e' [w' [HN [LE HS]]]].
      exists (TC w' 0 s); split.
      * eapply AllowedT; [exact HN|lia|lia|cbn; lia|cbn; lia|exact Hrc].
      * exact (HS ldh s).
    + replace ((1+q*2)/2) with q by lia.
      destruct (SOne _ _ _ _ Hn) as [HN HS].
      exists (SC (false::w) s); split.
      * eapply AllowedS; [exact HN|lia|lia|lia|exact Hrc].
      * exact (HS ldh s).
  - assert (HC:0<2^(h+2)) by (pose proof (Nat.pow_nonzero 2 (h+2)); lia).
    destruct Hr as [|q s Hrc|q s Hrc]; try lia.
    + replace (q*2/2) with q by lia.
      assert (Hp:0<q) by lia.
      assert (Hb:2^(h+2)<=o) by nia.
      replace o with (2^(h+2)+(o-2^(h+2))) in Hn by lia.
      destruct (TZero _ _ _ _ h ldh s Hn) as [e' [w' [HN [LE HS]]]].
      exists (TC w' (h+1) s); split.
      * eapply AllowedT; [exact HN|exact Hl|lia| | |exact Hrc].
        -- rewrite cap_succ; nia.
        -- rewrite cap_succ; nia.
      * exact HS.
    + replace ((1+q*2)/2) with q by lia.
      destruct (Num_B_lower h _ _ _ _ (q+1) Hn ltac:(nia) ltac:(nia))
        as [E [O [HN [HE HO]]]].
      replace O with (1+(O-1)) in HN by lia.
      destruct (TOne _ _ _ _ HN) as [e' [w' [HN' [LE HS]]]].
      exists (SC (true::w') s); split.
      * eapply AllowedS; [exact HN'|lia|lia|lia|exact Hrc].
      * rewrite TC_word; exact (HS ldh s).
Qed.

Lemma to_zero z c : Allowed z c -> exists c',
  Allowed 0 c' /\ c -[tm]->* c'.
Proof.
  gen c; induction z using lt_wf_ind; intros c HA.
  destruct (Nat.eq_dec z 0) as [->|Hz].
  - exists c; split; [exact HA|apply evstep_refl].
  - destruct (positive_step _ _ HA ltac:(lia)) as [c1 [HA1 HS]].
    destruct (H (z/2) ltac:(apply Nat.div_lt; lia) _ HA1) as [c2 [HA2 HT]].
    exists c2; split; [exact HA2|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.

End Semantics.
End STClosure.

(* Shared: TenNum/HalfTen. *)
Module HalfTen.
Import HalfCounter Pair45Right HalfNormal.
Local Open Scope sym_scope.

Lemma ten_prefix t r :
  [1;0] *> rd0^^(1+t) *> rd1 *> r =
  rd1 *> rd0^^t *> [0;0;1;0;0] *> r.
Proof. cbn [lpow Nat.add]; st; do 2 (rewrite lpow_rotate; cbn); reflexivity. Qed.

Lemma A_head k w : 0<k -> exists v, repeat true k++w=true::v.
Proof. intro H; destruct k; [lia|eexists; reflexivity]. Qed.

Lemma A_pairs k : (Half 0)^^(2*k)=ld0^^k.
Proof.
  induction k; [reflexivity|].
  replace (2*S k) with (2+2*k) by lia.
  rewrite lpow_add, IHk; reflexivity.
Qed.

Lemma flip_A n e o w : Num n e o (true::w) ->
  Num n (e-1) o (false::w) /\ 1<=e.
Proof.
  intro H; inversion H as [|n0 e0 o0 w0 H0|]; subst.
  split; [applys_eq (NB _ _ _ _ H0); flia|lia].
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis LStep : forall n e o w, Num n e (1+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\ forall l r,
  l <* tape (true::w) <{{QL}} r -[tm]->+
  l <* tape (true::w') {{QR}}> r.
Hypothesis RCarry : forall l r k,
  l {{QR}}> rd1^^k *> [0] *> r -[tm]->+
  l <{{QL}} rd0^^k *> [1] *> r.

Let scan l r k := RCarry l ([0;0] *> r) k.
Let pairs := FC_pairs tm QL QR LStep scan.

Lemma pre n e o w t l r : Num n e (2^(1+t)-1+o) (true::w) ->
  exists e' w', Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <{{QL}} [1;0] *> rd0^^t *> rd1 *> r -[tm]->+
  l <* tape (true::w') {{QR}}> rd1^^t *> [1;0;1;0;0] *> r.
Proof.
  intro Hn; destruct t as [|t].
  - destruct (LStep _ _ _ _ Hn) as [e' [w' [H' [Le HS]]]].
    exists e',w'; repeat split; auto.
  - assert (Hp:2<=2^(1+t)) by
      (cbn [Nat.pow Nat.add]; pose proof (Nat.pow_nonzero 2 t); lia).
    replace (2^(1+S t)-1+o) with
      ((2^(1+t)-2)+(2^(1+t)+o+1)) in Hn
      by (cbn [Nat.pow Nat.add]; lia).
    assert (Hr:FC ([0;0;1;0;0] *> r) (1+t) 1
      (rd1 *> rd0^^t *> [0;0;1;0;0] *> r))
      by (applys_eq (FC_d1 _ _ _ _ (FC_zero ([0;0;1;0;0] *> r) t)); flia).
    destruct (pairs _ _ (2^(1+t)-2) _ _ _ _ 1 _ Hn Hr ltac:(lia))
      as [e1 [w1 [r1 [H1 [Le1 [Hr1 HS1]]]]]].
    replace (2^(1+t)+o+1) with (1+(2^(1+t)+o)) in H1 by lia.
    destruct (LStep _ _ _ _ H1) as [e2 [w2 [H2 [Le2 HL2]]]].
    assert (Er1:r1=rd1^^(1+t) *> [0;0;1;0;0] *> r).
    { apply FC_full_unique; applys_eq Hr1; flia. }
    subst r1.
    replace (2^(1+t)+o) with ((2^(1+t)-1)+(1+o)) in H2 by lia.
    destruct (pairs ([1;0;1;0;0] *> r) (1+t) (2^(1+t)-1)
      _ _ _ _ 0 _ H2 (FC_zero _ _) ltac:(lia))
      as [e3 [w3 [r3 [H3 [Le3 [Hr3 HS3]]]]]].
    destruct (LStep _ _ _ _ H3) as [e4 [w4 [H4 [Le4 HL4]]]].
    assert (Er3:r3=rd1^^(1+t) *> [1;0;1;0;0] *> r)
      by (apply FC_full_unique; exact Hr3).
    subst r3; exists e4,w4; repeat split; try assumption; try lia.
    replace (S t) with (1+t) by lia; rewrite ten_prefix.
    follow (HS1 l).
    follow10 (HL2 l (rd1^^(1+t) *> [0;0;1;0;0] *> r)).
    follow100 (RCarry (l <* tape (true::w2)) ([0;1;0;0] *> r) (1+t)).
    follow (HS3 l); apply progress_evstep, HL4.
Qed.

Hypothesis EvenEntry : forall l r m,
  l <* <[0] {{QR}}> rd1^^(m*2) *> [1;0;1;0;0] *> r -[tm]->+
  l <* <[0] <{{QL}} [1]^^(m*6+3) *> [0;0] *> r.
Hypothesis OnesScan : forall l r k,
  l {{QR}}> [1]^^(k*3) *> r -[tm]->*
  l <* (Half 0)^^k {{QR}}> r.
Hypothesis OddEntry : forall l r m,
  l <* <[0] {{QR}}> rd1^^(m*2+1) *> [1;0;1] *> r -[tm]->+
  l <* <[1] <* ld0^^(m+1) {{QR}}> r.

Lemma even_exit n e o w m l r : Num n e (1+o) (true::w) ->
  exists n' e' o' v, Num n' e' o' (true::v) /\ n<=n' /\
  2*o+1<=e' /\ e<=o' /\
  l <* tape (true::w) {{QR}}> rd1^^(m*2) *> [1;0;1;0;0] *> r -[tm]->+
  l <* tape (true::v) <{{QL}} [1;0] *> r.
Proof.
  intro H; destruct (LStep _ _ _ _ H) as [e1 [w1 [H1 [Le HL]]]].
  pose proof (Num_Aodd _ _ _ _ m H1) as HN.
  destruct (A_head (2*m+1) (true::w1) ltac:(lia)) as [v Ev].
  pose proof (tape_A_prefix (2*m+1) (true::w1)) as Et.
  rewrite Ev in HN,Et.
  pose proof (pow2_pos m) as Hp.
  assert (Hp2:2<=2^(m+1)) by (rewrite Nat.pow_add_r; cbn; nia).
  exists (n+2*m+1),((o+1)*2^(m+1)-1),((e1+1)*2^m-1),v.
  split; [exact HN|]; split; [lia|]; split; [nia|]; split; [nia|].
  rewrite Et; repeat rewrite Str_app_assoc.
  follow10 (EvenEntry (l <* tape w <* <[1;1]) r m).
  follow100 (HL l ([1]^^(m*6+3) *> [0;0] *> r)).
  replace (m*6+3) with ((2*m+1)*3) by lia.
  follow (OnesScan (l <* tape (true::w1)) ([0;0] *> r) (2*m+1)).
  apply progress_evstep, (RCarry _ ([0] *> r) 0).
Qed.

Lemma odd_exit n e o w m l r : Num n e o (true::w) ->
  exists n' e' o' v, Num n' e' o' (true::v) /\ n<=n' /\
  2*e-1<=e' /\ 2*o+1<=o' /\
  l <* tape (true::w) {{QR}}> rd1^^(m*2+1) *> [1;0;1;0;0] *> r -[tm]->+
  l <* tape (true::v) <{{QL}} [1;0] *> r.
Proof.
  intro H; destruct (flip_A _ _ _ _ H) as [HF He].
  pose proof (Num_AA _ _ _ _ (m+1) HF) as HN.
  destruct (A_head (2*(m+1)) (false::w) ltac:(lia)) as [v Ev].
  pose proof (tape_A_prefix (2*(m+1)) (false::w)) as Et.
  rewrite Ev in HN,Et; rewrite A_pairs in Et.
  pose proof (pow2_pos m) as Hp.
  assert (Hp2:2<=2^(m+1)) by (rewrite Nat.pow_add_r; cbn; nia).
  exists (n+2*(m+1)),((e-1+1)*2^(m+1)-1),((o+1)*2^(m+1)-1),v.
  split; [exact HN|]; split; [lia|]; split; [nia|]; split; [nia|].
  rewrite Et; repeat rewrite Str_app_assoc.
  follow10 (OddEntry (l <* tape w <* <[1;1]) ([0;0] *> r) m).
  apply progress_evstep, (RCarry _ ([0] *> r) 0).
Qed.
End Semantics.
End HalfTen.

(* Shared: TenClosure/TenClosure. *)
Module TenClosure.
Import HalfCounter Pair45Right.
Local Open Scope sym_scope.

Definition JC (QL:Q) (w:list bool) (r:side) :=
  ldh <* tape (true::w) <{{QL}} [1;0] *> r.

Inductive Allowed (QL:Q) : nat -> (Q*(side*sym*side))%type -> Prop :=
| AllowedJ n e o w z r :
    Num n e o (true::w) -> 4<=n -> RC z r ->
    (z=0%nat \/ (2*z+1<=e /\ 2*z+1<=o)) ->
    Allowed QL z (JC QL w r).

Lemma zero_shape QL c : Allowed QL 0 c -> exists n e o w,
  Num n e o (true::w) /\ 4<=n /\ c=JC QL w (0inf)%sym.
Proof.
  intro H; inversion H; subst.
  match goal with Hr:RC 0 ?r |- _ => apply RC_zero_unique in Hr; subst r end.
  exists n,e,o,w; auto.
Qed.

Lemma reserve t q e o :
  2*(2^t*(1+q*2))+1<=e -> 2*(2^t*(1+q*2))+1<=o ->
  2^(1+t)-1<=o /\ 2*q+2<=o-(2^(1+t)-1) /\ 2*q+1<=e.
Proof.
  intros He Ho; pose proof (Nat.pow_nonzero 2 t).
  cbn [Nat.pow Nat.add]; nia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis pre : forall n e o w t l r,
  Num n e (2^(1+t)-1+o) (true::w) -> exists e' w',
  Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <{{QL}} [1;0] *> rd0^^t *> rd1 *> r -[tm]->+
  l <* tape (true::w') {{QR}}> rd1^^t *> [1;0;1;0;0] *> r.
Hypothesis even_exit : forall n e o w m l r,
  Num n e (1+o) (true::w) -> exists n' e' o' v,
  Num n' e' o' (true::v) /\ n<=n' /\ 2*o+1<=e' /\ e<=o' /\
  l <* tape (true::w) {{QR}}> rd1^^(m*2) *> [1;0;1;0;0] *> r -[tm]->+
  l <* tape (true::v) <{{QL}} [1;0] *> r.
Hypothesis odd_exit : forall n e o w m l r,
  Num n e o (true::w) -> exists n' e' o' v,
  Num n' e' o' (true::v) /\ n<=n' /\ 2*e-1<=e' /\ 2*o+1<=o' /\
  l <* tape (true::w) {{QR}}> rd1^^(m*2+1) *> [1;0;1;0;0] *> r -[tm]->+
  l <* tape (true::v) <{{QL}} [1;0] *> r.

Lemma positive_step z c : Allowed QL z c -> 0<z -> exists q c',
  q<z /\ Allowed QL q c' /\ c -[tm]->+ c'.
Proof.
  intros HA Hz; destruct HA as [n e o w z r Hn Hl Hr Hg].
  destruct Hg as [Hg|[He Ho]]; [lia|].
  destruct (RC_positive_split _ _ Hr Hz) as [t [q [s [-> [Hs [Ez Hq]]]]]].
  destruct (reserve t q e o ltac:(rewrite <-Ez; exact He)
    ltac:(rewrite <-Ez; exact Ho)) as [Hb [Hbq Heq]].
  set (b:=o-(2^(1+t)-1)) in *.
  replace o with (2^(1+t)-1+b) in Hn by (unfold b; lia).
  destruct (pre _ _ _ _ t ldh s Hn) as [e1 [w1 [H1 [Le1 HS1]]]].
  destruct (Nat.Even_or_Odd t) as [[m Hm]|[m Hm]].
  - assert (Et:t=m*2) by lia; subst t.
    replace b with (1+(b-1)) in H1 by lia.
    destruct (even_exit _ _ _ _ m ldh s H1)
      as [n2 [e2 [o2 [w2 [H2 [Hlen [HE [HO HS2]]]]]]]].
    exists q,(JC QL w2 s); split; [exact Hq|]; split.
    + eapply AllowedJ; [exact H2|lia|exact Hs|right; lia].
    + eapply progress_trans; [exact HS1|applys_eq HS2; flia].
  - assert (Et:t=m*2+1) by lia; subst t.
    destruct (odd_exit _ _ _ _ m ldh s H1)
      as [n2 [e2 [o2 [w2 [H2 [Hlen [HE [HO HS2]]]]]]]].
    exists q,(JC QL w2 s); split; [exact Hq|]; split.
    + eapply AllowedJ; [exact H2|lia|exact Hs|right; lia].
    + eapply progress_trans; [exact HS1|applys_eq HS2; flia].
Qed.

Lemma to_zero z c : Allowed QL z c -> exists c',
  Allowed QL 0 c' /\ c -[tm]->* c'.
Proof.
  gen c; induction z using lt_wf_ind; intros c HA.
  destruct (Nat.eq_dec z 0) as [->|Hz].
  - exists c; auto.
  - destruct (positive_step _ _ HA ltac:(lia)) as [q [c1 [Hq [HA1 HS]]]].
    destruct (H q Hq _ HA1) as [c2 [HA2 HT]].
    exists c2; split; [exact HA2|].
    eapply evstep_trans; [apply progress_evstep; exact HS|exact HT].
Qed.

End Semantics.
End TenClosure.

(* Shared: INum/HalfI. *)
Module HalfI.
Import HalfCounter HalfNormal Pair45Right.
Local Open Scope sym_scope.

Lemma FC_insert_one r t :
  FC ([0;1;0;0] *> r) (S t) 1 ([1] *> rd0^^(S t) *> rd1 *> r).
Proof.
  applys_eq (FC_d1 _ _ _ _ (FC_zero ([0;1;0;0] *> r) t)).
  st; simpl_rotate; reflexivity.
Qed.

Lemma normal_split n k w : Normal n k w -> 0<k ->
  exists v a u, Normal n (k-1) v /\
    tape w=ld1^^a++ld0++tape u /\ tape v=ld0^^a++ld1++tape u.
Proof.
  intro H; induction H; intro Hk; [lia| |].
  - exists (true::false::w),0%nat,w; split.
    + applys_eq (Normal_zero _ _ _ H); flia.
    + split; reflexivity.
  - destruct (IHNormal ltac:(lia)) as [v [a [u [Hv [Ew Ev]]]]].
    exists (true::true::v),(S a),u; split.
    + applys_eq (Normal_one _ _ _ Hv); flia.
    + split; cbn [tape digit]; [rewrite Ew|rewrite Ev]; reflexivity.
Qed.

Lemma normal_AA n k w m : Normal n k w ->
  Normal (n+m) ((k+1)*2^m-1) (repeat true (2*m)++w).
Proof.
  intro H; apply num_normal.
  pose proof (Num_AA _ _ _ _ m (normal_num _ _ _ H)) as HN.
  pose proof (pow2_pos n).
  applys_eq HN; rewrite ?Nat.pow_add_r; nia.
Qed.

Lemma Num_flip n e o w : Num n e o (true::w) ->
  Num n (e-1) o (false::w).
Proof.
  intro H; inversion H as [|n0 e0 o0 w0 H0|]; subst.
  applys_eq (NB _ _ _ _ H0); flia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis LStep : forall n k w, Normal n (1+k) w ->
  exists w', Normal n k w' /\ forall l r,
  l <* tape w <{{QL}} r -[tm]->+ l <* tape w' {{QR}}> r.
Hypothesis RCarry : forall l r k,
  l {{QR}}> rd1^^k *> [0] *> r -[tm]->+
  l <{{QL}} rd0^^k *> [1] *> r.

Lemma normal_FC_Rpairs tail h q n b w z r :
  Normal n (q+b) w -> FC tail h z r -> z+q<2^h ->
  exists w' r', Normal n b w' /\ FC tail h (z+q) r' /\ forall l,
  l <* tape w {{QR}}> r -[tm]->* l <* tape w' {{QR}}> r'.
Proof.
  gen n b w z r; induction q; intros n b w z r Hn Hr Hb.
  - exists w,r; replace (z+0) with z by lia; repeat split; auto.
  - assert (Hscan:forall l r k,
      l {{QR}}> rd1^^k *> rd0 *> r -[tm]->+
      l <{{QL}} rd0^^k *> rd1 *> r).
    { intros l s k; exact (RCarry l ([0;0] *> s) k). }
    destruct (FiniteRInc_ex tm QL QR Hscan _ _ _ _ Hr ltac:(lia))
      as [r1 [Hr1 HR]].
    replace (S q+b) with (1+(q+b)) in Hn by lia.
    destruct (LStep _ _ _ Hn) as [w1 [H1 HL]].
    destruct (IHq _ _ _ _ _ H1 Hr1 ltac:(lia)) as [w2 [r2 [H2 [Hr2 HS]]]].
    exists w2,r2; split; [exact H2|]; split.
    + applys_eq Hr2; flia.
    + intro l; follow100 (HR (l <* tape w)).
      follow100 (HL l r1); apply HS.
Qed.

Lemma pre n b w t l r : Normal n (2^(1+t)-2+b) w -> 1<=b ->
  exists w', Normal n b w' /\
  l <* tape w {{QR}}> [1] *> rd0^^t *> rd1 *> r -[tm]->*
  l <* tape w' {{QR}}> rd1^^t *> [1;1;0;0] *> r.
Proof.
  intros Hn Hb; destruct t as [|t].
  - exists w; split; [exact Hn|st; apply evstep_refl].
  - assert (Hp:2<=2^(S t)) by (cbn [Nat.pow]; pose proof (pow2_pos t); lia).
    replace (2^(1+S t)-2+b) with ((2^(S t)-2)+(2^(S t)+b)) in Hn
      by (rewrite Nat.pow_add_r; cbn [Nat.pow]; pose proof (pow2_pos t); nia).
    destruct (normal_FC_Rpairs ([0;1;0;0] *> r) (S t) (2^(S t)-2)
      _ _ _ 1 _ Hn (FC_insert_one r t) ltac:(lia))
      as [w1 [r1 [H1 [Hr1 HS1]]]].
    assert (Er1:r1=rd1^^(S t) *> [0;1;0;0] *> r).
    { apply FC_full_unique; applys_eq Hr1; flia. }
    subst r1.
    replace (2^(S t)+b) with (1+((2^(S t)-1)+b)) in H1 by lia.
    destruct (LStep _ _ _ H1) as [w2 [H2 HL]].
    destruct (normal_FC_Rpairs ([1;1;0;0] *> r) (S t) (2^(S t)-1)
      _ _ _ 0 _ H2 (FC_zero ([1;1;0;0] *> r) (S t)) ltac:(lia))
      as [w3 [r3 [H3 [Hr3 HS3]]]].
    assert (Er3:r3=rd1^^(S t) *> [1;1;0;0] *> r).
    { apply FC_full_unique; exact Hr3. }
    subst r3; exists w3; split; [exact H3|].
    follow (HS1 l).
    follow100 (RCarry (l <* tape w1) ([1;0;0] *> r) (S t)).
    follow100 (HL l (rd0^^(S t) *> [1;1;0;0] *> r)).
    apply HS3.
Qed.

Hypothesis OddRecover : forall l r a m,
  l <* ld0 <* ld1^^a {{QR}}> rd1^^(m*2+1) *> [1;1;0;0] *> r -[tm]->+
  l <* ld1 <* ld0^^(m+a+1) {{QR}}> [1] *> r.

Lemma odd_exit n b w m l r : Normal n b w -> 0<b ->
  exists w', Normal (n+m+1) (b*2^(m+1)-1) w' /\
  l <* tape w {{QR}}> rd1^^(m*2+1) *> [1;1;0;0] *> r -[tm]->+
  l <* tape w' {{QR}}> [1] *> r.
Proof.
  intros Hn Hb; destruct (normal_split _ _ _ Hn Hb) as [v [a [u [Hv [Ew Ev]]]]].
  exists (repeat true (2*(m+1))++v); split.
  - applys_eq (normal_AA _ _ _ (m+1) Hv); nia.
  - rewrite Ew, tape_app, (normal_full_tape _ _ _ (normal_full (m+1)) eq_refl), Ev.
    pose proof (OddRecover (l <* tape u) r a m) as HH.
    replace (m+a+1) with ((m+1)+a) in HH by lia.
    rewrite (lpow_add _ (m+1) a ld0) in HH; applys_eq HH; st; reflexivity.
Qed.

Lemma odd n b w m l r : Normal n (2^(1+(m*2+1))-2+b) w -> 1<=b ->
  exists w', Normal (n+m+1) (b*2^(m+1)-1) w' /\
  l <* tape w {{QR}}> [1] *> rd0^^(m*2+1) *> rd1 *> r -[tm]->+
  l <* tape w' {{QR}}> [1] *> r.
Proof.
  intros Hn Hb; destruct (pre _ _ _ _ l r Hn Hb) as [v [Hv HP]].
  destruct (odd_exit _ _ _ m l r Hv ltac:(lia)) as [u [Hu HU]].
  exists u; split; [exact Hu|follow HP; exact HU].
Qed.

Hypothesis EvenAux : forall l r m,
  l <* <[0] {{QR}}> rd1^^(m*2) *> [1;1;0;0] *> r -[tm]->+
  l <* <[1] <* ld0^^m <* <[1;1;0;1] {{D}}> r.

Lemma even_exit n b w m l r : Normal n b w -> 0<b ->
  exists w', Num (2*(n+m)) ((2^n-1)*2^m-1) ((b+1)*2^m-1) w' /\
  l <* tape w {{QR}}> rd1^^(m*2) *> [1;1;0;0] *> r -[tm]->+
  l <* tape w' <* <[1;1;0;1] {{D}}> r.
Proof.
  intros Hn Hb; pose proof (normal_bound _ _ _ Hn) as Hbound.
  assert (Hpos:0<n) by (destruct n; cbn in Hbound; lia).
  assert (Hpow:2<=2^n) by (destruct n; [lia|cbn [Nat.pow]; pose proof (pow2_pos n); lia]).
  destruct (normal_head _ _ _ Hn Hpos) as [v ->].
  exists (repeat true (2*m)++false::v); split.
  - pose proof (Num_AA _ _ _ _ m (Num_flip _ _ _ _ (normal_num _ _ _ Hn))) as HH.
    applys_eq HH; nia.
  - rewrite tape_app, (normal_full_tape _ _ _ (normal_full m) eq_refl).
    applys_eq (EvenAux (l <* tape v <* [1;1]) r m).
    cbn [tape digit Half]; st; reflexivity.
Qed.

Lemma even n b w m l r : Normal n (2^(1+m*2)-2+b) w -> 1<=b ->
  exists w', Num (2*(n+m)) ((2^n-1)*2^m-1) ((b+1)*2^m-1) w' /\
  l <* tape w {{QR}}> [1] *> rd0^^(m*2) *> rd1 *> r -[tm]->+
  l <* tape w' <* <[1;1;0;1] {{D}}> r.
Proof.
  intros Hn Hb; destruct (pre _ _ _ _ l r Hn Hb) as [v [Hv HP]].
  destruct (even_exit _ _ _ m l r Hv ltac:(lia)) as [u [Hu HU]].
  exists u; split; [exact Hu|follow HP; exact HU].
Qed.
End Semantics.
End HalfI.

(* Shared: TBoundary/HalfTBoundary. *)
Module HalfTBoundary.
Import HalfCounter HalfZero.
Local Open Scope sym_scope.
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Lemma geometric_step h k o :
  2^(h+2)*(2^(S k)-1)+o=
  2^(h+2)+(2^(h+1+2)*(2^k-1)+o).
Proof.
  pose proof (Nat.pow_nonzero 2 k ltac:(lia)).
  replace (h+1+2) with (S (h+2)) by lia.
  cbn [Nat.pow]; nia.
Qed.

Section Semantics.
Variable tm : TM.
Hypothesis TZero : forall n e o w h l r,
  Num n e (2^(h+2)+o) (true::w) -> exists e' w',
  Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <* (Half 1)^^h |t> rd0 *> r -[tm]->+
  l <* tape (true::w') <* (Half 1)^^(h+1) |t> r.

Lemma TZeros k n e o w h l r :
  Num n e (2^(h+2)*(2^k-1)+o) (true::w) -> exists e' w',
  Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <* (Half 1)^^h |t> rd0^^k *> r -[tm]->*
  l <* tape (true::w') <* (Half 1)^^(h+k) |t> r.
Proof.
  gen n e o w h l r; induction k; intros n e o w h l r Hn.
  - replace (2^(h+2)*(2^0-1)+o) with o in Hn by (cbn; lia).
    exists e,w; split; [exact Hn|]; split; [lia|].
    rewrite Nat.add_0_r; apply evstep_refl.
  - rewrite geometric_step in Hn.
    destruct (TZero _ _ _ _ h l (rd0^^k *> r) Hn)
      as [e1 [w1 [H1 [LE1 HS1]]]].
    destruct (IHk _ _ _ _ _ l r H1) as [e2 [w2 [H2 [LE2 HS2]]]].
    exists e2,w2; split; [exact H2|]; split; [lia|].
    replace (h+S k) with (h+1+k) by lia.
    cbn [lpow]; rewrite Str_app_assoc.
    follow100 HS1; exact HS2.
Qed.

Variable QR : Q.
Hypothesis TOne : forall l r, l |t> rd1 *> r -[tm]->+
  l <{{E}} [0] *> [1]^^6 *> r.
Hypothesis Carry : forall l r bs,
  l <* Marked bs <{{E}} [0] *> r -[tm]->*
  l <{{E}} [0] *> [1]^^(length bs*6) *> r.
Hypothesis EHalfBoundary : forall r b,
  ldh <* Half b <{{E}} [0] *> r -[tm]->+
  ldh {{QR}}> [1]^^6 *> r.
Hypothesis RScan : forall l r k,
  l {{QR}}> [1]^^(k*3) *> r -[tm]->*
  l <* (Half 0)^^k {{QR}}> r.

Lemma RPairs l r k : l {{QR}}> [1]^^(k*6) *> r -[tm]->*
  l <* ld0^^k {{QR}}> r.
Proof.
  replace (k*6) with ((k*2)*3) by lia.
  follow (RScan l r (k*2)); finish.
  unfold Half; st; reflexivity.
Qed.

Lemma T100_zero_odd m e w r : Num (2*m+1) e 0 w ->
  ldh <* tape w |t> rd1 *> r -[tm]->+
  ldh <* ld0^^(m+2) {{QR}}> r.
Proof.
  intro Hn; destruct (zero_odd _ _ _ Hn) as [bs [b [Hm Et]]].
  rewrite Et; repeat rewrite Str_app_assoc.
  follow10 (TOne (ldh <* Half b <* Marked bs) r).
  follow (Carry (ldh <* Half b) ([1]^^6 *> r) bs).
  follow100 (EHalfBoundary ([1]^^(length bs*6) *> [1]^^6 *> r) b).
  rewrite Hm.
  replace ([1]^^6 *> [1]^^(m*6) *> [1]^^6 *> r)
    with ([1]^^((m+2)*6) *> r).
  - apply RPairs.
  - replace ((m+2)*6) with (6+(m*6+6)) by lia.
    repeat rewrite lpow_add; repeat rewrite Str_app_assoc; reflexivity.
Qed.
End Semantics.
End HalfTBoundary.

(* Shared: Union/PairUnion. *)
Module PairUnion.
Import HalfCounter HalfNormal Pair45Right.
Local Open Scope sym_scope.

Definition IC (QR:Q) w r := ldh <* tape w {{QR}}> [1] *> r.
Definition IGuard n k z :=
  z=0%nat \/ (exists d, z<2^d /\ d<=n /\ 2^d-1<=k) \/
  (k=2^n-1 /\ z<=2^n+1).

Inductive IAllowed (QR:Q) : (Q*(side*sym*side))%type -> Prop :=
| IntroI n k w z r : Normal n k w -> 1<=n -> RC z r -> IGuard n k z ->
    IAllowed QR (IC QR w r).

Inductive Allowed (QL QR:Q) : (Q*(side*sym*side))%type -> Prop :=
| Ordinary c : IAllowed QR c -> Allowed QL QR c
| Ten z c : TenClosure.Allowed QL z c -> Allowed QL QR c
| Signal z c : STClosure.Allowed z c -> Allowed QL QR c.

Lemma I_full QR n z r : 1<=n -> z<=2^n+1 -> RC z r ->
  IAllowed QR (ldh <* ld0^^n {{QR}}> [1] *> r).
Proof.
  intros Hn Hz Hr.
  rewrite <- (normal_full_tape _ _ _ (normal_full n) eq_refl).
  eapply IntroI; [apply normal_full|exact Hn|exact Hr|].
  right; right; auto.
Qed.

Lemma J_full QL n z r : 2<=n -> RC z r ->
  (z=0%nat \/ 2*z+1<=2^n-1) ->
  TenClosure.Allowed QL z (ldh <* ld0^^n <{{QL}} [1;0] *> r).
Proof.
  intros Hn Hr Hg.
  destruct (normal_head _ _ _ (normal_full n) ltac:(lia)) as [w Ew].
  pose proof (normal_num _ _ _ (normal_full n)) as HN; rewrite Ew in HN.
  pose proof (normal_full_tape _ _ _ (normal_full n) eq_refl) as Et.
  rewrite Ew in Et; rewrite <-Et.
  eapply TenClosure.AllowedJ; [exact HN|lia|exact Hr|tauto].
Qed.

Lemma J_odd_bound m e o w : Num (2*(1+m)+1) e o w ->
  2*((1+o)/2)+1<=2^(2+m)-1.
Proof.
  intro H; destruct (Num_bounds _ _ _ _ H) as [_ Ho].
  replace ((2*(1+m)+1)/2) with (1+m) in Ho by lia.
  cbn [Nat.pow Nat.add] in *; pose proof (pow2_pos m); lia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis LEven : forall m e o w z r,
  Num (2*m) e o (true::w) -> RC z r -> exists r', RC (z+o) r' /\
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^m {{QR}}> [1] *> r'.
Hypothesis LOdd : forall m e o w z r,
  Num (2*m+1) e o (true::w) -> RC z r -> exists r', RC ((z+o)/2) r' /\
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'.
Hypothesis SEven : forall m e o w, Num (2*m) e o w ->
  exists r', RC ((2+e)/2) r' /\
  STClosure.SC w (0inf)%sym -[tm]->+
  ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'.
Hypothesis SOdd : forall m e o w, Num (2*m+1) e o w ->
  exists r', RC (2+e) r' /\
  STClosure.SC w (0inf)%sym -[tm]->+
  ldh <* ld0^^(1+m) {{QR}}> [1] *> r'.

Lemma S_zero c : STClosure.Allowed 0 c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.
Proof.
  intro H; destruct (STClosure.zero_shape _ H) as [n [e [o [w [HN [Hl ->]]]]]].
  destruct (Nat.Even_or_Odd n) as [[m Hm]|[m Hm]]; subst n.
  - destruct (SEven _ _ _ _ HN) as [r' [Hr HS]].
    exists (ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'); split; [|exact HS].
    apply (Ten _ _ ((2+e)/2)); apply J_full; [lia|exact Hr|right].
    assert (HB:2*((2+e)/2)+1<=2^(2+(m-1))-1).
    { apply (HalfDrain.S_even_bound (m-1) e o w); applys_eq HN; flia. }
    replace (2+(m-1)) with (1+m) in HB by lia; exact HB.
  - destruct (SOdd _ _ _ _ HN) as [r' [Hr HS]].
    exists (ldh <* ld0^^(1+m) {{QR}}> [1] *> r'); split; [|exact HS].
    apply Ordinary; eapply I_full; [lia|eapply HalfDrain.S_odd_bound; exact HN|exact Hr].
Qed.

Lemma J_zero c : TenClosure.Allowed QL 0 c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.
Proof.
  intro H; destruct (TenClosure.zero_shape _ _ H)
    as [n [e [o [w [HN [Hl ->]]]]]].
  destruct (Nat.Even_or_Odd n) as [[m Hm]|[m Hm]]; subst n.
  - destruct (LEven _ _ _ _ 1 _ HN (RC_d1 0 _ RC_zero)) as [r' [Hr HS]].
    exists (ldh <* ld0^^m {{QR}}> [1] *> r'); split.
    + apply Ordinary; eapply I_full; [lia| |exact Hr].
      destruct (Num_bounds _ _ _ _ HN) as [_ Ho].
      replace (2*m/2) with m in Ho by lia; lia.
    + applys_eq HS; unfold TenClosure.JC; st; reflexivity.
  - destruct (LOdd _ _ _ _ 1 _ HN (RC_d1 0 _ RC_zero)) as [r' [Hr HS]].
    exists (ldh <* ld0^^(1+m) <{{QL}} [1;0] *> r'); split.
    + apply (Ten _ _ ((1+o)/2)); apply J_full; [lia|exact Hr|right].
      assert (HB:2*((1+o)/2)+1<=2^(2+(m-1))-1).
      { apply (J_odd_bound (m-1) e o (true::w)); applys_eq HN; flia. }
      replace (2+(m-1)) with (1+m) in HB by lia; exact HB.
    + applys_eq HS; unfold TenClosure.JC; st; reflexivity.
Qed.
End Semantics.
End PairUnion.

(* Shared: Return/NormalReturn. *)
Module NormalReturn.
Import HalfCounter HalfNormal Pair45Right PairUnion.
Local Open Scope sym_scope.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis RScan : forall l r k,
  l {{QR}}> rd1^^k *> rd0 *> r -[tm]->+
  l <{{QL}} rd0^^k *> rd1 *> r.
Hypothesis LEven : forall m e o w z r,
  Num (2*m) e o (true::w) -> RC z r -> exists r', RC (z+o) r' /\
  ldh <* tape (true::w) <{{QL}} r -[tm]->+
  ldh <* ld0^^m {{QR}}> [1] *> r'.

Lemma even_R_return n e o w z r : Num (2*n) e o (true::w) ->
  1<=n -> RC z r -> z<=1 -> exists c', Allowed QL QR c' /\
  ldh <* tape (true::w) {{QR}}> r -[tm]->+ c'.
Proof.
  intros Hn Hlen Hr Hz; destruct (Num_bounds _ _ _ _ Hn) as [_ Hb].
  replace (2*n/2) with n in Hb by lia.
  destruct (RInc_ex tm QL QR RScan _ _ Hr) as [s [Hs HR]].
  destruct (LEven _ _ _ _ _ _ Hn Hs) as [s' [Hs' HL]].
  exists (ldh <* ld0^^n {{QR}}> [1] *> s'); split.
  - apply Ordinary; eapply I_full; [exact Hlen| |exact Hs']; lia.
  - eapply progress_trans; [apply HR|exact HL].
Qed.

Lemma R_return n k w z r : Normal n k w -> 1<=n -> RC z r -> z<=1 ->
  exists c', Allowed QL QR c' /\ ldh <* tape w {{QR}}> r -[tm]->+ c'.
Proof.
  intros Hn Hlen Hr Hz; destruct (normal_head _ _ _ Hn ltac:(lia)) as [v ->].
  eapply even_R_return; [exact (normal_num _ _ _ Hn)|eassumption..].
Qed.

Lemma R_zero_full n : 1<=n -> exists c', Allowed QL QR c' /\
  ldh <* ld0^^n {{QR}}> 0inf -[tm]->+ c'.
Proof.
  intro Hn; destruct (R_return _ _ _ _ _ (normal_full n) Hn RC_zero ltac:(lia))
    as [c' [HA HS]].
  rewrite (normal_full_tape _ _ _ (normal_full n) eq_refl) in HS.
  exists c'; auto.
Qed.

Lemma I_zero n k w r : Normal n k w -> 1<=n -> RC 0 r ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Proof.
  intros Hn Hl Hr; apply RC_zero_unique in Hr; subst r.
  destruct (R_return _ _ _ _ _ Hn Hl (RC_d1 0 _ RC_zero) ltac:(lia))
    as [c' [HA HS]].
  exists c'; split; [exact HA|].
  applys_eq HS; unfold IC; st; reflexivity.
Qed.
End Semantics.
End NormalReturn.

(* Shared: IClosure/IClosure. *)
Module IClosure.
Import HalfCounter HalfNormal Pair45Right PairUnion.
Local Open Scope sym_scope.

Lemma small_bounds n k d t q :
  2^t*(1+q*2)<2^d -> d<=n -> 2^d-1<=k ->
  exists b s, k=2^(1+t)-2+b /\ 1<=b /\ q<2^s /\ s<=n /\
    2^s<=b /\ 2*q+2<=2^n.
Proof.
  intros Hz Hd Hk.
  pose proof (pow2_pos t) as Hpt.
  assert (Htd:t<d).
  { apply (proj2 (Nat.pow_lt_mono_r_iff 2 t d ltac:(lia))); nia. }
  set (s:=d-(1+t)).
  assert (Hds:d=(1+t)+s) by (unfold s; lia).
  assert (HP:2^d=2^(1+t)*2^s) by (rewrite Hds, Nat.pow_add_r; reflexivity).
  assert (HP2:2^(1+t)=2*2^t) by reflexivity.
  pose proof (pow2_pos s) as Hps.
  pose proof (Nat.pow_le_mono_r 2 d n ltac:(lia) Hd) as Hdn.
  assert (Hcost:2^(1+t)-2<=k) by nia.
  set (b:=k-(2^(1+t)-2)).
  assert (Hb:k=2^(1+t)-2+b) by (unfold b; lia).
  assert (Hbnd:2^s<=b) by nia.
  exists b,s; repeat split; try assumption; try (unfold s; lia); nia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis IOdd : forall n b w m l r,
  Normal n (2^(1+(m*2+1))-2+b) w -> 1<=b ->
  exists w', Normal (n+m+1) (b*2^(m+1)-1) w' /\
  l <* tape w {{QR}}> [1] *> rd0^^(m*2+1) *> rd1 *> r -[tm]->+
  l <* tape w' {{QR}}> [1] *> r.
Hypothesis IEven : forall n b w m l r,
  Normal n (2^(1+m*2)-2+b) w -> 1<=b ->
  exists w', Num (2*(n+m)) ((2^n-1)*2^m-1) ((b+1)*2^m-1) w' /\
  l <* tape w {{QR}}> [1] *> rd0^^(m*2) *> rd1 *> r -[tm]->+
  l <* tape w' <* <[1;1;0;1] {{D}}> r.

Lemma small n k w z r d : Normal n k w -> 1<=n -> RC z r ->
  0<z -> z<2^d -> d<=n -> 2^d-1<=k ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Proof.
  intros Hn Hlen Hr Hz Hcap Hd Hbudget.
  destruct (RC_positive_split _ _ Hr Hz)
    as [t [q [s [Er [Hs [Ez Hqz]]]]]].
  destruct (small_bounds n k d t q ltac:(rewrite <-Ez; exact Hcap) Hd Hbudget)
    as [b [d' [Ek [Hb [Hq [Hwidth [Hbb H2q]]]]]]].
  destruct (Nat.Even_or_Odd t) as [[m Hm]|[m Hm]]; subst t;
    replace (2*m) with (m*2) in * by lia.
  - rewrite Ek in Hn.
    destruct (IEven _ _ _ m ldh s Hn Hb) as [w' [HN HS]].
    exists (STClosure.SC w' s); split.
    + apply (Signal QL QR q); eapply STClosure.AllowedS.
      * exact HN.
      * lia.
      * pose proof (pow2_pos m); nia.
      * pose proof (pow2_pos m); nia.
      * exact Hs.
    + unfold IC, STClosure.SC; rewrite Er; exact HS.
  - rewrite Ek in Hn.
    destruct (IOdd _ _ _ m ldh s Hn Hb) as [w' [HN HS]].
    exists (IC QR w' s); split.
    + apply Ordinary; eapply IntroI; [exact HN|lia|exact Hs|].
      right; left; exists d'; repeat split; try assumption; try lia.
      pose proof (pow2_pos (m+1)); nia.
    + unfold IC; rewrite Er; exact HS.
Qed.
End Semantics.
End IClosure.

(* Shared: Special/PairSpecial. *)
Module PairSpecial.
Import HalfCounter HalfNormal Pair45Right.
Local Open Scope sym_scope.

Lemma Num_BB n e o w m : Num n e o w ->
  Num (n+2*m) (e*2^m) (o*2^m) (repeat false (2*m)++w).
Proof.
  intro H; induction m.
  - cbn; applys_eq H; flia.
  - replace (2*S m) with (S (S (2*m))) by lia; cbn [repeat app].
    applys_eq (NB _ _ _ _ (NB _ _ _ _ IHm)); cbn [Nat.pow]; nia.
Qed.

Lemma Num_Bodd n e o w m : Num n e o w ->
  Num (n+2*m+1) (o*2^(m+1)) (e*2^m) (repeat false (2*m+1)++w).
Proof.
  intro H; replace (2*m+1) with (S (2*m)) by lia; cbn [repeat app].
  applys_eq (NB _ _ _ _ (Num_BB _ _ _ _ m H)).
  all: replace (m+1) with (S m) by lia; cbn [Nat.pow]; nia.
Qed.

Lemma Num_A_positive n e o w : Num n e o (true::w) -> 0<e.
Proof. intro H; inversion H; lia. Qed.

Lemma plus_one_tape k r : RC (2^(S k)+1) r ->
  r=rd1 *> rd0^^k *> rd1 *> (0inf)%sym.
Proof.
  intro H; apply (RC_unique _ _ _ H).
  pose proof (RC_d1 _ _ (RC_zeros _ _ k (RC_d1 0 _ RC_zero))) as HH.
  applys_eq HH; cbn [Nat.pow]; nia.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).
Hypothesis EvenAux : forall l r m,
  l <* <[0] {{QR}}> rd1^^(m*2) *> [1;1;0;0] *> r -[tm]->+
  l <* <[1] <* ld0^^m |s> r.
Hypothesis SOne : forall n e o w, Num n e o w ->
  Num (n+1) (2*o) e (false::w) /\ forall l r,
  l <* tape w |s> rd1 *> r -[tm]->+
  l <* tape (false::w) |s> r.
Hypothesis TOne : forall n e o w, Num n e (1+o) w -> exists e' w',
  Num (n+1) (1+2*o) e' (true::w') /\ e<=e' /\ forall l r,
  l <* tape w |t> rd1 *> r -[tm]->+
  l <* tape (true::w') |s> r.
Hypothesis SZero : forall n e o w, Num n (2+e) o w -> exists e' w',
  Num (n+1) e' e (true::w') /\ 2*o+1<=e' /\ forall l r,
  l <* tape w |s> rd0 *> r -[tm]->+
  l <* tape (true::w') |t> r.
Hypothesis TZeros : forall k n e o w h l r,
  Num n e (2^(h+2)*(2^k-1)+o) (true::w) -> exists e' w',
  Num n e' o (true::w') /\ e<=e' /\
  l <* tape (true::w) <* (Half 1)^^h |t> rd0^^k *> r -[tm]->*
  l <* tape (true::w') <* (Half 1)^^(h+k) |t> r.
Hypothesis TZeroOdd : forall m e w r, Num (2*m+1) e 0 w ->
  ldh <* tape w |t> rd1 *> r -[tm]->+
  ldh <* ld0^^(m+2) {{QR}}> r.

Lemma entry n r : 1<=n -> exists w,
  Num (2*n) (2^n-2) (2^n-1) w /\
  ldh <* ld0^^n {{QR}}> [1] *> rd1 *> r -[tm]->+ STClosure.SC w r.
Proof.
  intro Hn; assert (HP:2<=2^n).
  { destruct n; [lia|cbn [Nat.pow]; pose proof (pow2_pos n); lia]. }
  destruct (HalfI.even_exit tm QR EvenAux n (2^n-1)
    (repeat true (2*n)) 0 ldh r (normal_full n) ltac:(lia))
    as [w [HN HS]].
  exists w; split; [applys_eq HN; cbn [Nat.pow]; nia|].
  rewrite (normal_full_tape _ _ _ (normal_full n) eq_refl) in HS.
  exact HS.
Qed.

Lemma one r : RC (2^1+1) r -> exists c',
  PairUnion.Allowed QL QR c' /\
  ldh <* ld0^^1 {{QR}}> [1] *> r -[tm]->+ c'.
Proof.
  intro HR; rewrite (plus_one_tape 0 r HR).
  destruct (entry 1 (rd1 *> (0inf)%sym) ltac:(lia)) as [w [HN HS]].
  destruct (SOne _ _ _ _ HN) as [HN' HS'].
  exists (STClosure.SC (false::w) (0inf)%sym); split.
  - apply (PairUnion.Signal _ _ 0); eapply STClosure.AllowedS;
      [exact HN'|lia|lia|lia|apply RC_zero].
  - follow10 HS; apply progress_evstep; exact (HS' ldh (0inf)%sym).
Qed.

(* All n=k+2 first reach T1 with zero odd-plane budget and k near B's. *)
Lemma to_T_one k r : RC (2^(k+2)+1) r -> exists e w,
  Num (2*(k+2)+1) e 0 (true::w) /\
  ldh <* ld0^^(k+2) {{QR}}> [1] *> r -[tm]->+
  STClosure.TC w k (rd1 *> (0inf)%sym).
Proof.
  intro HR; replace (k+2) with (S (S k)) in HR by lia.
  rewrite (plus_one_tape (S k) r HR); cbn [lpow].
  rewrite Str_app_assoc.
  destruct (entry (k+2) (rd0 *> rd0^^k *> rd1 *> (0inf)%sym) ltac:(lia))
    as [v [HN HS]].
  assert (HP:2^(k+2)=4*2^k) by (rewrite Nat.pow_add_r; cbn; nia).
  pose proof (pow2_pos k).
  replace (2^(k+2)-2) with (2+(2^(k+2)-4)) in HN by nia.
  destruct (SZero _ _ _ _ HN) as [e1 [w1 [H1 [LE1 HS1]]]].
  replace (2^(k+2)-4) with (2^(0+2)*(2^k-1)+0) in H1 by (cbn; nia).
  destruct (TZeros k _ _ 0 _ 0 ldh (rd1 *> (0inf)%sym) H1)
    as [e2 [w2 [H2 [LE2 HS2]]]].
  exists e2,w2; split; [exact H2|].
  follow10 HS; follow100 (HS1 ldh (rd0^^k *> rd1 *> (0inf)%sym)).
  exact HS2.
Qed.

Lemma odd k r : RC (2^(2*k+3)+1) r -> exists c',
  PairUnion.Allowed QL QR c' /\
  ldh <* ld0^^(2*k+3) {{QR}}> [1] *> r -[tm]->+ c'.
Proof.
  intro HR; replace (2*k+3) with (2*k+1+2) in * by lia.
  destruct (to_T_one (2*k+1) r HR) as [e [w [HN HS]]].
  pose proof (Num_A_positive _ _ _ _ HN) as HE.
  pose proof (Num_Bodd _ _ _ _ k HN) as HB.
  pose proof (pow2_pos k).
  replace (e*2^k) with (1+(e*2^k-1)) in HB by nia.
  destruct (TOne _ _ _ _ HB) as [e' [w' [HN' [LE HT]]]].
  exists (STClosure.SC (true::w') (0inf)%sym); split.
  - apply (PairUnion.Signal _ _ 0); eapply STClosure.AllowedS;
      [exact HN'|lia|lia|lia|apply RC_zero].
  - follow10 HS; rewrite STClosure.TC_word.
    apply progress_evstep; exact (HT ldh (0inf)%sym).
Qed.

Lemma even_R_zero k r : RC (2^(2*k+2)+1) r ->
  ldh <* ld0^^(2*k+2) {{QR}}> [1] *> r -[tm]->+
  ldh <* ld0^^(3*k+4) {{QR}}> (0inf)%sym.
Proof.
  intro HR; destruct (to_T_one (2*k) r HR) as [e [w [HN HS]]].
  pose proof (Num_BB _ _ _ _ k HN) as HB.
  replace (0*2^k) with 0%nat in HB by lia.
  replace (2*(2*k+2)+1+2*k) with (2*(3*k+2)+1) in HB by lia.
  pose proof (TZeroOdd _ _ _ (0inf)%sym HB) as HT.
  replace (3*k+2+2) with (3*k+4) in HT by lia.
  follow10 HS; rewrite STClosure.TC_word.
  apply progress_evstep; exact HT.
Qed.

Hypothesis RZero : forall n, 1<=n -> exists c',
  PairUnion.Allowed QL QR c' /\
  ldh <* ld0^^n {{QR}}> (0inf)%sym -[tm]->+ c'.

Lemma cap_plus_one n r : 1<=n -> RC (2^n+1) r -> exists c',
  PairUnion.Allowed QL QR c' /\
  ldh <* ld0^^n {{QR}}> [1] *> r -[tm]->+ c'.
Proof.
  intros Hn Hr; destruct n as [|[|k]]; [lia|exact (one r Hr)|].
  replace (S (S k)) with (k+2) in * by lia.
  destruct (Nat.Even_or_Odd k) as [[m Hm]|[m Hm]]; subst k.
  - destruct (RZero (3*m+4) ltac:(lia)) as [c' [HA HS]].
    exists c'; split; [exact HA|].
    follow10 (even_R_zero m r Hr); apply progress_evstep; exact HS.
  - replace (2*m+1+2) with (2*m+3) in * by lia; exact (odd m r Hr).
Qed.
End Semantics.
End PairSpecial.

(* Shared: Saturated/Saturated. *)
Module Saturated.
Import HalfCounter HalfNormal Pair45Right PairUnion.
Local Open Scope sym_scope.

Definition cut (QR:Q) n := 0inf <* <[1;1;1;0] <* ld1^^n {{QR}}>
  rd1^^(n-1) *> [1;1;1;0;0] *> 0inf.

Lemma Num_total w : exists e o, Num (length w) e o w.
Proof.
  induction w as [|b w [e [o H]]].
  - exists 0%nat,0%nat; constructor.
  - destruct b; eexists; eexists; [apply NA|apply NB]; exact H.
Qed.

Lemma odd_word m : exists w e o, Num (2*(3*m+2)) e o (true::w) /\
  ldh <* tape (true::w)=
  0inf <* <[1;1;1;0] <* ld1^^(m*2) <* <[1;1;1] <* ld1 <* ld0^^m.
Proof.
  destruct (normal_zero (m*2)) as [z Hz].
  pose proof (normal_length _ _ _ Hz) as Hl.
  pose proof (normal_zero_tape _ _ _ Hz eq_refl) as Et.
  set (u:=repeat true (2*m)++true::false::false::z++[true]).
  assert (Hu:length u=2*(3*m+2)).
  { unfold u; rewrite length_app, repeat_length; cbn [length].
    rewrite length_app; cbn [length]; lia. }
  assert (Hhead:exists w, u=true::w).
  { unfold u; destruct m; cbn [Nat.mul Nat.add repeat app]; eauto. }
  destruct Hhead as [w Hw].
  destruct (Num_total u) as [e [o HN]].
  exists w,e,o; split.
  - rewrite Hw in HN; applys_eq HN; rewrite <-Hw; symmetry; exact Hu.
  - rewrite <-Hw; unfold u; repeat rewrite tape_app.
    rewrite (normal_full_tape _ _ _ (normal_full m) eq_refl).
    cbn [tape digit app]; repeat rewrite tape_app; rewrite Et.
    cbn [tape digit]; st; reflexivity.
Qed.

Lemma FC_head_one r t :
  FC ([0] *> r) (S t) 1 ([1] *> rd0^^(S t) *> r).
Proof.
  applys_eq (FC_d1 _ _ _ _ (FC_zero ([0] *> r) t)).
  st; simpl_rotate; reflexivity.
Qed.

Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis RZero : forall n, 1<=n -> exists c', Allowed QL QR c' /\
  ldh <* ld0^^n {{QR}}> 0inf -[tm]->+ c'.
Hypothesis REven : forall n e o w z r, Num (2*n) e o (true::w) ->
  1<=n -> RC z r -> z<=1 -> exists c', Allowed QL QR c' /\
  ldh <* tape (true::w) {{QR}}> r -[tm]->+ c'.
Hypothesis EvenCut : forall n r,
  0inf <* <[1;1;1;0] <* ld1^^(2+n*2) {{QR}}>
    rd1^^(1+n*2) *> [1;1;1;0;0] *> r -[tm]->+
  ldh <* ld0^^(4+n*3) {{QR}}> [0] *> r.
Hypothesis OddCut : forall l r n,
  l <* ld1 {{QR}}> rd1^^(n*2) *> [1;1;1;0;0] *> r -[tm]->+
  l <* <[1;1;1] <* ld1 <* ld0^^n {{QR}}> [1;0] *> r.

Lemma cut_even m : exists c', Allowed QL QR c' /\ cut QR (2+m*2) -[tm]->+ c'.
Proof.
  destruct (RZero (4+m*3) ltac:(lia)) as [c' [HA HS]].
  exists c'; split; [exact HA|].
  unfold cut; replace (2+m*2-1) with (1+m*2) by lia.
  follow10 (EvenCut m 0inf); apply progress_evstep.
  applys_eq HS; st; reflexivity.
Qed.

Lemma cut_odd m : exists c', Allowed QL QR c' /\ cut QR (1+m*2) -[tm]->+ c'.
Proof.
  destruct (odd_word m) as [w [e [o [HN Et]]]].
  destruct (REven _ _ _ _ _ _ HN ltac:(lia) (RC_d1 0 _ RC_zero) ltac:(lia))
    as [c' [HA HS]].
  exists c'; split; [exact HA|].
  unfold cut; replace (1+m*2-1) with (m*2) by lia.
  eapply progress_trans.
  - applys_eq (OddCut (0inf <* <[1;1;1;0] <* ld1^^(m*2)) 0inf m).
  - rewrite Et in HS; applys_eq HS; st; reflexivity.
Qed.

Lemma cut_return n : 1<=n -> exists c', Allowed QL QR c' /\ cut QR n -[tm]->+ c'.
Proof.
  intro Hn; destruct (Nat.Even_or_Odd n) as [[m ->]|[m ->]].
  - destruct m as [|m]; [lia|].
    replace (2*S m) with (2+m*2) by lia; apply cut_even.
  - replace (2*m+1) with (1+m*2) by lia; apply cut_odd.
Qed.

Hypothesis LStep : forall n k w, Normal n (1+k) w ->
  exists w', Normal n k w' /\ forall l r,
  l <* tape w <{{QL}} r -[tm]->+ l <* tape w' {{QR}}> r.
Hypothesis RCarry : forall l r k,
  l {{QR}}> rd1^^k *> [0] *> r -[tm]->+
  l <{{QL}} rd0^^k *> [1] *> r.
Hypothesis LOv : forall r n,
  ldh <* ld1^^(1+n) <{{QL}} r -[tm]->+
  ldh <* ld0^^(1+n) {{QR}}> [1] *> r.
Hypothesis Turn : forall l r,
  l {{QR}}> [1;1;0;0] *> r -[tm]->+
  l <* <[1;1;0] <{{QL}} [1] *> r.
Hypothesis One : forall r,
  ldh <* ld0 {{QR}}> [1] *> rd0 *> rd1 *> r -[tm]->+
  0inf <* <[1;1;1;0] <* ld1 {{QR}}> [1;1;1;0;0] *> r.

Let FP := HalfI.normal_FC_Rpairs tm QL QR LStep RCarry.

(* The same two protected batches as INum.pre, now permitting zero final
   budget and an arbitrary suffix after the displaced leading 1. *)
Lemma two_batches n b w t l r : Normal n (2^(1+S t)-2+b) w ->
  exists w', Normal n b w' /\
  l <* tape w {{QR}}> [1] *> rd0^^(S t) *> [1] *> r -[tm]->*
  l <* tape w' {{QR}}> rd1^^(S t) *> [1;1] *> r.
Proof.
  intro Hn.
  assert (Hp:2<=2^(S t)) by (cbn [Nat.pow]; pose proof (pow2_pos t); lia).
  replace (2^(1+S t)-2+b) with ((2^(S t)-2)+(2^(S t)+b)) in Hn
    by (rewrite Nat.pow_add_r; cbn [Nat.pow]; pose proof (pow2_pos t); nia).
  destruct (FP ([0;1] *> r) (S t) (2^(S t)-2) _ _ _ 1 _ Hn
    (FC_head_one ([1] *> r) t) ltac:(lia)) as [w1 [r1 [H1 [Hr1 HS1]]]].
  assert (Er1:r1=rd1^^(S t) *> [0;1] *> r).
  { apply FC_full_unique; applys_eq Hr1; flia. }
  subst r1.
  replace (2^(S t)+b) with (1+((2^(S t)-1)+b)) in H1 by lia.
  destruct (LStep _ _ _ H1) as [w2 [H2 HL]].
  destruct (FP ([1;1] *> r) (S t) (2^(S t)-1) _ _ _ 0 _ H2
    (FC_zero ([1;1] *> r) (S t)) ltac:(lia)) as [w3 [r3 [H3 [Hr3 HS3]]]].
  assert (Er3:r3=rd1^^(S t) *> [1;1] *> r).
  { apply FC_full_unique; exact Hr3. }
  subst r3; exists w3; split; [exact H3|].
  follow (HS1 l).
  follow100 (RCarry (l <* tape w1) ([1] *> r) (S t)).
  follow100 (HL l (rd0^^(S t) *> [1;1] *> r)); apply HS3.
Qed.

Lemma front n :
  ldh <* ld0^^(S n) {{QR}}> [1] *> rd0^^(S n) *> rd1 *> 0inf -[tm]->+
  0inf <* <[1;1;1;0] <* ld0^^(S n) <{{QL}}
    [1] *> rd0^^n *> [1;1;0;0] *> 0inf.
Proof.
  assert (Hp:2<=2^(S n)) by (cbn [Nat.pow]; pose proof (pow2_pos n); lia).
  pose proof (normal_full (S n)) as Hn.
  replace (2^(S n)-1) with ((2^(S n)-2)+1) in Hn by lia.
  destruct (FP ([0;1;0;0] *> 0inf) (S n) (2^(S n)-2) _ _ _ 1 _ Hn
    (HalfI.FC_insert_one 0inf n) ltac:(lia)) as [w1 [r1 [H1 [Hr1 HS1]]]].
  assert (Er1:r1=rd1^^(S n) *> [0;1;0;0] *> 0inf).
  { apply FC_full_unique; applys_eq Hr1; flia. }
  subst r1; destruct (LStep _ _ _ H1) as [w2 [H2 HL]].
  rewrite (normal_zero_tape _ _ _ H2 eq_refl) in HL.
  pose proof (HS1 ldh) as HH.
  rewrite (normal_full_tape _ _ _ (normal_full (S n)) eq_refl) in HH.
  follow HH.
  follow10 (RCarry (ldh <* tape w1) ([1;0;0] *> 0inf) (S n)).
  follow100 (HL ldh (rd0^^(S n) *> [1;1;0;0] *> 0inf)).
  follow100 (RCarry (ldh <* ld1^^(S n))
    ([0;0] *> rd0^^n *> [1;1;0;0] *> 0inf) 0).
  follow100 (LOv (rd1 *> rd0^^n *> [1;1;0;0] *> 0inf) n).
  apply progress_evstep.
  applys_eq (Turn (ldh <* ld0^^(S n)) (rd0^^n *> [1;1;0;0] *> 0inf)).
  st; simpl_rotate; reflexivity.
Qed.

Lemma to_cut n : 1<=n ->
  ldh <* ld0^^n {{QR}}> [1] *> rd0^^n *> rd1 *> 0inf -[tm]->+ cut QR n.
Proof.
  intro Hlen; destruct n as [|[|n]]; [lia| |].
  - unfold cut; applys_eq (One 0inf); st; reflexivity.
  - assert (Hp:2<=2^(S (S n))) by (cbn [Nat.pow]; pose proof (pow2_pos n); lia).
    pose proof (normal_full (S (S n))) as Hn.
    replace (2^(S (S n))-1) with (1+(2^(S (S n))-2)) in Hn by lia.
    destruct (LStep _ _ _ Hn) as [w1 [H1 HL]].
    replace (2^(S (S n))-2) with (2^(1+S n)-2+0) in H1
      by (rewrite Nat.add_0_r; reflexivity).
    destruct (two_batches _ _ _ n (0inf <* <[1;1;1;0]) ([1;0;0] *> 0inf) H1)
      as [w2 [H2 HS]].
    rewrite (normal_zero_tape _ _ _ H2 eq_refl) in HS.
    rewrite (normal_full_tape _ _ _ (normal_full (S (S n))) eq_refl) in HL.
    follow10 (front (S n)).
    follow100 (HL (0inf <* <[1;1;1;0]) ([1] *> rd0^^(S n) *> [1;1;0;0] *> 0inf)).
    applys_eq HS; unfold cut; st; reflexivity.
Qed.

Lemma full n w r : Normal n (2^n-1) w -> 1<=n -> RC (2^n) r ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Proof.
  intros Hn Hlen Hr; destruct (cut_return n Hlen) as [c' [HA HS]].
  assert (Hr0:RC (2^n) (rd0^^n *> rd1 *> 0inf)).
  { pose proof (RC_zeros 1 _ n (RC_d1 0 _ RC_zero)) as H.
    now rewrite Nat.mul_1_r in H. }
  assert (Er:r=rd0^^n *> rd1 *> 0inf) by (eapply RC_unique; eauto).
  subst r; exists c'; split; [exact HA|].
  unfold IC; rewrite (normal_full_tape _ _ _ Hn eq_refl).
  eapply progress_trans; [apply to_cut; exact Hlen|exact HS].
Qed.
End Semantics.
End Saturated.

(* Shared: Closure/PairClosure. *)
Module PairClosure.
Import HalfNormal Pair45Right PairUnion.
Local Open Scope sym_scope.
Section Semantics.
Variables (tm:TM) (QL QR:Q).
Hypothesis IZero : forall n k w r, Normal n k w -> 1<=n -> RC 0 r ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Hypothesis ISmall : forall n k w z r d, Normal n k w -> 1<=n -> RC z r ->
  0<z -> z<2^d -> d<=n -> 2^d-1<=k ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Hypothesis ICap : forall n w r, Normal n (2^n-1) w -> 1<=n -> RC (2^n) r ->
  exists c', Allowed QL QR c' /\ IC QR w r -[tm]->+ c'.
Hypothesis IExtra : forall n r, 1<=n -> RC (2^n+1) r -> exists c',
  Allowed QL QR c' /\ ldh <* ld0^^n {{QR}}> [1] *> r -[tm]->+ c'.
Hypothesis JDrain : forall z c, TenClosure.Allowed QL z c -> exists c',
  TenClosure.Allowed QL 0 c' /\ c -[tm]->* c'.
Hypothesis JZero : forall c, TenClosure.Allowed QL 0 c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.
Hypothesis SDrain : forall z c, STClosure.Allowed z c -> exists c',
  STClosure.Allowed 0 c' /\ c -[tm]->* c'.
Hypothesis SZero : forall c, STClosure.Allowed 0 c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.

Lemma I_step c : IAllowed QR c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.
Proof.
  intros [n k w z r HN Hlen Hr Hg].
  destruct (Nat.eq_dec z 0) as [->|Hz]; [eapply IZero; eassumption|].
  destruct Hg as [Hz0|[[d [Hd [Hdn Hk]]]|[Hk Hb]]]; [lia| |].
  - eapply ISmall; eauto; lia.
  - destruct (Nat.lt_ge_cases z (2^n)) as [Hlt|Hge].
    + eapply ISmall with (d:=n); eauto; lia.
    + destruct (Nat.eq_dec z (2^n)) as [->|Hne].
      * subst k; eapply ICap; eassumption.
      * assert (z=2^n+1) by lia; subst z.
        unfold IC; rewrite (normal_full_tape _ _ _ HN Hk).
        apply IExtra; assumption.
Qed.

Lemma step c : Allowed QL QR c -> exists c',
  Allowed QL QR c' /\ c -[tm]->+ c'.
Proof.
  intros [c' HI|z c' HJ|z c' HS]; [apply I_step; exact HI| |].
  - destruct (JDrain _ _ HJ) as [c1 [HJ1 HS1]].
    destruct (JZero _ HJ1) as [c2 [HA HS2]].
    exists c2; split; [exact HA|eapply evstep_progress_trans; eauto].
  - destruct (SDrain _ _ HS) as [c1 [HS0 HS1]].
    destruct (SZero _ HS0) as [c2 [HA HS2]].
    exists c2; split; [exact HA|eapply evstep_progress_trans; eauto].
Qed.

Lemma nonhalt c : Allowed QL QR c -> ~halts tm c.
Proof. apply (progress_nonhalt tm (Allowed QL QR) c step). Qed.
End Semantics.
End PairClosure.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0LC_1RA1RE_0RF0RB_1LC---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Lemma LInc l r n: l <* ld0 <* ld1^^n <{{C}} r -->+
  l <* ld1 <* ld0^^n {{B}}> r.
Proof. es. Qed.
Lemma RInc l r n: l {{B}}> rd1^^n *> [0] *> r -->+
  l <{{C}} rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n: ldh <* ld1^^(1+n) <{{C}} r -->+
  ldh <* ld0^^(1+n) {{B}}> [1] *> r.
Proof. es. Qed.

Module A4Half.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Lemma ECarry l r b :
  l <* Half 1 <* Half b <{{E}} [0] *> r -->+
  l <{{E}} [0] *> [1]^^6 *> r.
Proof. destruct b; es. Qed.
Lemma EStop l r b :
  l <* Half 0 <* Half b <{{E}} [0] *> r -->+
  l <* Half 1 |s> r.
Proof. destruct b; es. Qed.
Lemma SOnes l r n :
  l |s> [1]^^(n*6) *> r -->* l <* ld0^^n |s> r.
Proof. es. Qed.
Lemma S100 l r : l |s> [1;0;0] *> r -->+ l <* Half 1 |s> r.
Proof. es. Qed.
Lemma T100 l r : l |t> [1;0;0] *> r -->+ l <{{E}} [0] *> [1]^^6 *> r.
Proof. es. Qed.
Lemma S000 l r b : l <* Half b |s> [0;0;0] *> r -->+
  l <{{E}} [0] *> [1]^^5 *> [Opp b;0;0;1] *> r.
Proof. destruct b; es. Qed.
Lemma S000_end l r b : l |s> [1]^^5 *> [Opp b;0;0;1] *> r -->+
  l <* Half 0 <* Half b <* Half 0 |t> r.
Proof. destruct b; es. Qed.

Lemma MarkedCarry l r bs :
  l <* Marked bs <{{E}} [0] *> r -->*
  l <{{E}} [0] *> [1]^^(length bs*6) *> r.
Proof.
  revert l r; induction bs as [|b bs IH]; intros l r; cbn [Marked length]; st.
  - finish.
  - follow100 (ECarry (l <* Marked bs) r b).
    follow (IH l ([1]^^6 *> r)).
    finish.
    rewrite (lpow_mul [1] (length bs) 6).
    rewrite <- (Str_app_assoc (([1]^^6)^^(length bs)) ([1]^^6) r).
    rewrite lpow_shift; reflexivity.
Qed.

End A4Half.

Module A4Boundary.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma ROvOddRecover l r a m:
  l <* ld0 <* ld1^^a {{B}}> rd1^^(m*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(m+a+1) {{B}}> [1] *> r.
Proof. es. Qed.

Lemma ROvEvenAux l r m:
  l <* <[0] {{B}}> rd1^^(m*2) *> [1;1;0;0] *> r -->+
  l <* <[1] <* ld0^^m <* <[1;1;0;1] {{D}}> r.
Proof. es. Qed.

Lemma ROv101Odd l r m:
  l <* <[0] {{B}}> rd1^^(m*2+1) *> [1;0;1] *> r -->+
  l <* <[1] <* ld0^^(m+1) {{B}}> r.
Proof. es. Qed.

Lemma R1100Turn l r:
  l {{B}}> [1;1;0;0] *> r -->+
  l <* <[1;1;0] <{{C}} [1] *> r.
Proof. es. Qed.

End A4Boundary.

Module A4Capacity.
Lemma saturated_one r :
  ldh <* ld0 {{B}}> [1] *> rd0 *> rd1 *> r -[tm]->+
  0inf <* <[1;1;1;0] <* ld1 {{B}}> [1;1;1;0;0] *> r.
Proof. es. Qed.

Lemma odd_capacity_entry l r n :
  l <* ld1 {{B}}> rd1^^(n*2) *> [1;1;1;0;0] *> r -[tm]->+
  l <* <[1;1;1] <* ld1 <* ld0^^n {{B}}> [1;0] *> r.
Proof. es. Qed.

Lemma even_capacity_cleanup n r :
  0inf <* <[1;1;1;0] <* ld1^^(2+n*2) {{B}}>
    rd1^^(1+n*2) *> [1;1;1;0;0] *> r -[tm]->+
  ldh <* ld0^^(4+n*3) {{B}}> [0] *> r.
Proof.
  replace (4+n*3) with (4+(n+n*2)) by lia.
  rewrite (lpow_add _ 4 (n+n*2) ld0), (lpow_add _ n (n*2) ld0), (lpow_mul ld0 n 2).
  repeat rewrite Str_app_assoc.
  es' n & r.
Qed.

(* N=1, full left budget, z=40: removing the size condition is invalid. *)
End A4Capacity.

Module A4TZero.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Lemma TStart l r : l |t> [0;0;0] *> r -->+
  l <* Half 1 <* Half 1 <{{C}} [1] *> r.
Proof. unfold Half. es. Qed.

Lemma LOnes l r h :
  l <* (Half 1)^^h <{{C}} r -->* l <{{C}} rd0^^h *> r.
Proof. unfold Half. es. Qed.

Lemma TZeroEntry l r h :
  l <* Half 0 <* (Half 1)^^h |t> [0;0;0] *> r -->+
  l <* Half 0 <{{C}} rd0^^(h+2) *> [1] *> r.
Proof.
  rewrite lpow_add; st.
  follow10 (TStart (l <* Half 0 <* (Half 1)^^h) r).
  follow (LOnes (l <* Half 0 <* (Half 1)^^h) ([1] *> r) 2).
  apply LOnes.
Qed.

Lemma LBAtoE l r :
  l <* Half 1 <* Half 0 <{{C}} r -->+
  l <{{E}} [0] *> [1]^^5 *> r.
Proof. unfold Half. es. Qed.

Lemma SFive l r : l |s> [1]^^5 *> r -->+
  l <* Half 0 <* Half 0 <* Half 0 {{B}}> r.
Proof. unfold Half. es. Qed.

Lemma R100Scan l r n :
  l {{B}}> rd1^^n *> r -->* l <* (Half 1)^^n {{B}}> r.
Proof. unfold Half. es. Qed.

Lemma RExit l r h :
  l {{B}}> rd1^^(h+2) *> [1] *> r -->+
  l <* (Half 1)^^(h+1) |t> r.
Proof.
  follow (R100Scan l ([1] *> r) (h+2)).
  replace (h+2) with (1+(h+1)) by lia. rewrite lpow_add; st.
  unfold Half. es.
Qed.
End A4TZero.

Module A4ZeroBoundary.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma SZeroEntry l r :
  l <* <[1;1;0;1] {{D}}> [0;0;0] *> r -->+
  l <* Half 0 <{{C}} [0;0;0;1] *> r.
Proof. unfold Half; es. Qed.

Lemma R11Bit l r b : l {{B}}> [1;1;b;0;0] *> r -->+
  l <* Half 0 <{{C}} [1;0] *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma EHalfBoundary r b : ldh <* Half b <{{E}} [0] *> r -->+
  ldh {{B}}> [1]^^6 *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma EEven r n : ldh <{{E}} [0] *> [1]^^(n*6+5) *> r -->+
  ldh <* ld0^^(n+1) {{B}}> [1] *> r.
Proof. es. Qed.

Lemma EOdd r n b : ldh <* Half b <{{E}} [0] *> [1]^^(n*6+5) *> r -->+
  ldh <* ld0^^(n+1) <* Half 0 {{B}}> [1;1] *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma LSingle r : ldh <* Half 0 <{{C}} r -->+
  ldh <* Half 0 {{B}}> [1;1] *> r.
Proof. unfold Half; es. Qed.

Lemma LZeroEven r bs :
  ldh <* Marked bs <* Half 1 <* Half 0 <{{C}} r -->+
  ldh <* ld0^^(length bs+1) {{B}}> [1] *> r.
Proof.
  follow10 (A4TZero.LBAtoE (ldh <* Marked bs) r).
  follow (A4Half.MarkedCarry ldh ([1]^^5 *> r) bs).
  replace ([1]^^(length bs*6) *> [1]^^5 *> r)
    with ([1]^^(length bs*6+5) *> r)
    by (rewrite lpow_add, Str_app_assoc; reflexivity).
  follow100 (EEven r (length bs)); finish.
Qed.

Lemma LZeroOdd r bs b :
  ldh <* Half b <* Marked bs <* Half 1 <* Half 0 <{{C}} r -->+
  ldh <* ld0^^(length bs+1) <* Half 0 {{B}}> [1;1] *> r.
Proof.
  follow10 (A4TZero.LBAtoE (ldh <* Half b <* Marked bs) r).
  follow (A4Half.MarkedCarry (ldh <* Half b) ([1]^^5 *> r) bs).
  replace ([1]^^(length bs*6) *> [1]^^5 *> r)
    with ([1]^^(length bs*6+5) *> r)
    by (rewrite lpow_add, Str_app_assoc; reflexivity).
  follow100 (EOdd r (length bs) b); finish.
Qed.
End A4ZeroBoundary.

Module A4TenHalf.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma R101EvenEntry l r m :
  l <* <[0] {{B}}> rd1^^(m*2) *> [1;0;1;0;0] *> r -->+
  l <* <[0] <{{C}} [1]^^(m*6+3) *> [0;0] *> r.
Proof. es. Qed.

Lemma R111Scan l r n :
  l {{B}}> [1]^^(n*3) *> r -->* l <* (Half 0)^^n {{B}}> r.
Proof. unfold Half. es. Qed.

Lemma init : c0 -->* ldh <* ld1^^4 <{{C}}
  rd0 *> rd1 *> rd0 *> rd1 *> 0inf.
Proof. esx. Qed.
End A4TenHalf.

Module A4Model.
Definition LInc := HalfCounter.LInc tm
  A4Half.ECarry A4Half.EStop A4Half.SOnes C B
  (fun l r => LInc l r 0) A4TZero.LBAtoE A4TZero.SFive.
Definition RScan l r k := RInc l ([0;0] *> r) k.
Definition RC_pairs := HalfCounter.RC_pairs tm C B LInc RScan.
Definition FC_pairs := HalfCounter.FC_pairs tm C B LInc RScan.
Definition TZero := HalfCounter.TZero tm C B LInc RScan
  A4TZero.TZeroEntry A4TZero.RExit.
End A4Model.

Module A4Normal.
Definition normal_LInc := HalfNormal.normal_LInc tm C B A4Model.LInc.
End A4Normal.

Module A4ZeroNum.
Import HalfCounter HalfZero.
Lemma LZeroEven m e w r : Num (2*m) e 0 (true::w) ->
  ldh <* tape (true::w) <{{C}} r -[tm]->+
  ldh <* ld0^^m {{B}}> [1] *> r.
Proof.
  intro H; destruct (zero_even_A _ _ _ H) as [bs [Hm Et]].
  rewrite Et, <-Hm; repeat rewrite Str_app_assoc.
  apply A4ZeroBoundary.LZeroEven.
Qed.

Lemma LZeroOdd m e w r : Num (2*m+1) e 0 (true::w) ->
  ldh <* tape (true::w) <{{C}} r -[tm]->+
  ldh <* ld0^^m <* Half 0 {{B}}> [1;1] *> r.
Proof.
  intro H; destruct (zero_odd_A _ _ _ H) as [[-> ->]|[bs [b [Hm Et]]]].
  - cbn [tape digit lpow]; rewrite app_nil_r; apply A4ZeroBoundary.LSingle.
  - rewrite Et, <-Hm; repeat rewrite Str_app_assoc.
    apply A4ZeroBoundary.LZeroOdd.
Qed.
End A4ZeroNum.

Module A4Drain.
Definition even := HalfDrain.even tm C B A4Model.RC_pairs
  A4ZeroNum.LZeroEven.
Definition odd := HalfDrain.odd tm C B A4Model.RC_pairs
  A4ZeroNum.LZeroOdd A4ZeroBoundary.R11Bit.
Definition S_even := HalfDrain.S_even tm C B A4Model.RC_pairs
  A4ZeroNum.LZeroOdd A4ZeroBoundary.R11Bit A4ZeroBoundary.SZeroEntry.
Definition S_odd := HalfDrain.S_odd tm C B A4Model.RC_pairs
  A4ZeroNum.LZeroEven A4ZeroBoundary.SZeroEntry.
End A4Drain.

Module A4STNum.
Definition BorrowSem := HalfCounter.Borrow_spec tm
  A4Half.ECarry A4Half.EStop A4Half.SOnes.
Definition S100 := HalfST.S100 tm A4Half.S100.
Definition T100 := HalfST.T100 tm BorrowSem A4Half.T100 A4Half.SOnes.
Definition S000 := HalfST.S000 tm BorrowSem A4Half.S000 A4Half.S000_end.
End A4STNum.

Module A4STClosure.
Definition to_zero := STClosure.to_zero tm
  A4STNum.S100 A4STNum.T100 A4STNum.S000 A4Model.TZero.
End A4STClosure.

Module A4TenNum.
Definition pre := HalfTen.pre tm C B A4Model.LInc RInc.
Definition even_exit := HalfTen.even_exit tm C B A4Model.LInc RInc
  A4TenHalf.R101EvenEntry A4TenHalf.R111Scan.
Definition odd_exit := HalfTen.odd_exit tm C B RInc A4Boundary.ROv101Odd.
End A4TenNum.

Module A4TenClosure.
Definition to_zero := TenClosure.to_zero tm C B
  A4TenNum.pre A4TenNum.even_exit A4TenNum.odd_exit.
End A4TenClosure.

Module A4INum.
Definition odd := HalfI.odd tm C B A4Normal.normal_LInc RInc A4Boundary.ROvOddRecover.
Definition even := HalfI.even tm C B A4Normal.normal_LInc RInc A4Boundary.ROvEvenAux.
End A4INum.

Module A4IClosure.
Definition small := IClosure.small tm C B A4INum.odd A4INum.even.
End A4IClosure.

Module A4Union.
Definition S_zero := PairUnion.S_zero tm C B A4Drain.S_even A4Drain.S_odd.
Definition J_zero := PairUnion.J_zero tm C B A4Drain.even A4Drain.odd.
End A4Union.

Module A4Return.
Import PairUnion Pair45Right.
Local Open Scope sym_scope.
Definition even_R_return := NormalReturn.even_R_return tm C B A4Model.RScan A4Drain.even.
Definition R_zero_full := NormalReturn.R_zero_full tm C B A4Model.RScan A4Drain.even.
Definition I_zero := NormalReturn.I_zero tm C B A4Model.RScan A4Drain.even.
Definition seed := ldh <* ld0^^4 {{B}}> [1] *>
  rd0 *> rd1 *> rd0 *> rd1 *> 0inf.
Lemma init : Allowed C B seed /\ c0 -[tm]->* seed.
Proof.
  split.
  - unfold seed; apply Ordinary; eapply I_full with (z:=10); try (cbn; lia).
    exact (RC_d0 5 _ (RC_d1 2 _ (RC_d0 1 _ (RC_d1 0 _ RC_zero)))).
  - unfold seed; follow A4TenHalf.init.
    apply progress_evstep, (LOv _ 3).
Qed.
End A4Return.

Module A4TBoundary.
Definition TZeros := HalfTBoundary.TZeros tm A4Model.TZero.
Definition T100_zero_odd := HalfTBoundary.T100_zero_odd tm B
  A4Half.T100 A4Half.MarkedCarry A4ZeroBoundary.EHalfBoundary A4TenHalf.R111Scan.
End A4TBoundary.

Module A4Special.
Definition cap_plus_one := PairSpecial.cap_plus_one tm C B A4Boundary.ROvEvenAux
  A4STNum.S100 A4STNum.T100 A4STNum.S000 A4TBoundary.TZeros
  A4TBoundary.T100_zero_odd A4Return.R_zero_full.
End A4Special.

Module A4Saturated.
Definition full := Saturated.full tm C B A4Return.R_zero_full
  A4Return.even_R_return A4Capacity.even_capacity_cleanup A4Capacity.odd_capacity_entry
  A4Normal.normal_LInc RInc LOv A4Boundary.R1100Turn A4Capacity.saturated_one.
End A4Saturated.

Definition closed := PairClosure.nonhalt tm C B
  A4Return.I_zero A4IClosure.small A4Saturated.full A4Special.cap_plus_one
  A4TenClosure.to_zero A4Union.J_zero A4STClosure.to_zero A4Union.S_zero.
Theorem nonhalt : ~halts tm c0.
Proof.
  destruct A4Return.init as [HA HS].
  eapply multistep_nonhalt; [exact HS|apply closed; exact HA].
Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RC1RE_1RF0RA_0LE---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Lemma LInc l r n: l <* ld0 <* ld1^^n <{{B}} r -->+
  l <* ld1 <* ld0^^n {{A}}> r.
Proof. es. Qed.
Lemma RInc l r n: l {{A}}> rd1^^n *> [0] *> r -->+
  l <{{B}} rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n: ldh <* ld1^^(1+n) <{{B}} r -->+
  ldh <* ld0^^(1+n) {{A}}> [1] *> r.
Proof. es. Qed.

Module A5Half.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Lemma ECarry l r b :
  l <* Half 1 <* Half b <{{E}} [0] *> r -->+
  l <{{E}} [0] *> [1]^^6 *> r.
Proof. destruct b; es. Qed.
Lemma EStop l r b :
  l <* Half 0 <* Half b <{{E}} [0] *> r -->+
  l <* Half 1 |s> r.
Proof. destruct b; es. Qed.
Lemma SOnes l r n :
  l |s> [1]^^(n*6) *> r -->* l <* ld0^^n |s> r.
Proof. es. Qed.
Lemma S100 l r : l |s> [1;0;0] *> r -->+ l <* Half 1 |s> r.
Proof. es. Qed.
Lemma T100 l r : l |t> [1;0;0] *> r -->+ l <{{E}} [0] *> [1]^^6 *> r.
Proof. es. Qed.
Lemma S000 l r b : l <* Half b |s> [0;0;0] *> r -->+
  l <{{E}} [0] *> [1]^^5 *> [Opp b;0;0;1] *> r.
Proof. destruct b; es. Qed.
Lemma S000_end l r b : l |s> [1]^^5 *> [Opp b;0;0;1] *> r -->+
  l <* Half 0 <* Half b <* Half 0 |t> r.
Proof. destruct b; es. Qed.

Lemma MarkedCarry l r bs :
  l <* Marked bs <{{E}} [0] *> r -->*
  l <{{E}} [0] *> [1]^^(length bs*6) *> r.
Proof.
  revert l r; induction bs as [|b bs IH]; intros l r; cbn [Marked length]; st.
  - finish.
  - follow100 (ECarry (l <* Marked bs) r b).
    follow (IH l ([1]^^6 *> r)).
    finish.
    rewrite (lpow_mul [1] (length bs) 6).
    rewrite <- (Str_app_assoc (([1]^^6)^^(length bs)) ([1]^^6) r).
    rewrite lpow_shift; reflexivity.
Qed.

End A5Half.

Module A5Boundary.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma ROvOddRecover l r a m:
  l <* ld0 <* ld1^^a {{A}}> rd1^^(m*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(m+a+1) {{A}}> [1] *> r.
Proof. es. Qed.

Lemma ROvEvenAux l r m:
  l <* <[0] {{A}}> rd1^^(m*2) *> [1;1;0;0] *> r -->+
  l <* <[1] <* ld0^^m <* <[1;1;0;1] {{D}}> r.
Proof. es. Qed.

Lemma ROv101Odd l r m:
  l <* <[0] {{A}}> rd1^^(m*2+1) *> [1;0;1] *> r -->+
  l <* <[1] <* ld0^^(m+1) {{A}}> r.
Proof. es. Qed.

Lemma R1100Turn l r:
  l {{A}}> [1;1;0;0] *> r -->+
  l <* <[1;1;0] <{{B}} [1] *> r.
Proof. es. Qed.

End A5Boundary.

Module A5Capacity.
Lemma saturated_one r :
  ldh <* ld0 {{A}}> [1] *> rd0 *> rd1 *> r -[tm]->+
  0inf <* <[1;1;1;0] <* ld1 {{A}}> [1;1;1;0;0] *> r.
Proof. es. Qed.

Lemma odd_capacity_entry l r n :
  l <* ld1 {{A}}> rd1^^(n*2) *> [1;1;1;0;0] *> r -[tm]->+
  l <* <[1;1;1] <* ld1 <* ld0^^n {{A}}> [1;0] *> r.
Proof. es. Qed.

Lemma even_capacity_cleanup n r :
  0inf <* <[1;1;1;0] <* ld1^^(2+n*2) {{A}}>
    rd1^^(1+n*2) *> [1;1;1;0;0] *> r -[tm]->+
  ldh <* ld0^^(4+n*3) {{A}}> [0] *> r.
Proof.
  replace (4+n*3) with (4+(n+n*2)) by lia.
  rewrite (lpow_add _ 4 (n+n*2) ld0), (lpow_add _ n (n*2) ld0), (lpow_mul ld0 n 2).
  repeat rewrite Str_app_assoc.
  es' n & r.
Qed.

End A5Capacity.

Module A5TZero.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "l |s> r" := (l <* <[1;1;0;1] {{D}}> r) (at level 30).
Notation "l |t> r" := (l <* <[1;1;1;1] {{D}}> r) (at level 30).

Lemma TStart l r : l |t> [0;0;0] *> r -->+
  l <* Half 1 <* Half 1 <{{B}} [1] *> r.
Proof. unfold Half. es. Qed.

Lemma LOnes l r h :
  l <* (Half 1)^^h <{{B}} r -->* l <{{B}} rd0^^h *> r.
Proof. unfold Half. es. Qed.

Lemma TZeroEntry l r h :
  l <* Half 0 <* (Half 1)^^h |t> [0;0;0] *> r -->+
  l <* Half 0 <{{B}} rd0^^(h+2) *> [1] *> r.
Proof.
  rewrite lpow_add; st.
  follow10 (TStart (l <* Half 0 <* (Half 1)^^h) r).
  follow (LOnes (l <* Half 0 <* (Half 1)^^h) ([1] *> r) 2).
  apply LOnes.
Qed.

Lemma LBAtoE l r :
  l <* Half 1 <* Half 0 <{{B}} r -->+
  l <{{E}} [0] *> [1]^^5 *> r.
Proof. unfold Half. es. Qed.

Lemma SFive l r : l |s> [1]^^5 *> r -->+
  l <* Half 0 <* Half 0 <* Half 0 {{A}}> r.
Proof. unfold Half. es. Qed.

Lemma R100Scan l r n :
  l {{A}}> rd1^^n *> r -->* l <* (Half 1)^^n {{A}}> r.
Proof. unfold Half. es. Qed.

Lemma RExit l r h :
  l {{A}}> rd1^^(h+2) *> [1] *> r -->+
  l <* (Half 1)^^(h+1) |t> r.
Proof.
  follow (R100Scan l ([1] *> r) (h+2)).
  replace (h+2) with (1+(h+1)) by lia. rewrite lpow_add; st.
  unfold Half. es.
Qed.
End A5TZero.

Module A5ZeroBoundary.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma SZeroEntry l r :
  l <* <[1;1;0;1] {{D}}> [0;0;0] *> r -->+
  l <* Half 0 <{{B}} [0;0;0;1] *> r.
Proof. unfold Half; es. Qed.

Lemma R11Bit l r b : l {{A}}> [1;1;b;0;0] *> r -->+
  l <* Half 0 <{{B}} [1;0] *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma EHalfBoundary r b : ldh <* Half b <{{E}} [0] *> r -->+
  ldh {{A}}> [1]^^6 *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma EEven r n : ldh <{{E}} [0] *> [1]^^(n*6+5) *> r -->+
  ldh <* ld0^^(n+1) {{A}}> [1] *> r.
Proof. es. Qed.

Lemma EOdd r n b : ldh <* Half b <{{E}} [0] *> [1]^^(n*6+5) *> r -->+
  ldh <* ld0^^(n+1) <* Half 0 {{A}}> [1;1] *> r.
Proof. destruct b; unfold Half; es. Qed.

Lemma LSingle r : ldh <* Half 0 <{{B}} r -->+
  ldh <* Half 0 {{A}}> [1;1] *> r.
Proof. unfold Half; es. Qed.

Lemma LZeroEven r bs :
  ldh <* Marked bs <* Half 1 <* Half 0 <{{B}} r -->+
  ldh <* ld0^^(length bs+1) {{A}}> [1] *> r.
Proof.
  follow10 (A5TZero.LBAtoE (ldh <* Marked bs) r).
  follow (A5Half.MarkedCarry ldh ([1]^^5 *> r) bs).
  replace ([1]^^(length bs*6) *> [1]^^5 *> r)
    with ([1]^^(length bs*6+5) *> r)
    by (rewrite lpow_add, Str_app_assoc; reflexivity).
  follow100 (EEven r (length bs)); finish.
Qed.

Lemma LZeroOdd r bs b :
  ldh <* Half b <* Marked bs <* Half 1 <* Half 0 <{{B}} r -->+
  ldh <* ld0^^(length bs+1) <* Half 0 {{A}}> [1;1] *> r.
Proof.
  follow10 (A5TZero.LBAtoE (ldh <* Half b <* Marked bs) r).
  follow (A5Half.MarkedCarry (ldh <* Half b) ([1]^^5 *> r) bs).
  replace ([1]^^(length bs*6) *> [1]^^5 *> r)
    with ([1]^^(length bs*6+5) *> r)
    by (rewrite lpow_add, Str_app_assoc; reflexivity).
  follow100 (EOdd r (length bs) b); finish.
Qed.
End A5ZeroBoundary.

Module A5TenHalf.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma R101EvenEntry l r m :
  l <* <[0] {{A}}> rd1^^(m*2) *> [1;0;1;0;0] *> r -->+
  l <* <[0] <{{B}} [1]^^(m*6+3) *> [0;0] *> r.
Proof. es. Qed.

Lemma R111Scan l r n :
  l {{A}}> [1]^^(n*3) *> r -->* l <* (Half 0)^^n {{A}}> r.
Proof. unfold Half. es. Qed.

Lemma init : c0 -->* ldh <* ld1 <{{B}} rd0 *> rd1 *> 0inf.
Proof. esx. Qed.
End A5TenHalf.

Module A5Model.
Definition LInc := HalfCounter.LInc tm
  A5Half.ECarry A5Half.EStop A5Half.SOnes B A
  (fun l r => LInc l r 0) A5TZero.LBAtoE A5TZero.SFive.
Definition RScan l r k := RInc l ([0;0] *> r) k.
Definition RC_pairs := HalfCounter.RC_pairs tm B A LInc RScan.
Definition FC_pairs := HalfCounter.FC_pairs tm B A LInc RScan.
Definition TZero := HalfCounter.TZero tm B A LInc RScan
  A5TZero.TZeroEntry A5TZero.RExit.
End A5Model.

Module A5Normal.
Definition normal_LInc := HalfNormal.normal_LInc tm B A A5Model.LInc.
End A5Normal.

Module A5ZeroNum.
Import HalfCounter HalfZero.
Lemma LZeroEven m e w r : Num (2*m) e 0 (true::w) ->
  ldh <* tape (true::w) <{{B}} r -[tm]->+
  ldh <* ld0^^m {{A}}> [1] *> r.
Proof.
  intro H; destruct (zero_even_A _ _ _ H) as [bs [Hm Et]].
  rewrite Et, <-Hm; repeat rewrite Str_app_assoc.
  apply A5ZeroBoundary.LZeroEven.
Qed.

Lemma LZeroOdd m e w r : Num (2*m+1) e 0 (true::w) ->
  ldh <* tape (true::w) <{{B}} r -[tm]->+
  ldh <* ld0^^m <* Half 0 {{A}}> [1;1] *> r.
Proof.
  intro H; destruct (zero_odd_A _ _ _ H) as [[-> ->]|[bs [b [Hm Et]]]].
  - cbn [tape digit lpow]; rewrite app_nil_r; apply A5ZeroBoundary.LSingle.
  - rewrite Et, <-Hm; repeat rewrite Str_app_assoc.
    apply A5ZeroBoundary.LZeroOdd.
Qed.
End A5ZeroNum.

Module A5Drain.
Definition even := HalfDrain.even tm B A A5Model.RC_pairs
  A5ZeroNum.LZeroEven.
Definition odd := HalfDrain.odd tm B A A5Model.RC_pairs
  A5ZeroNum.LZeroOdd A5ZeroBoundary.R11Bit.
Definition S_even := HalfDrain.S_even tm B A A5Model.RC_pairs
  A5ZeroNum.LZeroOdd A5ZeroBoundary.R11Bit A5ZeroBoundary.SZeroEntry.
Definition S_odd := HalfDrain.S_odd tm B A A5Model.RC_pairs
  A5ZeroNum.LZeroEven A5ZeroBoundary.SZeroEntry.
End A5Drain.

Module A5STNum.
Definition BorrowSem := HalfCounter.Borrow_spec tm
  A5Half.ECarry A5Half.EStop A5Half.SOnes.
Definition S100 := HalfST.S100 tm A5Half.S100.
Definition T100 := HalfST.T100 tm BorrowSem A5Half.T100 A5Half.SOnes.
Definition S000 := HalfST.S000 tm BorrowSem A5Half.S000 A5Half.S000_end.
End A5STNum.

Module A5STClosure.
Definition to_zero := STClosure.to_zero tm
  A5STNum.S100 A5STNum.T100 A5STNum.S000 A5Model.TZero.
End A5STClosure.

Module A5TenNum.
Definition pre := HalfTen.pre tm B A A5Model.LInc RInc.
Definition even_exit := HalfTen.even_exit tm B A A5Model.LInc RInc
  A5TenHalf.R101EvenEntry A5TenHalf.R111Scan.
Definition odd_exit := HalfTen.odd_exit tm B A RInc A5Boundary.ROv101Odd.
End A5TenNum.

Module A5TenClosure.
Definition to_zero := TenClosure.to_zero tm B A
  A5TenNum.pre A5TenNum.even_exit A5TenNum.odd_exit.
End A5TenClosure.

Module A5INum.
Definition odd := HalfI.odd tm B A A5Normal.normal_LInc RInc A5Boundary.ROvOddRecover.
Definition even := HalfI.even tm B A A5Normal.normal_LInc RInc A5Boundary.ROvEvenAux.
End A5INum.

Module A5IClosure.
Definition small := IClosure.small tm B A A5INum.odd A5INum.even.
End A5IClosure.

Module A5Union.
Definition S_zero := PairUnion.S_zero tm B A A5Drain.S_even A5Drain.S_odd.
Definition J_zero := PairUnion.J_zero tm B A A5Drain.even A5Drain.odd.
End A5Union.

Module A5Return.
Import PairUnion Pair45Right.
Local Open Scope sym_scope.
Definition even_R_return := NormalReturn.even_R_return tm B A A5Model.RScan A5Drain.even.
Definition R_zero_full := NormalReturn.R_zero_full tm B A A5Model.RScan A5Drain.even.
Definition I_zero := NormalReturn.I_zero tm B A A5Model.RScan A5Drain.even.
Definition seed := ldh <* ld0 {{A}}> [1] *> rd0 *> rd1 *> 0inf.
Lemma init : Allowed B A seed /\ c0 -[tm]->* seed.
Proof.
  split.
  - unfold seed; apply Ordinary; eapply I_full with (n:=1%nat) (z:=2); try (cbn; lia).
    exact (RC_d0 1 _ (RC_d1 0 _ RC_zero)).
  - unfold seed; follow A5TenHalf.init.
    apply progress_evstep, (LOv _ 0).
Qed.
End A5Return.

Module A5TBoundary.
Definition TZeros := HalfTBoundary.TZeros tm A5Model.TZero.
Definition T100_zero_odd := HalfTBoundary.T100_zero_odd tm A
  A5Half.T100 A5Half.MarkedCarry A5ZeroBoundary.EHalfBoundary A5TenHalf.R111Scan.
End A5TBoundary.

Module A5Special.
Definition cap_plus_one := PairSpecial.cap_plus_one tm B A A5Boundary.ROvEvenAux
  A5STNum.S100 A5STNum.T100 A5STNum.S000 A5TBoundary.TZeros
  A5TBoundary.T100_zero_odd A5Return.R_zero_full.
End A5Special.

Module A5Saturated.
Definition full := Saturated.full tm B A A5Return.R_zero_full
  A5Return.even_R_return A5Capacity.even_capacity_cleanup A5Capacity.odd_capacity_entry
  A5Normal.normal_LInc RInc LOv A5Boundary.R1100Turn A5Capacity.saturated_one.
End A5Saturated.

Definition closed := PairClosure.nonhalt tm B A
  A5Return.I_zero A5IClosure.small A5Saturated.full A5Special.cap_plus_one
  A5TenClosure.to_zero A5Union.J_zero A5STClosure.to_zero A5Union.S_zero.
Theorem nonhalt : ~halts tm c0.
Proof.
  destruct A5Return.init as [HA HS].
  eapply multistep_nonhalt; [exact HS|apply closed; exact HA].
Qed.
End TM5.

(* A6 uses the literal L/R mirror of the user's machine. *)
Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC1LB_1LF1RD_0RE0RC_0LC---_1RA0LF").
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* A signal is (right-entry,left-return); lists are in execution order. *)
Definition P : list (DH0*DH0) := [((D,[]),(B,[]))].
Definition H : list (DH0*DH0) := [((C,[]),(F,[]))].
Definition U0 : list sym := [1;1;0;0;0].
Definition U1 : list sym := [1;1;1;0;0].
Definition d0 : list sym := [0;0;0;0].
Definition d1 : list sym := [1;0;0;0].
Definition d2 : list sym := [0;1;0;0].
Definition d3 : list sym := [1;1;0;0].

(* Finite-word interfaces: emitted calls must still be discharged by the
   eventual suffix proof.  In particular P11 does not assume their return. *)
Lemma P0 : segRLs tm P [] U0 U1.
Proof. unfold P,U0,U1; solve_segRLs. Qed.
Lemma P1 : segRLs tm P H U1 U0.
Proof. unfold P,H,U0,U1; solve_segRLs. Qed.
Lemma H0 : segRLs tm H [] d0 d1.
Proof. unfold H,d0,d1; solve_segRLs. Qed.
Lemma H1 : segRLs tm H [] d1 d2.
Proof. unfold H,d1,d2; solve_segRLs. Qed.
Lemma H2 : segRLs tm H [] d2 d3.
Proof. unfold H,d2,d3; solve_segRLs. Qed.
Lemma H3 : segRLs tm H H d3 d0.
Proof. unfold H,d3,d0; solve_segRLs. Qed.

(* The guarded terminal digit uses three cells, not four. *)
Lemma HT0 : segRLs tm H [] [0;0;0] [1;0;0].
Proof. unfold H; solve_segRLs. Qed.
Lemma HT1 : segRLs tm H [] [1;0;0] [0;1;0].
Proof. unfold H; solve_segRLs. Qed.
Lemma HT2 : segRLs tm H [] [0;1;0] [1;1;0].
Proof. unfold H; solve_segRLs. Qed.

(* Physical wiring of the unfinished binary call stack, arbitrary contexts. *)
Lemma StackEnter l r:
  l {{D}}> [1;1] *> r -->+ l <* <[0;1] {{D}}> r.
Proof. es. Qed.
Lemma StackFirst l r:
  l <* <[0;1] <{{B}} r -->+ l <* <[1;1] {{D}}> r.
Proof. es. Qed.
Lemma StackLast l r:
  l <* <[1;1] <{{B}} r -->+ l <{{B}} [1;1] *> r.
Proof. es. Qed.

(* Segment interfaces used directly by Longitudinal.BCR.Incs.
   Left-side segment words are stored nearest-first: physical 01 is <[0;1]. *)
Lemma FrameEnter : segRR tm (D,[]) (D,[]) [1;1] <[0;1].
Proof. solve_seg. Qed.
Lemma FrameNext : segLR tm (B,[]) (D,[]) <[0;1] [1;1].
Proof. solve_seg. Qed.
Lemma FrameDone : segLL tm (B,[]) (B,[]) [1;1] [1;1].
Proof. solve_seg. Qed.

(* Right-exit overflow; no claim that any enclosing P call has returned. *)
Lemma TerminalOverflow l r k:
  l {{D}}> U1 *> d3^^k *> [1;1;0;1] *> r -->+
  l <* <[1] <* <[1;0]^^(k*2+4) {{C}}> r.
Proof. unfold U1,d3; es. Qed.


(* Explicit finite windows, so the unread exterior remains arbitrary. *)
Lemma Reentry0 l r:
  l <* <[1;0;1;0;1;0] {{C}}> [0;0;0;0;0;0] *> r -->+
  l <* <[1;1;1] {{D}}> [1;1;0;0;0;1;0;0;0] *> r.
Proof. es. Qed.
Lemma Reentry1 l r:
  l <* <[1;0;1;0] {{C}}> [1;0;0;0] *> r -->+
  l <* <[1;1;1] {{D}}> U1 *> r.
Proof. unfold U1; es. Qed.
Lemma Restart0 l r:
  l <* <[0] <{{B}} [1] *> r -->+ l <* <[1;1] {{D}}> r.
Proof. es. Qed.
Lemma Restart11 l r:
  l <* <[0;1;1] <{{B}} r -->+ l <* <[1;1] {{D}}> [1] *> r.
Proof. es. Qed.

Module TM6Counter.
Open Scope nat_scope.

(* All numerical indices below are nat proof parameters.  No large numeral
   or exponentially long signal list is evaluated by computation. *)
Inductive RC : nat -> side -> Prop :=
| RC_zero : RC 0 (0inf)%sym
| RC_d0 n r : RC n r -> RC (4*n) (d0 *> r)
| RC_d1 n r : RC n r -> RC (1+4*n) (d1 *> r)
| RC_d2 n r : RC n r -> RC (2+4*n) (d2 *> r)
| RC_d3 n r : RC n r -> RC (3+4*n) (d3 *> r).

Lemma RC_zero_unique r : RC 0 r -> r=(0inf)%sym.
Proof.
  intro Hrc. remember 0 as n eqn:En.
  induction Hrc; try lia.
  - reflexivity.
  - assert (n=0) by lia. subst n.
    rewrite IHHrc by reflexivity.
    unfold d0. st; reflexivity.
Qed.

Lemma RC_unique n r r' : RC n r -> RC n r' -> r=r'.
Proof.
  intros Hrc. revert r'. induction Hrc; intros r' Hr'.
  { symmetry. now apply RC_zero_unique. }
  all: inversion Hr'; subst; try lia.
  all: try (assert (n=0) by lia; subst n;
    rewrite (RC_zero_unique _ Hrc); unfold d0; st; reflexivity).
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma RInc n r : RC n r ->
  exists r', RC (S n) r' /\ sideRLs tm H r r'.
Proof.
  intro Hrc. induction Hrc.
  - exists (d1 *> (0inf)%sym). split.
    + change (RC (1+4*0) (d1 *> (0inf)%sym)). constructor; constructor.
    + assert (Ez : d0 *> (0inf)%sym = (0inf)%sym) by (unfold d0; st; reflexivity).
      rewrite <-Ez at 1.
      eapply segRLs_sideRLs_concat; [apply H0|constructor].
  - exists (d1 *> r). split.
    + replace (S (4*n)) with (1+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H0|constructor].
  - exists (d2 *> r). split.
    + replace (S (1+4*n)) with (2+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H1|constructor].
  - exists (d3 *> r). split.
    + replace (S (2+4*n)) with (3+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H2|constructor].
  - destruct IHHrc as [r' [Hr' Hstep]]. exists (d0 *> r'). split.
    + replace (S (3+4*n)) with (4*S n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H3|exact Hstep].
Qed.

Inductive NC : nat -> side -> Prop :=
| NC_0 n r : RC n r -> NC (2*n) (U0 *> r)
| NC_1 n r : RC n r -> NC (1+2*n) (U1 *> r).

Lemma NC_unique n r r' : NC n r -> NC n r' -> r=r'.
Proof.
  intros Hrc Hr'. inversion Hrc; inversion Hr'; subst; try lia;
    assert (n0=n1) by lia; subst n1; f_equal; eapply RC_unique; eauto.
Qed.

Lemma NormalInc n r : NC n r ->
  exists r', NC (S n) r' /\ sideRLs tm P r r'.
Proof.
  intro Hrc. destruct Hrc as [n r Hrc|n r Hrc].
  - exists (U1 *> r). split.
    + replace (S (2*n)) with (1+2*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply P0|constructor].
  - destruct (RInc _ _ Hrc) as [r' [Hr' Hstep]].
    exists (U0 *> r'). split.
    + replace (S (1+2*n)) with (2*S n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply P1|exact Hstep].
Qed.

Lemma NormalAdds_ex q n r : NC n r ->
  exists r', NC (n+q) r' /\ sideRLs tm (P^^q) r r'.
Proof.
  revert n r. induction q; intros n r Hrc.
  - exists r. split; [replace (n+0) with n by lia; exact Hrc|constructor].
  - destruct (NormalInc _ _ Hrc) as [r1 [Hrc1 Hstep]].
    destruct (IHq _ _ Hrc1) as [r2 [Hrc2 Hsteps]].
    exists r2. split.
    + replace (n+S q) with (S n+q) by lia. exact Hrc2.
    + cbn [lpow]. eapply sideRLs_trans; eauto.
Qed.

Lemma NormalAdds q n r r' :
  NC n r -> NC (n+q) r' -> sideRLs tm (P^^q) r r'.
Proof.
  intros Hrc Hr'. destruct (NormalAdds_ex q n r Hrc) as [r2 [Hr2 Hsteps]].
  assert (r2=r') by (eapply NC_unique; eauto). now subst.
Qed.

(* A fixed k-digit four-cell prefix followed by one three-cell digit.
   The exterior tail is arbitrary and is never assumed to be blank. *)
Inductive FC (tail:side) : nat -> nat -> side -> Prop :=
| FC_t0 : FC tail 0 0 ([0;0;0] *> tail)%sym
| FC_t1 : FC tail 0 1 ([1;0;0] *> tail)%sym
| FC_t2 : FC tail 0 2 ([0;1;0] *> tail)%sym
| FC_t3 : FC tail 0 3 ([1;1;0] *> tail)%sym
| FC_d0 k n r : FC tail k n r -> FC tail (S k) (4*n) (d0 *> r)
| FC_d1 k n r : FC tail k n r -> FC tail (S k) (1+4*n) (d1 *> r)
| FC_d2 k n r : FC tail k n r -> FC tail (S k) (2+4*n) (d2 *> r)
| FC_d3 k n r : FC tail k n r -> FC tail (S k) (3+4*n) (d3 *> r).


Lemma FC_unique tail k n r r' :
  FC tail k n r -> FC tail k n r' -> r=r'.
Proof.
  intros Hfc. revert r'. induction Hfc; intros r' Hr';
    inversion Hr'; subst; try lia; try reflexivity.
  all: assert (n=n0) by lia; subst n0; f_equal; eauto.
Qed.

Lemma FiniteRInc tail k n r :
  FC tail k n r -> S n<4^(S k) ->
  exists r', FC tail k (S n) r' /\ sideRLs tm H r r'.
Proof.
  intro Hfc. induction Hfc; intro Hbound.
  - exists ([1;0;0] *> tail)%sym. split; [constructor|].
    eapply segRLs_sideRLs_concat; [apply HT0|constructor].
  - exists ([0;1;0] *> tail)%sym. split; [constructor|].
    eapply segRLs_sideRLs_concat; [apply HT1|constructor].
  - exists ([1;1;0] *> tail)%sym. split; [constructor|].
    eapply segRLs_sideRLs_concat; [apply HT2|constructor].
  - cbn in Hbound. lia.
  - exists (d1 *> r). split.
    + replace (S (4*n)) with (1+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H0|constructor].
  - exists (d2 *> r). split.
    + replace (S (1+4*n)) with (2+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H1|constructor].
  - exists (d3 *> r). split.
    + replace (S (2+4*n)) with (3+4*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H2|constructor].
  - assert (Hsmall : S n<4^(S k)) by (cbn [Nat.pow] in *; lia).
    destruct (IHHfc Hsmall) as [r' [Hr' Hstep]]. exists (d0 *> r'). split.
    + replace (S (3+4*n)) with (4*S n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply H3|exact Hstep].
Qed.

Inductive FNC (tail:side) (k:nat) : nat -> side -> Prop :=
| FNC_0 n r : FC tail k n r -> FNC tail k (2*n) (U0 *> r)
| FNC_1 n r : FC tail k n r -> FNC tail k (1+2*n) (U1 *> r).


Lemma FNC_unique tail k n r r' :
  FNC tail k n r -> FNC tail k n r' -> r=r'.
Proof.
  intros Hfc Hr'. inversion Hfc; inversion Hr'; subst; try lia;
    assert (n0=n1) by lia; subst n1; f_equal; eapply FC_unique; eauto.
Qed.

Lemma FiniteInc tail k n r :
  FNC tail k n r -> S n<2*4^(S k) ->
  exists r', FNC tail k (S n) r' /\ sideRLs tm P r r'.
Proof.
  intros Hfc Hbound. destruct Hfc as [n r Hfc|n r Hfc].
  - exists (U1 *> r). split.
    + replace (S (2*n)) with (1+2*n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply P0|constructor].
  - assert (Hsmall : S n<4^(S k)) by lia.
    destruct (FiniteRInc _ _ _ _ Hfc Hsmall) as [r' [Hr' Hstep]].
    exists (U0 *> r'). split.
    + replace (S (1+2*n)) with (2*S n) by lia. now constructor.
    + eapply segRLs_sideRLs_concat; [apply P1|exact Hstep].
Qed.

Lemma FiniteAdds_ex tail k q n r :
  FNC tail k n r -> n+q<2*4^(S k) ->
  exists r', FNC tail k (n+q) r' /\ sideRLs tm (P^^q) r r'.
Proof.
  revert n r. induction q; intros n r Hfc Hbound.
  - exists r. split; [replace (n+0) with n by lia; exact Hfc|constructor].
  - assert (Hfirst : S n<2*4^(S k)) by lia.
    destruct (FiniteInc _ _ _ _ Hfc Hfirst) as [r1 [Hfc1 Hstep]].
    assert (Hrest : S n+q<2*4^(S k)) by lia.
    destruct (IHq _ _ Hfc1 Hrest) as [r2 [Hfc2 Hsteps]].
    exists r2. split.
    + replace (n+S q) with (S n+q) by lia. exact Hfc2.
    + cbn [lpow]. eapply sideRLs_trans; eauto.
Qed.

Lemma FiniteAdds tail k q n r r' :
  FNC tail k n r -> FNC tail k (n+q) r' ->
  n+q<2*4^(S k) -> sideRLs tm (P^^q) r r'.
Proof.
  intros Hfc Hr' Hbound.
  destruct (FiniteAdds_ex tail k q n r Hfc Hbound) as [r2 [Hr2 Hsteps]].
  assert (r2=r') by (eapply FNC_unique; eauto). now subst.
Qed.

End TM6Counter.

Module TM6Frames.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

(* Bits are low-bit first, hence also nearest-to-head first on the left.
   A physical frame x1 is stored as [1;x].  No hidden reversal is used. *)
Definition bval (b:bool) : nat := if b then 1 else 0.
Definition bit (b:bool) : sym := if b then 1 else 0.
Fixpoint value (bs:list bool) : nat :=
  match bs with [] => 0 | b::bs => bval b + 2*value bs end.
Fixpoint Frame (bs:list bool) : list sym :=
  match bs with [] => [] | b::bs => [1;bit b] ++ Frame bs end.
Fixpoint inc (bs:list bool) : list bool :=
  match bs with
  | [] => []
  | false::bs => true::bs
  | true::bs => false::inc bs
  end.
Definition Back : list (DH0*DH0) := [((B,[]),(D,[]))].

Lemma Frame_app xs ys : Frame (xs++ys)=Frame xs++Frame ys.
Proof. induction xs; cbn [app Frame]; [reflexivity|rewrite IHxs; reflexivity]. Qed.
Lemma value_app xs ys : value (xs++ys)=value xs+2^length xs*value ys.
Proof.
  induction xs as [|b xs IH]; [cbn; lia|].
  destruct b; cbn [app value bval length Nat.pow]; rewrite IH; nia.
Qed.
Lemma value_zeros m : value (repeat false m)=0%nat.
Proof. induction m; cbn [repeat value bval]; lia. Qed.

Lemma value_bound bs : value bs < 2^length bs.
Proof. induction bs as [|b bs IH]; [cbn; lia|destruct b; cbn [value bval length Nat.pow]; lia]. Qed.
Lemma inc_length bs : length (inc bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity|destruct b; cbn; congruence]. Qed.
Lemma value_inc bs : value bs+1 < 2^length bs -> value (inc bs)=value bs+1.
Proof.
  induction bs as [|b bs IH]; [cbn; lia|].
  destruct b; cbn [value inc bval length Nat.pow]; intros H; [rewrite IH; lia|lia].
Qed.
Lemma value_injective xs ys :
  length xs=length ys -> value xs=value ys -> xs=ys.
Proof.
  revert ys; induction xs as [|b xs IH]; intros [|c ys] Hl Hv; cbn in Hl; try discriminate; [reflexivity|].
  destruct b,c; cbn [value bval] in Hv; try lia; f_equal; apply IH; lia.
Qed.
Lemma value_ones m : value (repeat true m)+1=2^m.
Proof. induction m; cbn [repeat value bval Nat.pow]; lia. Qed.
Lemma Frame_ones m : Frame (repeat true m)=[1;1]^^m.
Proof. induction m; cbn [repeat Frame bit lpow]; [reflexivity|rewrite IHm; reflexivity]. Qed.
Lemma Frame_zeros m : Frame (repeat false m)=<[0;1]^^m.
Proof. induction m; cbn [repeat Frame bit lpow]; [reflexivity|rewrite IHm; reflexivity]. Qed.

Lemma FrameInc bs : value bs+1 < 2^length bs ->
  segLR tm (B,[]) (D,[]) (Frame bs) (Frame (inc bs)).
Proof.
  induction bs as [|b bs IH]; [cbn; lia|].
  destruct b; intros H.
  - assert (Hb:value bs+1 < 2^length bs) by (cbn [value bval length Nat.pow] in H; lia).
    specialize (IH Hb); unfold segLR in *; intros l r; cbn [Frame bit inc to_DH_config]; st.
    follow100 StackLast; follow IH; follow100 StackEnter; finish.
  - unfold segLR; intros l r; cbn [Frame bit inc to_DH_config]; st.
    apply progress_evstep, StackFirst.
Qed.

(* This is the general same-width walk, not only a zero/all-one special case.
   The target's upper bound follows from its bool-list representation. *)
Lemma FrameWalk q xs ys :
  length xs=length ys -> value xs+q=value ys ->
  segLRs tm (Back^^q) (Frame xs) (Frame ys).
Proof.
  revert xs ys; induction q as [|q IH]; intros xs ys Hl Hv.
  - assert (xs=ys) by (apply value_injective; auto; lia).
    subst; constructor.
  - assert (Hb:value xs+1 < 2^length xs).
    { pose proof (value_bound ys) as Hbound; rewrite <-Hl in Hbound; lia. }
    change (segLRs tm (((B,[]),(D,[]))::Back^^q) (Frame xs) (Frame ys)).
    econstructor; [apply FrameInc; exact Hb|].
    apply IH; [rewrite inc_length; exact Hl|rewrite value_inc; lia].
Qed.

Lemma FrameToLast q bs : value bs+q+1=2^length bs ->
  segLRs tm (Back^^q) (Frame bs) ([1;1]^^length bs).
Proof.
  intro H; rewrite <-Frame_ones; apply FrameWalk.
  - rewrite repeat_length; reflexivity.
  - pose proof (value_ones (length bs)); lia.
Qed.

(* Pair each actual right-side return with one weak left-frame advance.
   This RR loop stops at the next leaf entrance, not at a P return. *)
Lemma WalkCalls q w w' r r' :
  segLRs tm (Back^^q) w w' -> sideRLs tm (P^^q) r r' ->
  forall l, l <* w {{D}}> r -->* l <* w' {{D}}> r'.
Proof.
  revert w w' r r'; induction q as [|q IH]; intros w w' r r' HL HR l.
  - inversion HL; inversion HR; subst; apply evstep_refl.
  - cbn [lpow Back P] in HL,HR.
    inversion HL as [|tm0 h1 h2 ls w0 wm w2 Hleft HLtail]; subst.
    inversion HR as [|h1 h2 r0 rm r2 ls Hright HRtail]; subst.
    unfold sideRL,to_DH_config in Hright; cbn in Hright.
    unfold segLR,to_DH_config in Hleft; cbn in Hleft.
    eapply evstep_trans; [apply progress_evstep, Hright|].
    eapply evstep_trans; [apply Hleft|].
    apply IH; assumption.
Qed.
Lemma Descend m l r :
  l {{D}}> [1;1]^^m *> r -->* l <* Frame (repeat false m) {{D}}> r.
Proof. rewrite Frame_zeros; es. Qed.
Lemma LastReturn m l r :
  l <* [1;1]^^m <{{B}} r -->* l <{{B}} [1;1]^^m *> r.
Proof. es. Qed.

Lemma calls_after_returns q :
  lrcons (D,[]) (Back^^q) (B,[]) = P^^(q+1).
Proof.
  unfold Back,P; replace q with (q+1-1) at 1 by lia.
  apply lrcons_lpow1; lia.
Qed.

(* Drain leaves the suffix representation abstract.  Its q+1 genuine P
   returns will be supplied by NormalAdds, not assumed of arbitrary tails. *)
Lemma Drain q bs l r r' :
  value bs+q+1=2^length bs -> sideRLs tm (P^^(q+1)) r r' ->
  l <* Frame bs {{D}}> r -->+ l <{{B}} [1;1]^^length bs *> r'.
Proof.
  intros Hv Hr; eapply progress_evstep_trans.
  - eapply (@sideRLs_segLRs_concat tm (Back^^q) (D,[]) (B,[])
      (Frame bs) ([1;1]^^length bs) r r'); [apply FrameToLast; exact Hv|].
    rewrite calls_after_returns; exact Hr.
  - apply LastReturn.
Qed.

Lemma Double q : segRLs tm (P^^q) (P^^(q*2)) [1;1] [1;1].
Proof.
  unfold P; eapply BCR.Incs; [apply FrameNext|apply FrameDone|apply FrameEnter].
Qed.
Lemma Multiplier n q :
  segRLs tm (P^^q) (P^^(q*2^n)) ([1;1]^^n) ([1;1]^^n).
Proof.
  revert q; induction n as [|n IH]; intros q.
  - cbn [lpow Nat.pow]; rewrite Nat.mul_1_r; apply segRLs_nil.
  - replace (q*2^S n) with ((q*2)*2^n) by (cbn [Nat.pow]; nia).
    cbn [lpow]; eapply segRLs_concat; [apply Double|apply IH].
Qed.
End TM6Frames.

(* Sparse-word parameters of the closed family. *)
Module Entry.
Definition bnat (b : bool) : nat := if b then 1 else 0.
Definition sparse (w : list bool) := flat_map (fun b : bool => if b then d1 else d0) w.
Definition doubled (w : list bool) := flat_map (fun b : bool => if b then d2 else d0) w.
Definition E (b : bool) (w : list bool) :=
  0inf <* [1;1] {{D}}> [1;1]^^(length w*2+3+bnat b) *>
  U0 *> sparse w *> [0;0;0] *> [1]^^(1+bnat b) *> 0inf.
Definition next_word (b : bool) (w : list bool) :=
  repeat false (length w+bnat b) ++ [true] ++ w ++ [false].
Fixpoint value (w : list bool) : nat := match w with
  | [] => 0 | b::w => bnat b+value w*4 end.
Close Scope sym.
Open Scope nat_scope.

Lemma value_bound w : value w < 4^length w.
Proof. induction w as [|b w IH]; cbn [value length Nat.pow]; [lia|destruct b; cbn [bnat]; lia]. Qed.
Lemma value_app u v : value (u++v) = value u+value v*4^length u.
Proof. induction u; cbn [value app length Nat.pow]; [lia|rewrite IHu; nia]. Qed.
Lemma value_zeroes n : value (repeat false n) = 0.
Proof. induction n; cbn [value repeat bnat]; lia. Qed.

Open Scope sym.
Lemma sparse_app u v : sparse (u++v) = sparse u++sparse v.
Proof. apply flat_map_app. Qed.
Lemma doubled_app u v : doubled (u++v) = doubled u++doubled v.
Proof. apply flat_map_app. Qed.

(* Physical zero insertion shifts only the sparse low part. This is NOT
   an unrestricted claim about shifting arbitrary base-four digits. *)
Lemma sparse_shift w : [0]++sparse w = doubled w++[0].
Proof.
  induction w as [|b w IH]; [reflexivity|].
  unfold sparse,doubled in *.
  destruct b; cbn [flat_map d0 d1 d2 app] in *; now rewrite IH.
Qed.

Lemma init : c0 -[tm]->* E false [true].
Proof. unfold E,bnat,sparse,U0,d0,d1; cbn; esx. Qed.
End Entry.

Import ListNotations.

Module TM6Bits.
Open Scope nat_scope.

(* Both bit lists here are least-significant/nearest-head first, exactly as
   in TM6Frames.  Entry.value is the separate base-four value of w. *)
Definition exit_bits (b:bool) (w:list bool) : list bool :=
  flat_map (fun d:bool => [true;negb d]) w ++ [true;true;true] ++
  repeat false (Entry.bnat b).

Lemma exit_bits_length b w :
  length (exit_bits b w)=length w*2+3+Entry.bnat b.
Proof.
  induction w; unfold exit_bits in *; cbn [flat_map app length] in *.
  - rewrite repeat_length. lia.
  - lia.
Qed.

Lemma exit_bits_value b w :
  2*Entry.value w+TM6Frames.value (exit_bits b w)+1=2*4^(S(length w)).
Proof.
  induction w as [|d w IH].
  - destruct b; reflexivity.
  - unfold exit_bits in *; destruct d;
      cbn [flat_map app Entry.value Entry.bnat TM6Frames.value TM6Frames.bval
           negb length Nat.pow] in *; lia.
Qed.

Definition reentry_radius (b:bool) (w:list bool) := length w*2+1+Entry.bnat b.
Definition reentry_bits (b:bool) (w:list bool) :=
  [true] ++ repeat false (reentry_radius b w) ++ [true] ++ exit_bits b w ++ [true].

Lemma reentry_bits_length b w :
  length (reentry_bits b w)=length w*4+7+Entry.bnat b*2.
Proof.
  unfold reentry_bits; repeat rewrite length_app.
  rewrite repeat_length, exit_bits_length; cbn [length].
  unfold reentry_radius. lia.
Qed.

Lemma reentry_bits_length_parts b w :
  length (reentry_bits b w)=reentry_radius b w+length(exit_bits b w)+3.
Proof.
  unfold reentry_bits; repeat rewrite length_app.
  rewrite repeat_length; cbn [length]; lia.
Qed.

Lemma reentry_bits_value b w :
  TM6Frames.value(reentry_bits b w)=1+2^(reentry_radius b w+1)*
    (1+2*TM6Frames.value(exit_bits b w)+2^(length(exit_bits b w)+1)).
Proof.
  unfold reentry_bits; repeat rewrite TM6Frames.value_app.
  rewrite TM6Frames.value_zeros, repeat_length.
  cbn [TM6Frames.value TM6Frames.bval length].
  replace (reentry_radius b w+1) with (S(reentry_radius b w)) by lia.
  replace (length(exit_bits b w)+1) with (S(length(exit_bits b w))) by lia.
  cbn [Nat.pow]. nia.
Qed.

(* A small symbolic bridge only; no large natural number is evaluated. *)
Lemma pow2_twice k : 2^(k*2)=4^k.
Proof.
  induction k; [reflexivity|].
  replace (S k*2) with (S(S(k*2))) by lia.
  cbn [Nat.pow]. rewrite IHk. lia.
Qed.

Lemma pow2_exit_length b k :
  2^(k*2+3+Entry.bnat b+1)=(1+Entry.bnat b)*4^(k+2).
Proof.
  destruct b; cbn [Entry.bnat].
  - replace (k*2+3+1+1) with (S((k+2)*2)) by lia.
    cbn [Nat.pow]. rewrite pow2_twice. lia.
  - replace (k*2+3+0+1) with ((k+2)*2) by lia.
    rewrite pow2_twice. lia.
Qed.

Definition drain_A b w := 4*Entry.value w+1+Entry.bnat b*4^(length w+2).
Definition drain_q b w := drain_A b w*2^(reentry_radius b w+1)-2.

Lemma exit_budget_identity b w :
  drain_A b w+2*TM6Frames.value(exit_bits b w)+1=2^(length(exit_bits b w)+1).
Proof.
  pose proof (exit_bits_value b w) as He.
  rewrite exit_bits_length, pow2_exit_length.
  unfold drain_A.
  replace (length w+2) with (S(S(length w))) by lia.
  cbn [Nat.pow] in *; destruct b; cbn [Entry.bnat] in *; lia.
Qed.

Lemma drain_budget b w :
  drain_q b w+TM6Frames.value(reentry_bits b w)+1=2^length(reentry_bits b w).
Proof.
  pose proof (exit_budget_identity b w) as Ha.
  pose proof (reentry_bits_value b w) as Hv.
  rewrite reentry_bits_length_parts.
  set (r:=reentry_radius b w) in *.
  set (n:=length(exit_bits b w)) in *.
  set (j:=TM6Frames.value(exit_bits b w)) in *.
  set (a:=drain_A b w) in *.
  assert (Hapos:1<=a) by (unfold a,drain_A; lia).
  assert (Hp:0<2^r) by lia.
  unfold drain_q; fold r a.
  replace (r+n+3) with ((r+1)+(n+2)) by lia.
  repeat rewrite Nat.pow_add_r.
  replace (r+1) with (S r) in * by lia.
  replace (n+1) with (S n) in * by lia.
  replace (n+2) with (S(S n)) by lia.
  cbn [Nat.pow] in *; nia.
Qed.

End TM6Bits.

Module TM6Reentry.
Import TM6Frames.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* Frame lists and every bare left word are nearest-cell first.  These
   bridges merely repackage the two already-proved finite reentry windows. *)
Lemma Reentry0Frames k bs:
  0inf <* [1;1] <* Frame bs <* [1] <* <[1;0]^^(k*2+4) {{C}}> 0inf -->+
  0inf <* Frame ([true] ++ repeat false (k*2+1) ++ [true] ++ bs ++ [true])
    {{D}}> U0 *> d1 *> 0inf.
Proof.
  applys_eq (Reentry0
    (0inf <* [1;1] <* Frame bs <* [1] <* <[1;0]^^(k*2+1)) 0inf);
    repeat rewrite Frame_app; repeat rewrite Frame_zeros; cbn [Frame bit U0 d1];
    st; simpl_rotate; reflexivity.
Qed.

Lemma Reentry1Frames k bs:
  0inf <* [1;1] <* Frame bs <* [1] <* <[1;0]^^(k*2+4) {{C}}> [1] *> 0inf -->+
  0inf <* Frame ([true] ++ repeat false (k*2+2) ++ [true] ++ bs ++ [true])
    {{D}}> U1 *> 0inf.
Proof.
  applys_eq (Reentry1
    (0inf <* [1;1] <* Frame bs <* [1] <* <[1;0]^^(k*2+2)) 0inf);
    repeat rewrite Frame_app; repeat rewrite Frame_zeros; cbn [Frame bit U1];
    st; simpl_rotate; reflexivity.
Qed.
End TM6Reentry.

Module TM6Cycle.
Import TM6Counter TM6Frames TM6Bits TM6Reentry.
Open Scope sym.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Lemma sparse_RC w : RC (Entry.value w) (Entry.sparse w *> 0inf).
Proof.
  induction w as [|b w IH]; [cbn [Entry.value Entry.sparse flat_map]; constructor|].
  destruct b; cbn [Entry.value Entry.bnat Entry.sparse flat_map]; rewrite Str_app_assoc;
    [applys_eq (RC_d1 _ _ IH)|applys_eq (RC_d0 _ _ IH)]; flia.
Qed.
Lemma doubled_RC w : RC (Entry.value w*2) (Entry.doubled w *> 0inf).
Proof.
  induction w as [|b w IH]; [cbn [Entry.value Entry.doubled flat_map]; constructor|].
  destruct b; cbn [Entry.value Entry.bnat Entry.doubled flat_map]; rewrite Str_app_assoc;
    [applys_eq (RC_d2 _ _ IH)|applys_eq (RC_d0 _ _ IH)]; flia.
Qed.

Lemma sparse_FC w tail :
  FC tail (length w) (Entry.value w) (Entry.sparse w *> [0;0;0] *> tail).
Proof.
  induction w as [|b w IH]; [cbn [Entry.value Entry.sparse flat_map length]; constructor|].
  destruct b; cbn [Entry.value Entry.bnat Entry.sparse flat_map length]; rewrite Str_app_assoc;
    [applys_eq (FC_d1 _ _ _ _ IH)|applys_eq (FC_d0 _ _ _ _ IH)]; flia.
Qed.

Lemma FC_last k tail :
  FC tail k (4^S k-1) (d3^^k *> [1;1;0] *> tail).
Proof.
  induction k; [cbn; constructor|].
  cbn [lpow]; rewrite Str_app_assoc.
  applys_eq (FC_d3 _ _ _ _ IHk); cbn [Nat.pow]; flia.
Qed.
Lemma FNC_last k tail :
  FNC tail k (2*4^S k-1) (U1 *> d3^^k *> [1;1;0] *> tail).
Proof. applys_eq (FNC_1 _ _ _ _ (FC_last k tail)); flia. Qed.

(* The last call really exits to C on the right; it is not counted as
   another P return. The remaining left frames are retained verbatim. *)
Lemma FirstExit n k v bs l x r :
  FNC ([1] *> r) k v x -> length bs=n ->
  v+TM6Frames.value bs+1=2*4^S k ->
  l {{D}}> [1;1]^^n *> x -->+
  l <* Frame bs <* <[1] <* <[1;0]^^(k*2+4) {{C}}> r.
Proof.
  intros Hx Hlen Hval.
  eapply evstep_progress_trans; [apply Descend|].
  eapply evstep_progress_trans.
  - eapply WalkCalls with (q:=TM6Frames.value bs) (w':=Frame bs)
      (r':=U1 *> d3^^k *> [1;1;0] *> [1] *> r).
    + apply FrameWalk; [now rewrite repeat_length|rewrite value_zeros; lia].
    + eapply FiniteAdds; [exact Hx| |lia].
      applys_eq (FNC_last k ([1] *> r)); flia.
  - applys_eq (TerminalOverflow (l <* Frame bs) r k); st; reflexivity.
Qed.

Lemma E_exit b w : Entry.E b w -->+
  0inf <* [1;1] <* Frame (exit_bits b w) <* [1]
    <* <[1;0]^^(length w*2+4) {{C}}> [1]^^Entry.bnat b *> 0inf.
Proof.
  unfold Entry.E.
  eapply FirstExit with (v:=2*Entry.value w).
  - cbn [lpow Nat.add]; apply FNC_0, sparse_FC.
  - apply exit_bits_length.
  - apply exit_bits_value.
Qed.

Definition reentry_right (b:bool) := if b then U1 *> 0inf else U0 *> d1 *> 0inf.
Lemma reentry_normal b : NC (2-Entry.bnat b) (reentry_right b).
Proof.
  destruct b; unfold reentry_right; cbn [Entry.bnat].
  - change (NC (1+2*0) (U1 *> 0inf)); constructor; constructor.
  - change (NC (2*(1+4*0)) (U0 *> d1 *> 0inf)); constructor; constructor; constructor.
Qed.

Lemma E_reentry b w : Entry.E b w -->+
  0inf <* Frame (reentry_bits b w) {{D}}> reentry_right b.
Proof.
  eapply progress_trans; [apply E_exit|].
  destruct b; unfold reentry_right,reentry_bits,reentry_radius; cbn [Entry.bnat lpow];
    [applys_eq (Reentry1Frames (length w) (exit_bits true w))|
     applys_eq (Reentry0Frames (length w) (exit_bits false w))]; flia.
Qed.

Lemma E_drain b w : exists r,
  NC ((2-Entry.bnat b)+(drain_q b w+1)) r /\
  Entry.E b w -->+ 0inf <{{B}} [1;1]^^(length w*4+7+Entry.bnat b*2) *> r.
Proof.
  destruct (NormalAdds_ex (drain_q b w+1) _ _ (reentry_normal b)) as [r [Hn Hr]].
  exists r; split; [exact Hn|].
  eapply progress_trans; [apply E_reentry|].
  rewrite <-reentry_bits_length.
  apply Drain with (q:=drain_q b w); [pose proof (drain_budget b w); lia|exact Hr].
Qed.
End TM6Cycle.

Module TM6Target.
Import TM6Counter TM6Bits.
Open Scope sym.

(* Arbitrary normal high digits can follow either finite sparse encoding. *)
Lemma sparse_with_tail_RC (t:list bool) (n:nat) (r:side) :
  RC n r -> RC (Entry.value t+n*4^length t) (Entry.sparse t *> r).
Proof.
  intros Hr; induction t as [|b t IH].
  - cbn [Entry.value Entry.sparse flat_map length Nat.pow].
    applys_eq Hr; flia.
  - destruct b; cbn [Entry.value Entry.bnat Entry.sparse flat_map length Nat.pow];
      rewrite Str_app_assoc;
      [applys_eq (RC_d1 _ _ IH)|applys_eq (RC_d0 _ _ IH)]; flia.
Qed.

Lemma doubled_with_tail_RC (t:list bool) (n:nat) (r:side) :
  RC n r -> RC (2*Entry.value t+n*4^length t) (Entry.doubled t *> r).
Proof.
  intros Hr; induction t as [|b t IH].
  - cbn [Entry.value Entry.doubled flat_map length Nat.pow].
    applys_eq Hr; flia.
  - destruct b; cbn [Entry.value Entry.bnat Entry.doubled flat_map length Nat.pow];
      rewrite Str_app_assoc;
      [applys_eq (RC_d2 _ _ IH)|applys_eq (RC_d0 _ _ IH)]; flia.
Qed.

Close Scope sym.
Open Scope nat_scope.

Definition core (b:bool) (w:list bool) :=
  repeat false (length w+Entry.bnat b) ++ [true] ++ w.

Lemma core_length b w :
  length (core b w)=length w*2+1+Entry.bnat b.
Proof.
  unfold core; repeat rewrite length_app; rewrite repeat_length; cbn; lia.
Qed.

Lemma next_word_core b w : Entry.next_word b w=core b w++[false].
Proof. unfold Entry.next_word,core; repeat rewrite app_assoc; reflexivity. Qed.

Lemma core_value b w :
  Entry.value (core b w)=(4*Entry.value w+1)*4^(length w+Entry.bnat b).
Proof.
  unfold core; repeat rewrite Entry.value_app.
  rewrite Entry.value_zeroes,repeat_length.
  cbn [Entry.value Entry.bnat length Nat.pow]; nia.
Qed.


(* All powers below keep their symbolic exponents.  The positive capacity
   removes the two-unit truncating subtraction in drain_q. *)
Lemma drain_joint_value b w :
  (2-Entry.bnat b)+(drain_q b w+1)=
  drain_A b w*2^(reentry_radius b w+1)+1-Entry.bnat b.
Proof.
  assert (Ha:1<=drain_A b w) by (unfold drain_A; lia).
  assert (Hp:0<2^reentry_radius b w) by lia.
  unfold drain_q.
  replace (reentry_radius b w+1) with (S(reentry_radius b w)) by lia.
  cbn [Nat.pow]; destruct b; cbn [Entry.bnat] in *; nia.
Qed.

Lemma drain_core_value b w :
  (2-Entry.bnat b)+(drain_q b w+1)=
  if b then 2*(Entry.value (core b w)+4^(length (core b w)+1))
       else 1+4*Entry.value (core b w).
Proof.
  rewrite drain_joint_value; destruct b; rewrite core_value, ?core_length;
    unfold drain_A,reentry_radius; cbn [Entry.bnat].
  - assert (Hp2:2^(length w*2+1+1+1)=2*4^(length w+1)).
    { replace (length w*2+1+1+1) with (S((length w+1)*2)) by lia.
      cbn [Nat.pow]; now rewrite pow2_twice. }
    assert (Hp4:4^(length w*2+1+1+1)=4^(length w+2)*4^(length w+1)).
    { replace (length w*2+1+1+1) with ((length w+2)+(length w+1)) by lia.
      apply Nat.pow_add_r. }
    rewrite Hp2,Hp4; nia.
  - replace (length w*2+1+0+1) with ((length w+1)*2) by lia.
    rewrite pow2_twice.
    replace (length w+1) with (S(length w)) by lia.
    cbn [Nat.pow]; repeat rewrite Nat.add_0_r; nia.
Qed.

Open Scope sym.
Definition outer_right (b:bool) (t:list bool) : side :=
  if b then U0 *> Entry.sparse t *> d0 *> d1 *> 0inf
       else U1 *> Entry.doubled t *> 0inf.

Lemma outer_right_false_NC t :
  NC (1+4*Entry.value t) (outer_right false t).
Proof.
  unfold outer_right.
  applys_eq (NC_1 _ _ (TM6Cycle.doubled_RC t)); flia.
Qed.

Lemma outer_right_true_NC t :
  NC (2*(Entry.value t+4^(length t+1))) (outer_right true t).
Proof.
  assert (Hr:RC 4 (d0 *> d1 *> 0inf)).
  { change (RC (4*(1+4*0)) (d0 *> d1 *> 0inf)); repeat constructor. }
  unfold outer_right.
  applys_eq (NC_0 _ _ (sparse_with_tail_RC t 4 _ Hr)).
  replace (length t+1) with (S(length t)) by lia.
  cbn [Nat.pow]; flia.
Qed.

Lemma drain_target_NC b w :
  NC ((2-Entry.bnat b)+(drain_q b w+1)) (outer_right b (core b w)).
Proof.
  rewrite drain_core_value; destruct b;
    [apply outer_right_true_NC|apply outer_right_false_NC].
Qed.

End TM6Target.

Module TM6Outer.
Import TM6Counter TM6Frames TM6Cycle TM6Target.
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(* All lower calls are discharged by the normal counter; this is a genuine
   positive return, with the entire exterior left side unchanged. *)
Lemma Batch n v l r r' : NC v r -> NC (v+2^n) r' ->
  l {{D}}> [1;1]^^n *> r -->+ l <{{B}} [1;1]^^n *> r'.
Proof.
  intros Hr Hr'.
  pose proof (Multiplier n 1) as Hmul.
  replace (1*2^n) with (2^n) in Hmul by lia.
  cbn [lpow] in Hmul; rewrite app_nil_r in Hmul.
  apply (@sideRLs_1 tm (D,[]) (B,[]) _ _).
  eapply segRLs_sideRLs_concat; [exact Hmul|].
  eapply NormalAdds; eassumption.
Qed.

(* The four restart windows use a real blank immediately outside the
   fixed two-one left boundary.  The suffix r remains arbitrary. *)
Lemma Shift t r : Entry.doubled t *> [0] *> r = [0] *> Entry.sparse t *> r.
Proof. rewrite <-Str_app_assoc, <-Entry.sparse_shift; reflexivity. Qed.

Lemma Blank0 n t r :
  0inf <{{B}} [1;1]^^(n+1) *> U0 *> Entry.sparse t *> r -->+
  0inf <* [1;1] {{D}}> [1;1]^^n *> U1 *> Entry.doubled t *> [0] *> r.
Proof.
  rewrite Shift.
  applys_eq (Restart0 0inf ([1] *> [1;1]^^n *> U0 *> Entry.sparse t *> r));
    unfold U0,U1; st; simpl_rotate; reflexivity.
Qed.

Lemma Blank1 n t r :
  0inf <{{B}} [1;1]^^(n+1) *> U1 *> Entry.doubled t *> [0] *> r -->+
  0inf <* [1;1] {{D}}> [1;1]^^(n+1) *> U0 *> Entry.sparse t *> r.
Proof.
  rewrite Shift.
  applys_eq (Restart0 0inf ([1] *> [1;1]^^n *> U1 *> [0] *> Entry.sparse t *> r));
    unfold U0,U1; st; simpl_rotate; reflexivity.
Qed.

Lemma Boundary0 n t r :
  0inf <* [1;1] <{{B}} [1;1]^^n *> U0 *> Entry.sparse t *> r -->+
  0inf <* [1;1] {{D}}> [1;1]^^n *> U1 *> Entry.doubled t *> [0] *> r.
Proof.
  rewrite Shift.
  applys_eq (Restart11 0inf ([1;1]^^n *> U0 *> Entry.sparse t *> r));
    unfold U0,U1; st; simpl_rotate; reflexivity.
Qed.

Lemma Boundary1 n t r :
  0inf <* [1;1] <{{B}} [1;1]^^n *> U1 *> Entry.doubled t *> [0] *> r -->+
  0inf <* [1;1] {{D}}> [1;1]^^(n+1) *> U0 *> Entry.sparse t *> r.
Proof.
  rewrite Shift.
  applys_eq (Restart11 0inf ([1;1]^^n *> U1 *> [0] *> Entry.sparse t *> r));
    unfold U0,U1; st; simpl_rotate; reflexivity.
Qed.

Lemma pow_batch4 n : 2^(n*2+4)=16*4^n.
Proof. rewrite Nat.pow_add_r, TM6Bits.pow2_twice; cbn; nia. Qed.
Lemma pow_batch5 n : 2^(n*2+5)=32*4^n.
Proof. rewrite Nat.pow_add_r, TM6Bits.pow2_twice; cbn; nia. Qed.

(* Two ordinary returns, with the two intervening short real-blank
   restarts.  No upper bound on t's length or numerical value is used. *)
Lemma Outer0 t :
  0inf <{{B}} [1;1]^^(length t*2+5) *> U1 *> Entry.doubled t *> 0inf -->+
  Entry.E true (t++[false]).
Proof.
  eapply progress_trans.
  { applys_eq (Blank1 (length t*2+4) t 0inf); st; reflexivity. }
  replace (length t*2+4+1) with (length t*2+5) by lia.
  eapply progress_trans.
  { eapply Batch with (v:=2*Entry.value t)
      (r':=U0 *> Entry.sparse t *> d0 *> d0 *> d1 *> 0inf).
    - apply NC_0, sparse_RC.
    - applys_eq (NC_0 _ _ (sparse_with_tail_RC t 16 _
        (RC_d0 _ _ (RC_d0 _ _ (RC_d1 _ _ RC_zero))))).
      rewrite pow_batch5; nia. }
  eapply progress_trans.
  { applys_eq (Boundary0 (length t*2+5) (t++[false;false;true]) 0inf);
      rewrite ?Entry.sparse_app, ?Entry.doubled_app;
      cbn [Entry.sparse Entry.doubled flat_map]; unfold d0,d1,d2; st; reflexivity. }
  eapply progress_trans.
  { eapply Batch with (v:=1+2*(2*Entry.value t+32*4^length t))
      (r':=U1 *> Entry.doubled t *> d0 *> d0 *> d3 *> 0inf).
    - apply NC_1.
      applys_eq (doubled_with_tail_RC t 32 _
        (RC_d0 _ _ (RC_d0 _ _ (RC_d2 _ _ RC_zero))));
        rewrite Entry.doubled_app; cbn [Entry.doubled flat_map]; unfold d0,d2; st; reflexivity.
    - applys_eq (NC_1 _ _ (doubled_with_tail_RC t 48 _
        (RC_d0 _ _ (RC_d0 _ _ (RC_d3 _ _ RC_zero))))).
      rewrite pow_batch5; nia. }
  applys_eq (Boundary1 (length t*2+5) (t++[false]) ([0;0;0] *> [1;1] *> 0inf));
    unfold Entry.E; rewrite ?Entry.doubled_app, ?length_app;
    cbn [Entry.doubled flat_map length Entry.bnat lpow]; unfold d0,d3; st;
    try reflexivity; f_equal; lia.
Qed.

(* The other phase needs just one ordinary return. *)
Lemma Outer1 t :
  0inf <{{B}} [1;1]^^(length t*2+5) *> U0 *> Entry.sparse t *> d0 *> d1 *> 0inf -->+
  Entry.E false (t++[false]).
Proof.
  eapply progress_trans.
  { applys_eq (Blank0 (length t*2+4) t (d0 *> d1 *> 0inf)); st; reflexivity. }
  eapply progress_trans.
  { eapply Batch with (v:=1+2*(2*Entry.value t+8*4^length t))
      (r':=U1 *> Entry.doubled t *> d0 *> d0 *> d1 *> 0inf).
    - apply NC_1.
      applys_eq (doubled_with_tail_RC t 8 _
        (RC_d0 _ _ (RC_d2 _ _ RC_zero))); unfold d0,d1,d2; st; reflexivity.
    - applys_eq (NC_1 _ _ (doubled_with_tail_RC t 16 _
        (RC_d0 _ _ (RC_d0 _ _ (RC_d1 _ _ RC_zero))))).
      rewrite pow_batch4; nia. }
  applys_eq (Boundary1 (length t*2+4) (t++[false]) ([0;0;0] *> [1] *> 0inf));
    unfold Entry.E; rewrite ?Entry.doubled_app, ?length_app;
    cbn [Entry.doubled flat_map length Entry.bnat lpow]; unfold d0,d1; st;
    try reflexivity; f_equal; lia.
Qed.

End TM6Outer.

Import TM6Counter TM6Cycle TM6Target TM6Outer.
Open Scope sym.

Lemma E_outer b w : Entry.E b w -[tm]->+
  0inf <{{B}} [1;1]^^(2*length (core b w)+5) *> outer_right b (core b w).
Proof.
  destruct (E_drain b w) as [r [Hn Hstep]].
  assert (r=outer_right b (core b w)) by
    (eapply NC_unique; [exact Hn|apply drain_target_NC]).
  subst r.
  applys_eq Hstep; rewrite core_length; flia.
Qed.

Lemma E_step b w : Entry.E b w -[tm]->+ Entry.E (negb b) (Entry.next_word b w).
Proof.
  eapply progress_trans; [apply E_outer|].
  rewrite next_word_core.
  destruct b; cbn [negb outer_right];
    [applys_eq (Outer1 (core true w))|applys_eq (Outer0 (core false w))]; flia.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply Entry.init|].
  apply (progress_nonhalt_simple tm _ (fun '(b,w) => Entry.E b w) (false,[true])).
  intros [b w]; exists (negb b,Entry.next_word b w); apply E_step.
Qed.
End TM6.

(* A7: ternary counter bounds and the original machine. *)
(* Shared: SOCPair7Ternary.v/Pair7Ternary. *)
Module Pair7Ternary.
Local Open Scope sym_scope.
Definition e0 : list sym := [0;0;0].
Definition e1 : list sym := [1;1;0].
Definition e2 : list sym := [0;1;0].
Local Open Scope nat_scope.

Inductive TC (tail:side) : nat -> nat -> side -> Prop :=
| TC_nil : TC tail 0 0 tail
| TC_d0 h v r : TC tail h v r -> TC tail (S h) (v*3) (e0 *> r)
| TC_d1 h v r : TC tail h v r -> TC tail (S h) (1+v*3) (e1 *> r)
| TC_d2 h v r : TC tail h v r -> TC tail (S h) (2+v*3) (e2 *> r).

Lemma TC_bound tail h v r : TC tail h v r -> v<3^h.
Proof. intro H; induction H; cbn [Nat.pow]; lia. Qed.

Lemma TC_unique tail h v r s : TC tail h v r -> TC tail h v s -> r=s.
Proof.
  intro H; revert s; induction H; intros s Hs;
    inversion Hs; subst; try lia; try reflexivity.
  all: assert (v=v0) by lia; subst v0; f_equal; eauto.
Qed.

Lemma TC_zero tail h : TC tail h 0 (e0^^h *> tail).
Proof.
  induction h; cbn [lpow]; [constructor|].
  rewrite Str_app_assoc; change (TC tail (S h) (0*3) (e0 *> e0^^h *> tail)).
  now constructor.
Qed.

Lemma TC_full tail h : TC tail h (3^h-1) (e2^^h *> tail).
Proof.
  induction h; cbn [lpow Nat.pow]; [constructor|].
  rewrite Str_app_assoc.
  replace (3*3^h-1) with (2+(3^h-1)*3)
    by (pose proof (Nat.pow_nonzero 3 h ltac:(lia)); lia).
  now constructor.
Qed.

Lemma TC_zero_unique tail h r : TC tail h 0 r -> r=e0^^h *> tail.
Proof. intro H; eapply TC_unique; [exact H|apply TC_zero]. Qed.

Lemma TC_full_unique tail h r : TC tail h (3^h-1) r -> r=e2^^h *> tail.
Proof. intro H; eapply TC_unique; [exact H|apply TC_full]. Qed.

(* The first non-two digit and the actual incremented word, with no digit map. *)
Lemma TC_carry tail h v r : TC tail h v r -> S v<3^h ->
  exists j b q s, h=j+S b /\ TC tail b q s /\
  ((r=e2^^j *> e0 *> s /\ TC tail h (S v) (e0^^j *> e1 *> s)) \/
   (r=e2^^j *> e1 *> s /\ TC tail h (S v) (e0^^j *> e2 *> s))).
Proof.
  intro H; induction H; intro Hb.
  - cbn in Hb; lia.
  - exists 0,h,v,r; split; [lia|]; split; [exact H|]; left; split; [reflexivity|].
    change (TC tail (S h) (1+v*3) (e1 *> r)); now constructor.
  - exists 0,h,v,r; split; [lia|]; split; [exact H|]; right; split; [reflexivity|].
    change (TC tail (S h) (2+v*3) (e2 *> r)); now constructor.
  - assert (Hv:S v<3^h) by (cbn [Nat.pow] in Hb; lia).
    destruct (IHTC Hv) as [j [b [q [s [Hh [Hs Hc]]]]]].
    exists (S j),b,q,s; split; [lia|]; split; [exact Hs|].
    destruct Hc as [[Er Hn]|[Er Hn]]; [left|right]; split.
    all: cbn [lpow]; rewrite Str_app_assoc.
    + now rewrite Er.
    + replace (S (2+v*3)) with (S v*3) by lia; now constructor.
    + now rewrite Er.
    + replace (S (2+v*3)) with (S v*3) by lia; now constructor.
Qed.

(* The first nonzero digit, retaining both the high counter and its value. *)
Lemma TC_positive tail h v r : TC tail h v r -> 0<v ->
  exists j b q s, h=j+S b /\ TC tail b q s /\
  ((r=e0^^j *> e1 *> s /\ v=3^j*(1+q*3)) \/
   (r=e0^^j *> e2 *> s /\ v=3^j*(2+q*3))).
Proof.
  intro H; induction H; intro Hv; [lia| | |].
  - assert (Hp:0<v) by lia.
    destruct (IHTC Hp) as [j [b [q [s [Hh [Hs Hc]]]]]].
    exists (S j),b,q,s; split; [lia|]; split; [exact Hs|].
    destruct Hc as [[Er Ev]|[Er Ev]]; [left|right]; split.
    + cbn [lpow]; rewrite Str_app_assoc; now rewrite Er.
    + cbn [Nat.pow]; nia.
    + cbn [lpow]; rewrite Str_app_assoc; now rewrite Er.
    + cbn [Nat.pow]; nia.
  - exists 0,h,v,r; split; [lia|]; split; [exact H|]; left; split; [reflexivity|cbn; lia].
  - exists 0,h,v,r; split; [lia|]; split; [exact H|]; right; split; [reflexivity|cbn; lia].
Qed.

End Pair7Ternary.

(* Shared: SOCPair7Bounds.v/Pair7Bounds. *)
Module Pair7Bounds.
Local Open Scope nat_scope.

Lemma pow6 i : 6^i=2^i*3^i.
Proof. rewrite <- Nat.pow_mul_l; reflexivity. Qed.

Lemma pow_pos b i : 0<b -> 0<b^i.
Proof. intro H; apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia. Qed.

Lemma pow_mono b i j : 0<b -> i<=j -> b^i<=b^j.
Proof. intros Hb Hij; apply Nat.pow_le_mono_r; lia. Qed.

(* A single zero/nonzero read has deficit at most 2*d+8*6^a+1.
   After the first nonzero trit, the valuation a is at most the age i. *)
Lemma deficit_next A i a d d' :
  a<=i -> d+1<=2^i*A+2*6^i -> d'<=2*d+8*6^a+1 ->
  d'+1<=2^(1+i)*A+2*6^(1+i).
Proof.
  intros Ha Hd Hstep; assert (6^a<=6^i) by (apply pow_mono; lia).
  cbn [Nat.pow Nat.add]; nia.
Qed.

Lemma deficit_guard C A i k d :
  k+d=C*2^i -> d+1<=2^i*A+2*6^i -> A+6*3^i<=C ->
  4*6^i<k.
Proof.
  intros Hsum Hd HC; rewrite pow6 in *.
  assert (0<2^i) by (apply pow_pos; lia); nia.
Qed.

(* D3: arbitrary trits after the odd deficit 3. *)
Lemma deficit3_budget C h i :
  i<=h -> 3*3^h<=C -> 2+6*3^i<=4*C.
Proof.
  intros Hi HC; assert (3^i<=3^h) by (apply pow_mono; lia).
  assert (0<3^i) by (apply pow_pos; lia); lia.
Qed.

(* D26: the first nonzero trit is at j, followed by t arbitrary trits.
   This stronger integral bound removes division from the informal estimate. *)
Lemma deficit26_budget C j t A :
  3*3^(j+1+t)<=C -> A+6<=36*3^j ->
  A+6*3^t<=4*C.
Proof.
  intros HC HA; rewrite !Nat.pow_add_r in HC; cbn [Nat.pow] in HC.
  assert (0<3^j) by (apply pow_pos; lia).
  assert (0<3^t) by (apply pow_pos; lia); nia.
Qed.

Lemma deficit26_budget_scaled C j t q A :
  q<=t -> 3*3^(j+1+t)<=C -> A+6<=36*3^j ->
  2^(j+1)*A+6*3^q<=2^(j+1)*(4*C).
Proof.
  intros Hq HC HA; pose proof (deficit26_budget C j t A HC HA).
  assert (3^q<=3^t) by (apply pow_mono; lia).
  assert (0<2^(j+1)) by (apply pow_pos; lia); nia.
Qed.

(* The exact all-zero prefix, with b=10 for initial deficit 2 and b=6
   for initial deficit 6, is d+2^i*b=12*6^i. *)
Lemma zeros_next i b d :
  d+2^i*b=12*6^i ->
  (2*d+8*6^(1+i))+2^(1+i)*b=12*6^(1+i).
Proof. intro H; cbn [Nat.pow Nat.add]; nia. Qed.

Lemma zeros_guard C h i b k d :
  i<h -> 3*3^h<=C -> 0<b ->
  k+d=4*C*2^i -> d+2^i*b=12*6^i ->
  4*6^(1+i)<k.
Proof.
  intros Hi HC Hb Hsum Hd.
  assert (3^(1+i)<=3^h) by (apply pow_mono; lia).
  rewrite pow6 in Hd; cbn [Nat.pow Nat.add]; rewrite pow6.
  cbn [Nat.pow Nat.add] in H.
  assert (0<2^i) by (apply pow_pos; lia); nia.
Qed.

Lemma zeros_end C h b k d :
  3*3^h<=C -> k+d=4*C*2^h -> d+2^h*b=12*6^h ->
  2^h*b<=k.
Proof. intros HC Hsum Hd; rewrite pow6 in Hd; nia. Qed.

(* 2^n is never divisible by 3.  No large modulus or primality theorem
   is needed in either of the two-overflow repairs. *)
Lemma pow2_mod3 n : 2^n mod 3=1 \/ 2^n mod 3=2.
Proof.
  induction n; [left; reflexivity|].
  change ((2*2^n) mod 3=1 \/ (2*2^n) mod 3=2).
  rewrite Nat.mul_mod by lia; destruct IHn as [-> | ->]; cbn; auto.
Qed.

Lemma pow2_remainder n : exists q, 2^n=1+q*3 \/ 2^n=2+q*3.
Proof.
  destruct (pow2_mod3 n) as [H|H]; exists (2^n/3);
    pose proof (Nat.div_mod (2^n) 3 ltac:(lia)); [left|right]; lia.
Qed.

(* The remainder after the second traversal is structural, not random.
   These two interfaces give an incrementable nonzero trit word whenever
   the low remainder is 2, including the smallest h. *)
Lemma hard0_remainder n h :
  6*3^h+1<=2^n -> 2^n+2<9*3^h ->
  exists q,
    (2^n+1-6*3^h=q*3 /\ 1<=q /\ q<3^h) \/
    (2^n+1-6*3^h=2+q*3 /\ 1+q<3^h).
Proof.
  intros Hlo Hhi; destruct (pow2_remainder n) as [t [H|H]].
  - exists (t-2*3^h); right; split; lia.
  - exists (1+t-2*3^h); left; repeat split; lia.
Qed.

Lemma hard2_remainder n h :
  6*3^h<=2^n -> 2^n+1<9*3^h ->
  exists q,
    (2^n-6*3^h=1+q*3 /\ q<3^h) \/
    (2^n-6*3^h=2+q*3 /\ 1+q<3^h).
Proof.
  intros Hlo Hhi; destruct (pow2_remainder n) as [t [H|H]];
    exists (t-2*3^h); [left|right]; split; lia.
Qed.

Lemma normal_budget a u :
  4*6^a<2^a*(1+u*2) <-> 2*3^a<=u.
Proof. rewrite pow6; assert (0<2^a) by (apply pow_pos; lia); nia. Qed.

(* Bounds at the exit of the pure-power Blank repair. *)
Lemma power_exit m a : 1<=a -> 3^a<=2^m ->
  11<=2^(a+1)*(2^(m+1)-2*3^a+3)-1 /\
  2^(a+1)*(2^(m+1)-2*3^a+3)-1<=2^(m+a+2)-13.
Proof.
  intros Ha Hm.
  assert (H2:4<=2^(a+1)) by (change (2^2<=2^(a+1)); apply pow_mono; lia).
  assert (H3:3<=3^a) by (change (3^1<=3^a); apply pow_mono; lia).
  replace (m+a+2) with ((a+1)+(m+1)) by lia.
  rewrite (Nat.pow_add_r 2 (a+1) (m+1)), (Nat.pow_add_r 2 m 1).
  cbn [Nat.pow]; split; nia.
Qed.

End Pair7Bounds.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RE_---1LD_0LE0LD_1RA0RF_1LD1RB").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* <[1] {{B}}> r) (at level 30).

(* The right windows used below; all outside tape is untouched. *)
Lemma R100 l r:
  l |> [1;0;0] *> r -->+ l <* <[1;1;1] |> r.
Proof. es. Qed.
Lemma R111 l r:
  l |> [1;1;1] *> r -->+ l <* <[1;1;0] |> r.
Proof. es. Qed.
Lemma R110 l r:
  l |> [1;1;0] *> r -->+ l <| [1;1;1] *> r.
Proof. es. Qed.
Lemma R0 l r:
  l |> [0] *> r -->+ l <{{D}} [1;1] *> r.
Proof. es. Qed.

(* Left carry and scan, with arbitrary unread environments. *)
Lemma LInc l r a:
  l <* <[1;1;0] <* <[1;1;1]^^a <| r -->+
  l <* <[1;1;1] <* <[1;1;0]^^a |> r.
Proof. es. Qed.

(* The actual one-bit sentinel at the blank left boundary. *)
Lemma LBlank1 r n:
  0inf <* <[1] <* <[1;1;1]^^n <| r -->+
  0inf <* <[1] <* <[1;1;0]^^n |> [1] *> r.
Proof. es. Qed.
(* Width and value of the left binary budget, without choosing a concrete
   representation for its unread outer tape.  The low digit is at the head. *)
Inductive LC (outer:side) : nat -> nat -> side -> Prop :=
| LC_nil : LC outer 0 0 outer
| LC_d0 n k l : LC outer n k l ->
    LC outer (1+n) (k*2) (l <* <[1;1;1])
| LC_d1 n k l : LC outer n k l ->
    LC outer (1+n) (1+k*2) (l <* <[1;1;0]).

Lemma LC_bound outer n k l : LC outer n k l -> k<2^n.
Proof. intro H; induction H; cbn [Nat.add Nat.pow]; lia. Qed.

Lemma LC_unique outer n k l l' :
  LC outer n k l -> LC outer n k l' -> l=l'.
Proof.
  intro H; revert l'; induction H; intros l' H';
    inversion H'; subst; try lia; try reflexivity.
  all: assert (k=k0) by lia; subst; f_equal; eauto.
Qed.

Lemma LC_zeros outer n k l a : LC outer n k l ->
  LC outer (n+a) (k*2^a) (l <* <[1;1;1]^^a).
Proof.
  intro H; induction a; cbn [lpow Nat.pow].
  - applys_eq H; flia.
  - applys_eq (LC_d0 _ _ _ _ IHa); flia.
Qed.

Lemma LC_ones outer n k l a : LC outer n k l ->
  LC outer (n+a) ((1+k)*2^a-1) (l <* <[1;1;0]^^a).
Proof.
  intro H; induction a; cbn [lpow Nat.pow].
  - applys_eq H; flia.
  - applys_eq (LC_d1 _ _ _ _ IHa); flia.
Qed.

Lemma LC_zero outer n : LC outer n 0 (outer <* <[1;1;1]^^n).
Proof. applys_eq (LC_zeros outer 0 0 outer n (LC_nil outer)); flia. Qed.
Lemma LC_full outer n :
  LC outer n (2^n-1) (outer <* <[1;1;0]^^n).
Proof. applys_eq (LC_ones outer 0 0 outer n (LC_nil outer)); flia. Qed.
Lemma LC_zero_unique outer n l :
  LC outer n 0 l -> l=outer <* <[1;1;1]^^n.
Proof. intro H; eapply LC_unique; [exact H|apply LC_zero]. Qed.
Lemma LC_positive_split outer n k l : LC outer n k l -> 0<k ->
  exists a m u hi, n=m+1+a /\ k=2^a*(1+u*2) /\
    LC outer m u hi /\ l=hi <* <[1;1;0] <* <[1;1;1]^^a.
Proof.
  intros H; induction H; intro Hk; try lia.
  - destruct IHLC as [a [m [u [hi [En [Ek [HC El]]]]]]]; [lia|].
    exists (1+a),m,u,hi; subst; cbn [lpow Nat.add Nat.pow].
    repeat split; try nia; try assumption; st; reflexivity.
  - exists 0%nat,n,k,l; cbn [lpow Nat.pow]; repeat split; try lia; assumption.
Qed.

Lemma LC_borrow outer n k l : LC outer n (1+k) l ->
  exists l', LC outer n k l' /\ forall r, l <| r -->+ l' |> r.
Proof.
  intro H; destruct (LC_positive_split _ _ _ _ H ltac:(lia))
    as [a [m [u [hi [En [Ek [HC El]]]]]]].
  exists (hi <* <[1;1;1] <* <[1;1;0]^^a); split.
  - applys_eq (LC_ones _ _ _ _ a (LC_d0 _ _ _ _ HC)); nia.
  - intro r; subst l; apply LInc.
Qed.

Lemma LC_R100 outer n k l r : LC outer n k l ->
  exists l', LC outer (1+n) (k*2) l' /\
    l |> [1;0;0] *> r -->+ l' |> r.
Proof. intro H; eexists; split; [apply LC_d0,H|apply R100]. Qed.
Lemma LC_R111 outer n k l r : LC outer n k l ->
  exists l', LC outer (1+n) (1+k*2) l' /\
    l |> [1;1;1] *> r -->+ l' |> r.
Proof. intro H; eexists; split; [apply LC_d1,H|apply R111]. Qed.

Lemma LC_R110 outer n k l r : LC outer n k l -> 0<k ->
  exists l', LC outer (1+n) (k*2-1) l' /\
    l |> [1;1;0] *> r -->+ l' |> r.
Proof.
  intros H Hk; assert (HC:LC outer n (1+(k-1)) l) by (applys_eq H; lia).
  destruct (LC_borrow _ _ _ _ HC) as [l' [H' HB]].
  exists (l' <* <[1;1;0]); split.
  - applys_eq (LC_d1 _ _ _ _ H'); lia.
  - follow10 R110; follow100 (HB ([1;1;1] *> r)); es.
Qed.

Definition outer := 0inf <* <[1].

Lemma LC_Lzero n l r : LC outer n 0 l ->
  exists l', LC outer n (2^n-1) l' /\ l <| r -->+ l' |> [1] *> r.
Proof.
  intro H; apply LC_zero_unique in H; subst l.
  eexists; split; [apply LC_full|unfold outer; apply LBlank1].
Qed.
Lemma DReturn l r a :
  l <* <[1;1;0] <* <[1;1;1]^^a <{{D}} r -->+
  l <| [1;1] *> [0;0;0]^^a *> r.
Proof. es. Qed.

Lemma LC_Dpositive outer m u hi a r : LC outer m (1+u) hi ->
  exists l', LC outer m u l' /\
    hi <* <[1;1;0] <* <[1;1;1]^^a <{{D}} r -->+
    l' |> [1;1] *> [0;0;0]^^a *> r.
Proof.
  intro H; destruct (LC_borrow _ _ _ _ H) as [l' [HC HB]].
  exists l'; split; [exact HC|].
  follow10 DReturn; apply progress_evstep,HB.
Qed.

Lemma LC_Dpower m hi a r : LC outer m 0 hi ->
  exists l', LC outer m (2^m-1) l' /\
    hi <* <[1;1;0] <* <[1;1;1]^^a <{{D}} r -->+
    l' |> [1;1;1] *> [0;0;0]^^a *> r.
Proof.
  intro H; apply LC_zero_unique in H; subst hi.
  eexists; split; [apply LC_full|].
  unfold outer; follow10 DReturn; apply progress_evstep.
  applys_eq (LBlank1 ([1;1] *> [0;0;0]^^a *> r) m); st; reflexivity.
Qed.

Lemma init : exists l, LC outer 5 27 l /\ c0 -->* l |> 0inf.
Proof.
  eexists; split.
  - exact (LC_d1 _ _ _ _ (LC_d1 _ _ _ _ (LC_d0 _ _ _ _
      (LC_d1 _ _ _ _ (LC_d1 _ _ _ _ (LC_nil outer)))))).
  - unfold outer; esx.
Qed.

(* An explicit odd high part identifies the trailing zero budget digits. *)
Lemma LC_factor outer m a u l :
  LC outer (m+1+a) (2^a*(1+u*2)) l ->
  exists hi, LC outer m u hi /\ l=hi <* <[1;1;0] <* <[1;1;1]^^a.
Proof.
  revert l; induction a; intros l H.
  - assert (H0:LC outer (1+m) (1+u*2) l)
      by (applys_eq H; cbn [Nat.pow]; lia).
    inversion H0 as [|n k hi HC|n k hi HC]; subst; try lia.
    assert (k=u) by lia; subst k.
    exists hi; split; [assumption|st; reflexivity].
  - assert (H0:LC outer (1+(m+1+a)) ((2^a*(1+u*2))*2) l)
      by (applys_eq H; cbn [Nat.pow]; nia).
    inversion H0 as [|n k hi HC|n k hi HC]; subst; try lia.
    assert (k=2^a*(1+u*2)) by lia; subst k.
    destruct (IHa _ HC) as [hi' [HC' E]].
    exists hi'; split; [exact HC'|subst hi; st; reflexivity].
Qed.

Lemma LC_R0positive outer m a u l r :
  LC outer (m+1+a) (2^a*(1+(1+u)*2)) l ->
  exists l', LC outer m u l' /\
    l |> [0] *> r -->+ l' |> [1;1] *> [0;0;0]^^a *> [1;1] *> r.
Proof.
  intro H; destruct (LC_factor _ _ _ _ _ H) as [hi [HC E]].
  destruct (LC_Dpositive _ _ _ _ a ([1;1] *> r) HC) as [l' [HC' HS]].
  exists l'; split; [exact HC'|subst l; follow10 R0; apply progress_evstep,HS].
Qed.

Lemma LC_R0power m a l r : LC outer (m+1+a) (2^a) l ->
  exists l', LC outer m (2^m-1) l' /\
    l |> [0] *> r -->+ l' |> [1;1;1] *> [0;0;0]^^a *> [1;1] *> r.
Proof.
  intro H; assert (H0:LC outer (m+1+a) (2^a*(1+0*2)) l)
    by (applys_eq H; lia).
  destruct (LC_factor _ _ _ _ _ H0) as [hi [HC E]].
  destruct (LC_Dpower _ _ a ([1;1] *> r) HC) as [l' [HC' HS]].
  exists l'; split; [exact HC'|subst l; follow10 R0; apply progress_evstep,HS].
Qed.

(* SOCPair7Counting.v. *)
Module Pair7Counting.
Import Pair7Ternary.
Local Open Scope sym_scope.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

(* These finite word bridges stop before borrowing from the unknown left tape. *)
Lemma QLow l r : l |q> e0 *> r -->+ l <| [1;1;1;0;0] *> r.
Proof. unfold e0; apply R110. Qed.

Lemma QLowBack l r :
  l |> [1;1;1;0;0] *> r -->+ l <| [1;1;1;1;0] *> r.
Proof. es. Qed.

Lemma QCarry0 l r j :
  l |q> e1 *> e2^^j *> e0 *> r -->+
  l <| [1;1] *> e0^^(1+j) *> e1 *> r.
Proof. unfold e0,e1,e2; es. Qed.

Lemma QCarry1 l r j :
  l |q> e1 *> e2^^j *> e1 *> r -->+
  l <| [1;1] *> e0^^(1+j) *> e2 *> r.
Proof. unfold e0,e1,e2; es. Qed.

Lemma QCarryTail l r j :
  l |q> e1 *> e2^^j *> [1;1] *> r -->+
  l <| [1;1] *> e0^^(1+j) *> [0;1] *> r.
Proof. unfold e0,e1,e2; es. Qed.

Lemma QExit l r j :
  l |q> e1 *> e2^^j *> [0;1] *> r -->+
  l <* <[1;1;0] <* <[1;1;1]^^(1+j) |> [1] *> r.
Proof. unfold e1,e2; es. Qed.

Lemma Q0 outer n k l r : LC outer n (2+k) l ->
  exists l', LC outer n k l' /\ l |q> e0 *> r -->+ l' |q> e1 *> r.
Proof.
  intro H; destruct (LC_borrow outer n (1+k) l H) as [l1 [H1 S1]].
  destruct (LC_borrow _ _ _ _ H1) as [l2 [H2 S2]].
  exists l2; split; [exact H2|].
  follow10 QLow; follow100 (S1 ([1;1;1;0;0] *> r)); follow100 QLowBack.
  follow100 (S2 ([1;1;1;1;0] *> r)).
  unfold e1; finish.
Qed.

Lemma Q1 outer n k l r j : LC outer n (1+k) l ->
  exists l', LC outer n k l' /\
    l |q> e1 *> e2^^j *> e0 *> r -->+ l' |q> e0^^(1+j) *> e1 *> r.
Proof.
  intro H; destruct (LC_borrow _ _ _ _ H) as [l' [H' HS]].
  exists l'; split; [exact H'|]; follow10 QCarry0; apply progress_evstep,HS.
Qed.

Lemma Q2 outer n k l r j : LC outer n (1+k) l ->
  exists l', LC outer n k l' /\
    l |q> e1 *> e2^^j *> e1 *> r -->+ l' |q> e0^^(1+j) *> e2 *> r.
Proof.
  intro H; destruct (LC_borrow _ _ _ _ H) as [l' [H' HS]].
  exists l'; split; [exact H'|]; follow10 QCarry1; apply progress_evstep,HS.
Qed.

Lemma Q3 outer n k l r j : LC outer n (1+k) l ->
  exists l', LC outer n k l' /\
    l |q> e1 *> e2^^j *> [1;1] *> r -->+ l' |q> e0^^(1+j) *> [0;1] *> r.
Proof.
  intro H; destruct (LC_borrow _ _ _ _ H) as [l' [H' HS]].
  exists l'; split; [exact H'|]; follow10 QCarryTail; apply progress_evstep,HS.
Qed.

Lemma Q4 outer n k l r j : LC outer n k l ->
  exists l', LC outer (n+j+2) ((1+k*2)*2^(1+j)) l' /\
    l |q> e1 *> e2^^j *> [0;1] *> r -->+ l' |> [1] *> r.
Proof.
  intro H; eexists; split; [|apply QExit].
  applys_eq (LC_zeros _ _ _ _ (1+j) (LC_d1 _ _ _ _ H)); nia.
Qed.

(* A normal ternary increment debits exactly three units of left budget. *)
Lemma TC_next outer tail n k l h v r :
  LC outer n (3+k) l -> TC tail h v r -> S v<3^h ->
  exists l' r', LC outer n k l' /\ TC tail h (S v) r' /\
    l |q> e0 *> r -->+ l' |q> e0 *> r'.
Proof.
  intros Hl Hr Hb.
  destruct (TC_carry _ _ _ _ Hr Hb) as [j [b [q [s [Hh [Hs HC]]]]]].
  destruct (Q0 outer n (1+k) l r Hl) as [l1 [H1 S1]].
  destruct HC as [[Er Hn]|[Er Hn]]; subst r.
  - destruct (Q1 _ _ _ _ s j H1) as [l2 [H2 S2]].
    exists l2,(e0^^j *> e1 *> s); repeat split; try assumption.
    follow10 S1; applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
  - destruct (Q2 _ _ _ _ s j H1) as [l2 [H2 S2]].
    exists l2,(e0^^j *> e2 *> s); repeat split; try assumption.
    follow10 S1; applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
Qed.

Lemma TC_steps count outer tail n k l h v r :
  LC outer n (3*count+k) l -> TC tail h v r -> v+count<3^h ->
  exists l' r', LC outer n k l' /\ TC tail h (v+count) r' /\
    l |q> e0 *> r -->* l' |q> e0 *> r'.
Proof.
  gen k l v r; induction count; intros k l v r Hl Hr Hb.
  - exists l,r; repeat split; try (applys_eq Hr; lia); try assumption; apply evstep_refl.
  - assert (HC:LC outer n (3+(3*count+k)) l) by (applys_eq Hl; lia).
    destruct (TC_next _ _ _ _ _ _ _ _ HC Hr ltac:(lia)) as [l1 [r1 [H1 [T1 S1]]]].
    destruct (IHcount _ _ _ _ H1 T1 ltac:(lia)) as [l2 [r2 [H2 [T2 S2]]]].
    exists l2,r2; split; [exact H2|]; split; [applys_eq T2; lia|].
    follow100 S1; exact S2.
Qed.

Lemma TC_first outer n k l h v r tail :
  LC outer n (3*(3^h-v)+k) l -> TC ([1;1] *> tail) h v r ->
  exists l', LC outer n k l' /\
    l |q> e0 *> r -->+ l' |q> e0 *> e0^^h *> [0;1] *> tail.
Proof.
  intros Hl Hr; pose proof (TC_bound _ _ _ _ Hr) as Hb.
  assert (HC:LC outer n (3*(3^h-1-v)+(3+k)) l) by (applys_eq Hl; lia).
  destruct (TC_steps (3^h-1-v) _ _ _ _ _ _ _ _ HC Hr ltac:(lia))
    as [l1 [r1 [H1 [T1 S1]]]].
  replace (v+(3^h-1-v)) with (3^h-1) in T1 by lia.
  apply TC_full_unique in T1; subst r1.
  destruct (Q0 outer n (1+k) l1 (e2^^h *> [1;1] *> tail) H1) as [l2 [H2 S2]].
  destruct (Q3 _ _ _ _ tail h H2) as [l3 [H3 S3]].
  exists l3; split; [exact H3|].
  follow S1; follow10 S2; applys_eq (progress_evstep _ _ _ S3); st; reflexivity.
Qed.

Lemma TC_exit outer n k l h v r tail :
  LC outer n (3*(3^h-v)-1+k) l -> TC ([0;1] *> tail) h v r ->
  exists l', LC outer (n+h+2) ((1+k*2)*2^(1+h)) l' /\
    l |q> e0 *> r -->+ l' |> [1] *> tail.
Proof.
  intros Hl Hr; pose proof (TC_bound _ _ _ _ Hr) as Hb.
  assert (HC:LC outer n (3*(3^h-1-v)+(2+k)) l) by (applys_eq Hl; lia).
  destruct (TC_steps (3^h-1-v) _ _ _ _ _ _ _ _ HC Hr ltac:(lia))
    as [l1 [r1 [H1 [T1 S1]]]].
  replace (v+(3^h-1-v)) with (3^h-1) in T1 by lia.
  apply TC_full_unique in T1; subst r1.
  destruct (Q0 outer n k l1 (e2^^h *> [0;1] *> tail) H1) as [l2 [H2 S2]].
  destruct (Q4 _ _ _ _ tail h H2) as [l3 [H3 S3]].
  exists l3; split; [exact H3|].
  follow S1; follow10 S2; apply progress_evstep,S3.
Qed.

Lemma Q_return outer n k l h tail :
  LC outer n (2*3^(1+h)-1+k) l ->
  exists l', LC outer (n+h+2) ((1+k*2)*2^(1+h)) l' /\
    l |q> e0^^(1+h) *> [1;1] *> tail -->+ l' |> [1] *> tail.
Proof.
  intro Hl.
  assert (HC:LC outer n (3*(3^h-0)+(3*3^h-1+k)) l)
    by (applys_eq Hl; cbn [Nat.pow Nat.add]; pose proof (Nat.pow_nonzero 3 h); lia).
  destruct (TC_first _ _ _ _ _ _ _ tail HC (TC_zero _ h)) as [l1 [H1 S1]].
  assert (H2:LC outer n (3*(3^h-0)-1+k) l1) by (applys_eq H1; lia).
  destruct (TC_exit _ _ _ _ _ _ _ tail H2 (TC_zero _ h)) as [l2 [H3 S2]].
  exists l2; split; [exact H3|].
  applys_eq (progress_trans _ _ _ _ S1 S2); st; reflexivity.
Qed.

End Pair7Counting.

(* SOCPair7Low.v. *)
Module Pair7Low.
Import Pair7Ternary Pair7Counting.
Local Open Scope sym_scope.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

Lemma zero11 n l r : LC outer n 0 l ->
  exists l', LC outer (n+1) (2^(n+1)-1) l' /\
    l <| [1;1] *> r -->+ l' |> r.
Proof.
  intro H; destruct (LC_Lzero _ _ ([1;1] *> r) H) as [l1 [H1 S1]].
  destruct (LC_R111 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2; split.
  - applys_eq H2; try lia; rewrite Nat.pow_add_r; cbn [Nat.pow];
      pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia.
  - follow10 S1; apply progress_evstep,S2.
Qed.

Lemma clear0 n l r : LC outer n 0 l ->
  exists l', LC outer (n+2) (2^(n+2)-2) l' /\
    l |q> e0 *> r -->+ l' |> r.
Proof.
  intro H; destruct (zero11 _ _ ([1;0;0] *> r) H) as [l1 [H1 S1]].
  destruct (LC_R100 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2; split.
  - applys_eq H2; try lia; rewrite !Nat.pow_add_r; cbn [Nat.pow];
      pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia.
  - follow10 QLow; follow100 S1; apply progress_evstep,S2.
Qed.

Lemma clear1 n l r : LC outer n 1 l ->
  exists l', LC outer (n+2) (2^(n+2)-3) l' /\
    l |q> e0 *> r -->+ l' |> r.
Proof.
  intro H; destruct (LC_borrow outer n 0 l H) as [l1 [H1 S1]].
  destruct (zero11 _ _ ([1;1;0] *> r) H1) as [l2 [H2 S2]].
  assert (Hp:0<2^(n+1)-1) by
    (rewrite Nat.pow_add_r; cbn [Nat.pow]; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia).
  destruct (LC_R110 _ _ _ _ r H2 Hp) as [l3 [H3 S3]].
  exists l3; split.
  - applys_eq H3; try lia; rewrite !Nat.pow_add_r; cbn [Nat.pow];
      pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia.
  - follow10 QLow; follow100 (S1 ([1;1;1;0;0] *> r)); follow100 QLowBack.
    follow100 S2; apply progress_evstep,S3.
Qed.

Lemma clear2a tail n l h v r :
  LC outer n 2 l -> TC tail h v r -> S v<3^h ->
  exists l' r', LC outer (n+1) (2^(n+1)-1) l' /\ TC tail h (S v) r' /\
    l |q> e0 *> r -->+ l' |> e0 *> r'.
Proof.
  intros Hl Hr Hb.
  destruct (TC_carry _ _ _ _ Hr Hb) as [j [b [q [s [Hh [Hs HC]]]]]].
  destruct (Q0 outer n 0 l r Hl) as [l1 [H1 S1]].
  destruct HC as [[Er Hn]|[Er Hn]]; subst r.
  - destruct (zero11 _ _ (e0^^(1+j) *> e1 *> s) H1) as [l2 [H2 S2]].
    exists l2,(e0^^j *> e1 *> s); repeat split; try assumption.
    follow10 S1; follow100 QCarry0.
    applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
  - destruct (zero11 _ _ (e0^^(1+j) *> e2 *> s) H1) as [l2 [H2 S2]].
    exists l2,(e0^^j *> e2 *> s); repeat split; try assumption.
    follow10 S1; follow100 QCarry1.
    applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
Qed.

Lemma clear2_full n l h r tail :
  LC outer n 2 l -> TC ([1;1] *> tail) h (3^h-1) r ->
  exists l' r', LC outer (n+1) (2^(n+1)-1) l' /\
    TC ([0;1] *> tail) h 0 r' /\
    l |q> e0 *> r -->+ l' |> e0 *> r'.
Proof.
  intros Hl Hr; apply TC_full_unique in Hr; subst r.
  destruct (Q0 outer n 0 l (e2^^h *> [1;1] *> tail) Hl) as [l1 [H1 S1]].
  destruct (zero11 _ _ (e0^^(1+h) *> [0;1] *> tail) H1) as [l2 [H2 S2]].
  exists l2,(e0^^h *> [0;1] *> tail); split; [exact H2|].
  split; [apply TC_zero|].
  follow10 S1; follow100 QCarryTail.
  applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
Qed.

End Pair7Low.

(* SOCPair7Normal.v. *)
Module Pair7Normal.
Import Pair7Ternary Pair7Counting Pair7Bounds.

(* Both prefixes preserve the width and replace the first right zero by one.
   The even high budget is 2*3^a+v, exactly the normal-return guard. *)
Lemma OddPrefix outer m v l r : LC outer (1+m) (3+v*2) l ->
  exists l', LC outer (1+m) (1+v*2) l' /\
    l |> [0] *> r -->+ l' |> [1] *> r.
Proof.
  intro H; assert (HC:LC outer (m+1+0) (2^0*(1+(1+v)*2)) l)
    by (applys_eq H; cbn [Nat.pow]; lia).
  destruct (LC_R0positive _ _ _ _ _ r HC) as [l1 [H1 S1]].
  destruct (LC_R111 _ _ _ _ ([1] *> r) H1) as [l2 [H2 S2]].
  exists l2; split; [exact H2|].
  applys_eq (progress_trans _ _ _ _ S1 S2); st; reflexivity.
Qed.

Lemma EvenPrefix outer m h v l r :
  LC outer (m+h+2) (2^(1+h)*(1+(2*3^(1+h)+v)*2)) l ->
  exists l', LC outer (m+h+2) (2^(1+h)*(1+v*2)) l' /\
    l |> [0] *> r -->+ l' |> [1] *> r.
Proof.
  intro H; assert (HC:LC outer (m+1+(1+h))
    (2^(1+h)*(1+(1+(2*3^(1+h)-1+v))*2)) l).
  { applys_eq H; pose proof (pow_pos 3 (1+h) ltac:(lia)); nia. }
  destruct (LC_R0positive _ _ _ _ _ r HC) as [l1 [H1 S1]].
  destruct (Q_return _ _ _ _ h r H1) as [l2 [H2 S2]].
  exists l2; split; [applys_eq H2; nia|].
  unfold Pair7Ternary.e0 in S2.
  exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Odd000 outer m v l r : LC outer (1+m) (3+v*2) l ->
  exists l', LC outer (2+m) (2+v*4) l' /\
    l |> [0;0;0] *> r -->+ l' |> r.
Proof.
  intro H; destruct (OddPrefix _ _ _ _ ([0;0] *> r) H) as [l1 [H1 S1]].
  destruct (LC_R100 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2; split; [applys_eq H2; lia|].
  exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Even000 outer m h v l r :
  LC outer (m+h+2) (2^(1+h)*(1+(2*3^(1+h)+v)*2)) l ->
  exists l', LC outer (m+h+3) (2^(2+h)*(1+v*2)) l' /\
    l |> [0;0;0] *> r -->+ l' |> r.
Proof.
  intro H; destruct (EvenPrefix _ _ _ _ _ ([0;0] *> r) H) as [l1 [H1 S1]].
  destruct (LC_R100 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2; split; [applys_eq H2; cbn [Nat.pow Nat.add]; nia|].
  exact (progress_trans _ _ _ _ S1 S2).
Qed.

End Pair7Normal.

(* SOCPair7Repair.v. *)
Module Pair7Repair.
Import Pair7Ternary Pair7Counting Pair7Normal Pair7Low Pair7Bounds.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

Lemma FullRead n l r : 3<=2^n -> LC outer (n+1) (2^(n+1)-1) l ->
  exists l', LC outer (n+2) (2^(n+2)-6) l' /\
    l |> e0 *> r -->+ l' |> r.
Proof.
  intros Hn Hl.
  assert (HC:LC outer (1+n) (3+(2^n-2)*2) l).
  { applys_eq Hl; try lia; rewrite Nat.pow_add_r; cbn [Nat.pow]; lia. }
  destruct (Odd000 _ _ _ _ r HC) as [l' [H' HS]].
  exists l'; split; [|exact HS].
  applys_eq H'; try lia; rewrite Nat.pow_add_r; cbn [Nat.pow]; lia.
Qed.

Lemma clear2 tail n l h v r :
  LC outer n 2 l -> TC tail h v r -> S v<3^h ->
  exists l' r', LC outer (n+2) (2^(n+2)-6) l' /\
    TC tail h (S v) r' /\ l |q> e0 *> r -->+ l' |> r'.
Proof.
  intros Hl Hr Hv; pose proof (LC_bound _ _ _ _ Hl) as Hn.
  destruct (clear2a _ _ _ _ _ _ Hl Hr Hv) as [l1 [r1 [H1 [T1 S1]]]].
  destruct (FullRead n l1 r1 ltac:(lia) H1) as [l2 [H2 S2]].
  exists l2,r1; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma clear2_full n l h r tail :
  LC outer n 2 l -> TC ([1;1] *> tail) h (3^h-1) r ->
  exists l' r', LC outer (n+2) (2^(n+2)-6) l' /\
    TC ([0;1] *> tail) h 0 r' /\ l |q> e0 *> r -->+ l' |> r'.
Proof.
  intros Hl Hr; pose proof (LC_bound _ _ _ _ Hl) as Hn.
  destruct (Pair7Low.clear2_full _ _ _ _ _ Hl Hr) as [l1 [r1 [H1 [T1 S1]]]].
  destruct (FullRead n l1 r1 ltac:(lia) H1) as [l2 [H2 S2]].
  exists l2,r1; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

(* Both hard branches meet here with different remaining budgets k.
   No zero word is discarded: the old 10 suffix becomes the final 0110. *)
Lemma HardEntry n h k l :
  LC outer (n+h+2) (2^(1+h)*(1+(1+3*3^h+k)*2)) l ->
  exists l', LC outer n k l' /\
    l |> [0;1] *> 0inf -->+
    l' |q> e0 *> e0^^h *> [0;1;1;0] *> 0inf.
Proof.
  intro Hl.
  assert (HC:LC outer (n+1+(1+h)) (2^(1+h)*(1+(1+(3*3^h+k))*2)) l)
    by (applys_eq Hl; lia).
  destruct (LC_R0positive _ _ _ _ _ ([1;0] *> 0inf) HC) as [l1 [H1 S1]].
  assert (HC1:LC outer n (3*(3^h-0)+k) l1) by (applys_eq H1; lia).
  destruct (TC_first _ _ _ _ _ _ _ ([1;0] *> 0inf) HC1 (TC_zero _ h))
    as [l2 [H2 S2]].
  exists l2; split; [exact H2|].
  applys_eq (progress_trans _ _ _ _ S1 S2); unfold e0; st; reflexivity.
Qed.

End Pair7Repair.

(* SOCPair7Read.v. *)
Module Pair7Read.
Import Pair7Ternary Pair7Normal Pair7Bounds.

Definition cost (a:nat) : nat := match a with O => 4 | S h => 8*6^(S h) end.

Lemma cost_bounds a : 4<=cost a /\ cost a<=8*6^a.
Proof. destruct a; cbn [cost]; [lia|pose proof (pow_pos 6 (S a) ltac:(lia)); lia]. Qed.

Lemma LC_adic_width o n k l a u : LC o n k l ->
  k=2^a*(1+u*2) -> a<n.
Proof.
  intros Hl Hk; pose proof (LC_bound _ _ _ _ Hl).
  destruct (Nat.lt_ge_cases a n); [assumption|].
  assert (2^n<=2^a) by (apply pow_mono; lia).
  assert (0<2^a) by (apply pow_pos; lia); nia.
Qed.

(* Do the common return only once; the three final words are cheap scans. *)
Lemma ReadPrefix o n k l a u r : LC o n k l ->
  k=2^a*(1+u*2) -> 4*6^a<k ->
  exists l' p v, LC o n p l' /\ p=2^a*(1+v*2) /\
    2<=p /\ p*2+cost a=k*2 /\
    l |> [0] *> r -->+ l' |> [1] *> r.
Proof.
  intros Hl Hk Hg; pose proof (LC_adic_width _ _ _ _ _ _ Hl Hk) as Hn.
  destruct a as [|a].
  - cbn [Nat.pow] in Hk,Hg.
    assert (HC:LC o (1+(n-1)) (3+(u-1)*2) l) by (applys_eq Hl; lia).
    destruct (OddPrefix _ _ _ _ r HC) as [l' [H' HS]].
    exists l',(1+(u-1)*2),(u-1); split; [applys_eq H'; lia|].
    repeat split; try (cbn [cost Nat.pow]; lia); exact HS.
  - assert (Hu:2*3^(S a)<=u) by (apply (proj1 (normal_budget (S a) u)); lia).
    assert (HC:LC o ((n-2-a)+a+2)
      (2^(1+a)*(1+(2*3^(1+a)+(u-2*3^(1+a)))*2)) l).
    { applys_eq Hl; [lia|change (2^(S a)*(1+(2*3^(S a)+(u-2*3^(S a)))*2)=k); nia]. }
    destruct (EvenPrefix _ _ _ _ _ r HC) as [l' [H' HS]].
    exists l',(2^(1+a)*(1+(u-2*3^(1+a))*2)),(u-2*3^(1+a)).
    split; [applys_eq H'; lia|]; split; [reflexivity|].
    assert (Hp:2<=2^(1+a)) by (change (2^1<=2^(1+a)); apply pow_mono; lia).
    split; [nia|]; split; [|exact HS].
    change (2^(S a)*(1+(u-2*3^(S a))*2)*2+8*6^(S a)=k*2).
    rewrite (pow6 (S a)); nia.
Qed.

Lemma Read0 o n k l a u r : LC o n k l ->
  k=2^a*(1+u*2) -> 4*6^a<k ->
  exists l' k' u', LC o (1+n) k' l' /\
    k'=2^(1+a)*(1+u'*2) /\ k'+cost a=k*2 /\
    l |> e0 *> r -->+ l' |> r.
Proof.
  intros Hl Hk Hg.
  destruct (ReadPrefix _ _ _ _ _ _ ([0;0] *> r) Hl Hk Hg)
    as [l1 [p [v [H1 [Hp [Hpos [HE S1]]]]]]].
  destruct (LC_R100 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2,(p*2),v; split; [applys_eq H2; lia|].
  split; [cbn [Nat.pow Nat.add]; nia|]; split; [exact HE|].
  exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Read1 o n k l r : LC o n k l -> 2<=k ->
  exists l' k' u', LC o (1+n) k' l' /\
    k'=1+u'*2 /\ 3<=k' /\ k'+1=k*2 /\
    l |> e1 *> r -->+ l' |> r.
Proof.
  intros Hl Hk; destruct (LC_R110 _ _ _ _ r Hl ltac:(lia)) as [l' [H' HS]].
  exists l',(k*2-1),(k-1); split; [applys_eq H'; lia|].
  repeat split; try lia; exact HS.
Qed.

Lemma Read2 o n k l a u r : LC o n k l ->
  k=2^a*(1+u*2) -> 4*6^a<k ->
  exists l' k' u', LC o (1+n) k' l' /\
    k'=1+u'*2 /\ 3<=k' /\ k'+cost a+1=k*2 /\
    l |> e2 *> r -->+ l' |> r.
Proof.
  intros Hl Hk Hg.
  destruct (ReadPrefix _ _ _ _ _ _ ([1;0] *> r) Hl Hk Hg)
    as [l1 [p [v [H1 [Hp [Hpos [HE S1]]]]]]].
  destruct (LC_R110 _ _ _ _ r H1 ltac:(lia)) as [l2 [H2 S2]].
  exists l2,(p*2-1),(p-1); split; [applys_eq H2; lia|].
  repeat split; try lia; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Read011 o n k l a u r : LC o n k l ->
  k=2^a*(1+u*2) -> 4*6^a<k ->
  exists l' k' u', LC o (1+n) k' l' /\
    k'=1+u'*2 /\ 3<=k' /\ k'+cost a=k*2+1 /\
    l |> [0;1;1] *> r -->+ l' |> r.
Proof.
  intros Hl Hk Hg.
  destruct (ReadPrefix _ _ _ _ _ _ ([1;1] *> r) Hl Hk Hg)
    as [l1 [p [v [H1 [Hp [Hpos [HE S1]]]]]]].
  destruct (LC_R111 _ _ _ _ r H1) as [l2 [H2 S2]].
  exists l2,(1+p*2),p; split; [applys_eq H2; lia|].
  repeat split; try lia; exact (progress_trans _ _ _ _ S1 S2).
Qed.

End Pair7Read.

(* SOCPair7Scan.v. *)
Module Pair7Scan.
Import Pair7Ternary Pair7Read Pair7Bounds.
Local Open Scope sym_scope.

Inductive EndTail : side -> Prop :=
| End11 : EndTail ([1;1] *> 0inf)
| End01 : EndTail ([0;1] *> 0inf)
| End0110 : EndTail ([0;1;1;0] *> 0inf).

Inductive Trit : list sym -> Prop :=
| Trit0 : Trit e0 | Trit1 : Trit e1 | Trit2 : Trit e2.

Lemma trit_step w o n k l a u d r :
  Trit w -> LC o n k l -> k=2^a*(1+u*2) -> 4*6^a<k -> 1<=d ->
  exists l' k' d' a' u', LC o (1+n) k' l' /\
    k'+d'=2*(k+d) /\ 1<=d' /\ d'<=2*d+8*6^a+1 /\
    a'<=1+a /\ k'=2^a'*(1+u'*2) /\ l |> w *> r -->+ l' |> r.
Proof.
  intros Hw Hl Hk Hg Hd; pose proof (cost_bounds a) as Hc.
  destruct Hw.
  - destruct (Read0 _ _ _ _ _ _ r Hl Hk Hg) as [l' [k' [u' [HL [HK [HC HS]]]]]].
    exists l',k',(2*d+cost a),(1+a),u'; repeat split; try assumption; try lia.
  - assert (2<=k) by (pose proof (pow_pos 6 a ltac:(lia)); nia).
    destruct (Read1 _ _ _ _ r Hl H) as [l' [k' [u' [HL [HK [HP [HC HS]]]]]]].
    exists l',k',(2*d+1),0%nat,u'; repeat split; try assumption; try lia.
  - destruct (Read2 _ _ _ _ _ _ r Hl Hk Hg) as [l' [k' [u' [HL [HK [HP [HC HS]]]]]]].
    exists l',k',(2*d+cost a+1),0%nat,u'; repeat split; try assumption; try lia.
Qed.

Lemma terminal o n k l a u tail :
  EndTail tail -> LC o n k l -> k=2^a*(1+u*2) -> 4*6^a<k ->
  exists l' v, LC o (n+1) (3+v*2) l' /\ 6+v*2<=2^(n+1) /\
    l |> tail -->+ l' |> 0inf.
Proof.
  intros HE Hl Hk Hg; pose proof (LC_bound _ _ _ _ Hl) as Hb.
  pose proof (cost_bounds a) as Hc.
  assert (2<=k) by (pose proof (pow_pos 6 a ltac:(lia)); nia).
  destruct HE.
  - destruct (Read1 _ _ _ _ 0inf Hl H) as [l' [k' [u' [HL [HK [HP [HC HS]]]]]]].
    exists l',(u'-1); split; [applys_eq HL; lia|]; split.
    + rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
    + applys_eq HS; unfold e1; st; reflexivity.
  - destruct (Read2 _ _ _ _ _ _ 0inf Hl Hk Hg) as [l' [k' [u' [HL [HK [HP [HC HS]]]]]]].
    exists l',(u'-1); split; [applys_eq HL; lia|]; split.
    + rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
    + applys_eq HS; unfold e2; st; reflexivity.
  - destruct (Read011 _ _ _ _ _ _ 0inf Hl Hk Hg) as [l' [k' [u' [HL [HK [HP [HC HS]]]]]]].
    exists l',(u'-1); split; [applys_eq HL; lia|]; split.
    + rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
    + applys_eq HS; st; reflexivity.
Qed.

(* One arbitrary trit followed by a bounded continuation. *)
Lemma bounded_cons o C A h r w : Trit w ->
  (forall n k l i d a u,
    LC o n k l -> k=2^a*(1+u*2) -> a<=i -> k+d=C*2^i ->
    1<=d -> d+1<=2^i*A+2*6^i -> A+6*3^(i+h)<=C ->
    exists l' v, LC o (n+h+1) (3+v*2) l' /\
      6+v*2<=2^(n+h+1) /\ l |> r -->+ l' |> 0inf) ->
  forall n k l i d a u,
    LC o n k l -> k=2^a*(1+u*2) -> a<=i -> k+d=C*2^i ->
    1<=d -> d+1<=2^i*A+2*6^i -> A+6*3^(i+S h)<=C ->
    exists l' v, LC o (n+S h+1) (3+v*2) l' /\
      6+v*2<=2^(n+S h+1) /\ l |> w *> r -->+ l' |> 0inf.
Proof.
  intros Hw IH n k l i d a u Hl Hk Ha Hsum Hd Hdef HC.
  assert (Hci:A+6*3^i<=C) by
    (assert (3^i<=3^(i+S h)) by (apply pow_mono; lia); nia).
  pose proof (deficit_guard C A i k d Hsum Hdef Hci) as Hgi.
  assert (Hg:4*6^a<k) by
    (assert (6^a<=6^i) by (apply pow_mono; lia); nia).
  destruct (trit_step _ _ _ _ _ _ _ _ r Hw Hl Hk Hg Hd)
    as [l1 [k1 [d1 [a1 [u1 [HL [HS [HD [HB [HA [HK HT]]]]]]]]]]].
  assert (Hsum1:k1+d1=C*2^(1+i)) by (cbn [Nat.pow Nat.add]; nia).
  pose proof (deficit_next A i a d d1 Ha Hdef HB) as Hdef1.
  assert (HC1:A+6*3^((1+i)+h)<=C) by (replace (1+i+h) with (i+S h) by lia; exact HC).
  destruct (IH (1+n) k1 l1 (1+i) d1 a1 u1 HL HK ltac:(lia) Hsum1 HD Hdef1 HC1)
    as [l2 [v [HL2 [HB2 HT2]]]].
  exists l2,v; split; [applys_eq HL2; lia|]; split.
  - replace (n+S h+1) with (1+n+h+1) by lia; exact HB2.
  - exact (progress_trans _ _ _ _ HT HT2).
Qed.

Lemma bounded_scan o C A tail h v r : TC tail h v r -> EndTail tail ->
  forall n k l i d a u,
    LC o n k l -> k=2^a*(1+u*2) -> a<=i -> k+d=C*2^i ->
    1<=d -> d+1<=2^i*A+2*6^i -> A+6*3^(i+h)<=C ->
    exists l' q, LC o (n+h+1) (3+q*2) l' /\
      6+q*2<=2^(n+h+1) /\ l |> r -->+ l' |> 0inf.
Proof.
  intros Hr HE; induction Hr.
  - intros n k l i d a u Hl Hk Ha Hsum Hd Hdef HC.
    rewrite Nat.add_0_r in HC.
    pose proof (deficit_guard C A i k d Hsum Hdef HC) as Hgi.
    assert (Hg:4*6^a<k) by (assert (6^a<=6^i) by (apply pow_mono; lia); nia).
    replace (n+0+1) with (n+1) by lia.
    exact (terminal _ _ _ _ _ _ _ HE Hl Hk Hg).
  - apply bounded_cons; [constructor|exact IHHr].
  - apply bounded_cons; [constructor|exact IHHr].
  - apply bounded_cons; [constructor|exact IHHr].
Qed.

Lemma D3 n l h v r tail :
  LC outer (n+2) (2^(n+2)-3) l -> TC tail h v r -> EndTail tail ->
  3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HE HC; pose proof (pow_pos 3 h ltac:(lia)) as Hp.
  assert (Hpow:2^(n+2)=4*2^n) by (rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
  assert (Hk:2^(n+2)-3=2^0*(1+(2*2^n-2)*2)) by (cbn [Nat.pow]; nia).
  assert (Hsum:(2^(n+2)-3)+3=(4*2^n)*2^0) by (cbn [Nat.pow]; nia).
  assert (HB:2+6*3^(0+h)<=4*2^n) by (apply (deficit3_budget (2^n) h (0+h)); lia).
  destruct (bounded_scan outer (4*2^n) 2 _ _ _ _ Hr HE
    (n+2) _ l 0 3 0 (2*2^n-2) Hl Hk ltac:(lia) Hsum ltac:(lia) ltac:(cbn; lia) HB)
    as [l' [u [HL [HG HS]]]].
  exists l',u; split; [applys_eq HL; lia|]; split; [|exact HS].
  replace (n+h+3) with (n+2+h+1) by lia; exact HG.
Qed.

(* The all-zero prefix preserves an exact deficit and a known valuation. *)
Lemma zero_scan count o C b r : forall n k l i d u,
  LC o n k l -> k=2^(1+i)*(1+u*2) -> k+d=4*C*2^i ->
  d+2^i*b=12*6^i -> 1<=d -> 0<b -> 3*3^(i+count)<=C ->
  exists l' k' d' u', LC o (n+count) k' l' /\
    k'=2^(1+(i+count))*(1+u'*2) /\ k'+d'=4*C*2^(i+count) /\
    d'+2^(i+count)*b=12*6^(i+count) /\ 1<=d' /\
    l |> e0^^count *> r -->* l' |> r.
Proof.
  induction count; intros n k l i d u Hl Hk Hsum Hd Hp Hb HC.
  - exists l,k,d,u; rewrite !Nat.add_0_r; repeat split; try assumption; apply evstep_refl.
  - assert (Hg:4*6^(1+i)<k) by
      (eapply (zeros_guard C (i+S count) i b k d); eauto; lia).
    destruct (Read0 _ _ _ _ _ _ (e0^^count *> r) Hl Hk Hg)
      as [l1 [k1 [u1 [HL [HK [HD HS]]]]]].
    change (k1+8*6^(1+i)=k*2) in HD.
    assert (Hsum1:k1+(2*d+8*6^(1+i))=4*C*2^(1+i))
      by (change (k1+(2*d+8*6^(1+i))=4*C*(2*2^i)); nia).
    pose proof (zeros_next i b d Hd) as Hd1.
    assert (HC1:3*3^((1+i)+count)<=C) by
      (replace (1+i+count) with (i+S count) by lia; exact HC).
    destruct (IHcount _ _ _ (1+i) _ _ HL HK Hsum1 Hd1 ltac:(lia) Hb HC1)
      as [l2 [k2 [d2 [u2 [HL2 [HK2 [HS2 [HD2 [HP2 HT2]]]]]]]]].
    exists l2,k2,d2,u2; split; [applys_eq HL2; lia|].
    replace (i+S count) with (1+i+count) by lia.
    repeat split; try assumption.
    cbn [lpow]; rewrite Str_app_assoc; follow100 HS; exact HT2.
Qed.

(* Initial exact data for either deficit 2 or deficit 6. *)
Lemma initial26 n h d : (d=2 \/ d=6) -> 3*3^h<=2^n ->
  exists b u, 6<=b /\ b<=10 /\ d+b=12 /\
    2^(n+2)-d=2^1*(1+u*2) /\ (2^(n+2)-d)+d=4*2^n /\ 1<=d.
Proof.
  intros Hd HC; pose proof (pow_pos 3 h ltac:(lia)).
  assert (Hpow:2^(n+2)=4*2^n) by (rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
  destruct Hd as [-> | ->].
  - exists 10,(2^n-1); cbn [Nat.pow]; repeat split; nia.
  - exists 6,(2^n-2); cbn [Nat.pow]; repeat split; nia.
Qed.

Lemma Zero26 n h d l r : (d=2 \/ d=6) -> 3*3^h<=2^n ->
  LC outer (n+2) (2^(n+2)-d) l ->
  exists l', LC outer (n+h+2) (2^h*(4*2^n-12*3^h+(12-d))) l' /\
    l |> e0^^h *> r -->* l' |> r.
Proof.
  intros Hd HC Hl.
  destruct (initial26 n h d Hd HC) as [b [u [Hb [Hb' [Hdb [Hk [Hsum Hp]]]]]]].
  assert (HS:(2^(n+2)-d)+d=4*2^n*2^0) by (cbn [Nat.pow]; lia).
  assert (HD:d+2^0*b=12*6^0) by (cbn [Nat.pow]; lia).
  destruct (zero_scan h outer (2^n) b r
    (n+2) _ l 0 d u Hl Hk HS HD Hp ltac:(lia) HC)
    as [l1 [k1 [d1 [u1 [HL [HK [HS1 [HD1 [HP1 HT]]]]]]]]].
  assert (Hvalue:k1=2^h*(4*2^n-12*3^h+(12-d))).
  { clear -HS1 HD1 HC Hdb.
    change (k1+d1=4*2^n*2^h) in HS1.
    change (d1+2^h*b=12*6^h) in HD1.
    rewrite pow6 in HD1; assert (b=12-d) by lia; subst b; nia. }
  exists l1; split; [applys_eq HL; lia|exact HT].
Qed.

Lemma Z26 n l h d r :
  LC outer (n+2) (2^(n+2)-d) l -> TC ([1;1] *> 0inf) h 0 r ->
  (d=2 \/ d=6) -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr Hd HC; apply TC_zero_unique in Hr; subst r.
  destruct (initial26 n h d Hd HC) as [b [u [Hb [Hb' [Hdb [Hk [Hsum Hp]]]]]]].
  assert (HS:(2^(n+2)-d)+d=4*2^n*2^0) by (cbn [Nat.pow]; lia).
  assert (HD:d+2^0*b=12*6^0) by (cbn [Nat.pow]; lia).
  destruct (zero_scan h outer (2^n) b ([1;1] *> 0inf)
    (n+2) _ l 0 d u Hl Hk HS HD Hp ltac:(lia) HC)
    as [l1 [k1 [d1 [u1 [HL [HK [HS1 [HD1 [HP1 HT]]]]]]]]].
  pose proof (zeros_end (2^n) h b k1 d1 HC HS1 HD1) as Hpos.
  assert (2<=k1) by (pose proof (pow_pos 2 h ltac:(lia)); nia).
  destruct (Read1 _ _ _ _ 0inf HL H) as [l2 [k2 [u2 [HL2 [HK2 [HP2 [HD2 HT2]]]]]]].
  pose proof (LC_bound _ _ _ _ HL) as Hbound.
  exists l2,(u2-1); split; [applys_eq HL2; lia|]; split.
  - replace (n+h+3) with (1+(n+2+h)) by lia; cbn [Nat.pow Nat.add]; nia.
  - follow HT; applys_eq HT2; unfold e1; st; reflexivity.
Qed.

Lemma after_nonzero o C j t A n k l u tail v r :
  TC tail t v r -> EndTail tail -> LC o n k l -> k=1+u*2 ->
  k+(2^(j+1)*A+1)=2^(j+1)*(4*C) -> A+6<=36*3^j ->
  3*3^(j+1+t)<=C ->
  exists l' q, LC o (n+t+1) (3+q*2) l' /\ 6+q*2<=2^(n+t+1) /\
    l |> r -->+ l' |> 0inf.
Proof.
  intros Hr HE Hl Hk Hsum HA HC.
  assert (HK:k=2^0*(1+u*2)) by (cbn [Nat.pow]; lia).
  assert (HS:k+(2^(j+1)*A+1)=(2^(j+1)*(4*C))*2^0) by (cbn [Nat.pow]; lia).
  assert (HB:2^(j+1)*A+6*3^(0+t)<=2^(j+1)*(4*C))
    by (apply (deficit26_budget_scaled C j t (0+t) A); lia).
  exact (bounded_scan o (2^(j+1)*(4*C)) (2^(j+1)*A) _ _ _ _ Hr HE
    n k l 0 (2^(j+1)*A+1) 0 u Hl HK ltac:(lia) HS ltac:(lia) ltac:(cbn; lia) HB).
Qed.

Lemma D26 n l h v r tail d :
  LC outer (n+2) (2^(n+2)-d) l -> TC tail h v r -> EndTail tail ->
  (d=2 \/ d=6) -> 0<v -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HE Hd Hv HC.
  destruct (initial26 n h d Hd HC) as [b [u [Hb [Hb' [Hdb [Hk [Hsum Hp]]]]]]].
  destruct (TC_positive _ _ _ _ Hr Hv) as [j [t [q [s [Hh [HT Hshape]]]]]].
  assert (HCj:3*3^j<=2^n) by
    (assert (3^j<=3^h) by (apply pow_mono; lia); nia).
  assert (HCt:3*3^(j+1+t)<=2^n) by (replace (j+1+t) with h by lia; exact HC).
  assert (HS:(2^(n+2)-d)+d=4*2^n*2^0) by (cbn [Nat.pow]; lia).
  assert (HD:d+2^0*b=12*6^0) by (cbn [Nat.pow]; lia).
  destruct Hshape as [[Er Ev]|[Er Ev]]; subst r.
  - destruct (zero_scan j outer (2^n) b (e1 *> s)
      (n+2) _ l 0 d u Hl Hk HS HD Hp ltac:(lia) HCj)
      as [l1 [k1 [d1 [u1 [HL [HK [HS1 [HD1 [HP1 HT1]]]]]]]]].
    assert (Hbnd:b<=12*3^j) by (pose proof (pow_pos 3 j ltac:(lia)); lia).
    assert (Hdef:d1=2^j*(12*3^j-b)).
    { clear -HD1 Hbnd; change (d1+2^j*b=12*6^j) in HD1.
      rewrite pow6 in HD1.
      assert (HX:2^j*(12*3^j-b)+2^j*b=12*(2^j*3^j)).
      { rewrite <- Nat.mul_add_distr_l, Nat.sub_add by exact Hbnd; nia. }
      lia. }
    assert (Hg:4*6^(1+j)<k1) by
      (eapply (zeros_guard (2^n) h j b k1 d1); eauto; lia).
    assert (2<=k1) by (pose proof (pow_pos 6 (1+j) ltac:(lia)); nia).
    destruct (Read1 _ _ _ _ s HL H) as [l2 [k2 [u2 [HL2 [HK2 [HP2 [HD2 HT2]]]]]]].
    assert (HA:(12*3^j-b)+6<=36*3^j) by (pose proof (pow_pos 3 j ltac:(lia)); nia).
    assert (Hsum2:k2+(2^(j+1)*(12*3^j-b)+1)=2^(j+1)*(4*2^n))
      by (clear -HD2 HS1 Hdef; change (k1+d1=4*2^n*2^j) in HS1;
          rewrite !Nat.pow_add_r; cbn [Nat.pow]; nia).
    destruct (after_nonzero outer (2^n) j t (12*3^j-b) _ _ _ _ _ _ _
      HT HE HL2 HK2 Hsum2 HA HCt) as [l3 [w [HL3 [HB3 HT3]]]].
    exists l3,w; split; [applys_eq HL3; lia|]; split.
    + replace (n+h+3) with (1+(n+2+j)+t+1) by lia; exact HB3.
    + follow HT1; follow11 HT2; exact HT3.
  - destruct (zero_scan j outer (2^n) b (e2 *> s)
      (n+2) _ l 0 d u Hl Hk HS HD Hp ltac:(lia) HCj)
      as [l1 [k1 [d1 [u1 [HL [HK [HS1 [HD1 [HP1 HT1]]]]]]]]].
    assert (Hbnd:b<=12*3^j) by (pose proof (pow_pos 3 j ltac:(lia)); lia).
    assert (Hdef:d1=2^j*(12*3^j-b)).
    { clear -HD1 Hbnd; change (d1+2^j*b=12*6^j) in HD1.
      rewrite pow6 in HD1.
      assert (HX:2^j*(12*3^j-b)+2^j*b=12*(2^j*3^j)).
      { rewrite <- Nat.mul_add_distr_l, Nat.sub_add by exact Hbnd; nia. }
      lia. }
    assert (Hg:4*6^(1+j)<k1) by
      (eapply (zeros_guard (2^n) h j b k1 d1); eauto; lia).
    destruct (Read2 _ _ _ _ _ _ s HL HK Hg) as [l2 [k2 [u2 [HL2 [HK2 [HP2 [HD2 HT2]]]]]]].
    change (k2+8*6^(1+j)+1=k1*2) in HD2.
    assert (HA:(36*3^j-b)+6<=36*3^j) by lia.
    assert (Hsum2:k2+(2^(j+1)*(36*3^j-b)+1)=2^(j+1)*(4*2^n)).
    { clear -HD2 HS1 Hdef Hbnd; change (k1+d1=4*2^n*2^j) in HS1.
      replace (36*3^j-b) with ((12*3^j-b)+24*3^j) by lia.
      rewrite !Nat.pow_add_r; cbn [Nat.pow].
      cbn [Nat.pow Nat.add] in HD2; rewrite pow6 in HD2; nia. }
    destruct (after_nonzero outer (2^n) j t (36*3^j-b) _ _ _ _ _ _ _
      HT HE HL2 HK2 Hsum2 HA HCt) as [l3 [w [HL3 [HB3 HT3]]]].
    exists l3,w; split; [applys_eq HL3; lia|]; split.
    + replace (n+h+3) with (1+(n+2+j)+t+1) by lia; exact HB3.
    + follow HT1; follow11 HT2; exact HT3.
Qed.

End Pair7Scan.

(* SOCPair7Power.v. *)
Module Pair7Power.
Import Pair7Ternary Pair7Normal Pair7Bounds.

(* The second input zero survives as the last symbol of the explicit 110. *)
Lemma PowerStart m h l r : 3^(1+h)<=2^m ->
  LC outer (m+h+2) (2^(1+h)) l ->
  exists l', LC outer (m+2) (2^(m+2)-6) l' /\
    l |> [0;0] *> r -->+ l' |> e0^^h *> [1;1;0] *> r.
Proof.
  intros Hg H; assert (H3:3<=2^m).
  { eapply Nat.le_trans with (m:=3^(1+h));
      [change (3^1<=3^(1+h)); apply pow_mono; lia|exact Hg]. }
  assert (HC:LC outer (m+1+(1+h)) (2^(1+h)) l) by (applys_eq H; lia).
  destruct (LC_R0power _ _ _ ([0] *> r) HC) as [l1 [H1 S1]].
  destruct (LC_R111 _ _ _ _ (e0^^(1+h) *> [1;1;0] *> r) H1)
    as [l2 [H2 S2]].
  assert (HC2:LC outer (1+m) (3+(2^m-2)*2) l2) by (applys_eq H2; lia).
  destruct (Odd000 _ _ _ _ (e0^^h *> [1;1;0] *> r) HC2)
    as [l3 [H3' S3]].
  exists l3; split.
  - applys_eq H3'; try lia; rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
  - follow10 S1; follow100 S2.
    applys_eq (progress_evstep _ _ _ S3); unfold e0; st; reflexivity.
Qed.

(* j counts completed ordinary zero reads; t counts the remaining reads. *)
Lemma PowerZeros m j t l r : 3^(1+j+t)<=2^m ->
  LC outer (m+j+2) (2^(1+j)*(1+(2^m-3^(1+j)+1)*2)) l ->
  exists l', LC outer (m+j+t+2)
      (2^(1+j+t)*(1+(2^m-3^(1+j+t)+1)*2)) l' /\
    l |> e0^^t *> [1;1;0] *> r -->* l' |> [1;1;0] *> r.
Proof.
  revert j l; induction t; intros j l Hg H.
  - exists l; split; [applys_eq H; flia|apply evstep_refl].
  - assert (Hj:3^(2+j)<=2^m).
    { eapply Nat.le_trans with (m:=3^(1+j+S t)); [apply pow_mono; lia|exact Hg]. }
    assert (Hu:2*3^(1+j)+(2^m-3^(2+j)+1)=2^m-3^(1+j)+1).
    { cbn [Nat.pow Nat.add] in Hj |- *; lia. }
    assert (HC:LC outer (m+j+2)
      (2^(1+j)*(1+(2*3^(1+j)+(2^m-3^(2+j)+1))*2)) l)
      by (rewrite Hu; exact H).
    destruct (Even000 _ _ _ _ _ (e0^^t *> [1;1;0] *> r) HC)
      as [l1 [H1 S1]].
    assert (HC1:LC outer (m+(1+j)+2)
      (2^(1+(1+j))*(1+(2^m-3^(1+(1+j))+1)*2)) l1)
      by (applys_eq H1; flia).
    destruct (IHt (1+j) l1 ltac:(applys_eq Hg; flia) HC1) as [l2 [H2 S2]].
    exists l2; split; [applys_eq H2; flia|].
    apply progress_evstep.
    applys_eq (progress_evstep_trans _ _ _ _ S1 S2); unfold e0; st; reflexivity.
Qed.

Lemma Power m h l r : 3^(1+h)<=2^m ->
  LC outer (m+h+2) (2^(1+h)) l ->
  exists l', LC outer (m+h+3)
      (2^(2+h)*(2^(m+1)-2*3^(1+h)+3)-1) l' /\
    l |> [0;0] *> r -->+ l' |> r.
Proof.
  intros Hg H; destruct (PowerStart _ _ _ r Hg H) as [l1 [H1 S1]].
  assert (H3:3<=2^m).
  { eapply Nat.le_trans with (m:=3^(1+h));
      [change (3^1<=3^(1+h)); apply pow_mono; lia|exact Hg]. }
  assert (HC:LC outer (m+0+2) (2^(1+0)*(1+(2^m-3^(1+0)+1)*2)) l1).
  { applys_eq H1; try lia; rewrite (Nat.pow_add_r 2 m 2); cbn [Nat.pow Nat.add]; nia. }
  destruct (PowerZeros m 0 h l1 r Hg HC) as [l2 [H2 S2]].
  assert (Hp:0<2^(1+0+h)*(1+(2^m-3^(1+0+h)+1)*2)) by
    (pose proof (pow_pos 2 (1+h) ltac:(lia)); nia).
  destruct (LC_R110 _ _ _ _ r H2 Hp) as [l3 [H4 S3]].
  exists l3; split.
  - applys_eq H4; try lia; rewrite (Nat.pow_add_r 2 m 1).
    cbn [Nat.pow Nat.add]; nia.
  - follow10 S1; eapply evstep_trans; [exact S2|apply progress_evstep,S3].
Qed.

(* The convenient odd-Blank interface used by the global closed class. *)
Lemma Power_Bo m h l r : 3^(1+h)<=2^m ->
  LC outer (m+h+2) (2^(1+h)) l ->
  exists l' v, LC outer (m+h+3) (3+v*2) l' /\
    6+v*2<=2^(m+h+3) /\ l |> [0;0] *> r -->+ l' |> r.
Proof.
  intros Hg H; destruct (Power _ _ _ r Hg H) as [l' [HC HS]].
  destruct (power_exit m (1+h) ltac:(lia) Hg) as [Hlo Hhi].
  exists l',(2^(1+h)*(2^(m+1)-2*3^(1+h)+3)-2).
  assert (He:2^(2+h)*(2^(m+1)-2*3^(1+h)+3)-1=
    3+(2^(1+h)*(2^(m+1)-2*3^(1+h)+3)-2)*2).
  { cbn [Nat.pow Nat.add] in Hlo |- *; nia. }
  split; [rewrite <- He; exact HC|]; split; [|exact HS].
  replace (1+h+1) with (2+h) in Hhi by lia.
  replace (m+(1+h)+2) with (m+h+3) in Hhi by lia.
  lia.
Qed.

End Pair7Power.

(* SOCPair7Closure.v. *)
Module Pair7Closure.
Import Pair7Ternary Pair7Counting Pair7Normal Pair7Power Pair7Bounds.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

Inductive Allowed : (Q*(side*sym*side))%type -> Prop :=
| Bo n v l : LC outer n (3+v*2) l -> 6+v*2<=2^n ->
    Allowed (l |> 0inf)
| Be m a u l : LC outer (m+a+2) (2^(1+a)*(1+u*2)) l ->
    u+3^(1+a)<=2^m -> Allowed (l |> 0inf)
| S11 n k h v l r : LC outer n k l -> TC ([1;1] *> 0inf) h v r ->
    k+v*3+3*3^h+1<=2^n -> Allowed (l |q> e0 *> r)
| S01 n k h v l r : LC outer n k l -> TC ([0;1] *> 0inf) h v r ->
    k+v*3+6*3^h+1<=2^n -> Allowed (l |q> e0 *> r).

Lemma Bo_step n v l : LC outer n (3+v*2) l -> 6+v*2<=2^n ->
  exists c', l |> 0inf -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hg; destruct n as [|m]; [cbn [Nat.pow] in Hg; lia|].
  destruct (Odd000 outer m v l 0inf Hl) as [l' [HC HS]].
  exists (l' |> 0inf); split; [applys_eq HS; st; reflexivity|].
  apply (Be m 0 v l').
  - applys_eq HC; cbn [Nat.pow Nat.add]; lia.
  - cbn [Nat.pow Nat.add] in Hg |- *; lia.
Qed.

Lemma Be_step m a u l :
  LC outer (m+a+2) (2^(1+a)*(1+u*2)) l -> u+3^(1+a)<=2^m ->
  exists c', l |> 0inf -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hg; destruct u as [|u].
  - assert (HC:LC outer (m+a+2) (2^(1+a)) l) by (applys_eq Hl; lia).
    destruct (Power_Bo m a l 0inf Hg HC) as [l' [v [H1 [H2 HS]]]].
    exists (l' |> 0inf); split; [applys_eq HS; st; reflexivity|].
    eapply Bo; eassumption.
  - assert (HC:LC outer (m+1+(1+a)) (2^(1+a)*(1+(1+u)*2)) l)
      by (applys_eq Hl; lia).
    destruct (LC_R0positive _ _ _ _ _ 0inf HC) as [l' [H1 HS]].
    exists (l' |q> e0 *> e0^^a *> [1;1] *> 0inf); split.
    + applys_eq HS; unfold e0; st; reflexivity.
    + apply (S11 m u a 0 l' (e0^^a *> [1;1] *> 0inf)).
      * exact H1.
      * apply TC_zero.
      * cbn [Nat.pow Nat.add] in Hg |- *; lia.
Qed.

(* The last 01 carry is legal at budget two, including a pure-power exit. *)
Lemma S01_exit n k h l r :
  LC outer n (2+k) l -> TC ([0;1] *> 0inf) h (3^h-1) r ->
  2+k+(3^h-1)*3+6*3^h+1<=2^n ->
  exists c', l |q> e0 *> r -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hr Hg; pose proof (pow_pos 3 h ltac:(lia)) as Hp.
  assert (HC:LC outer n (3*(3^h-(3^h-1))-1+k) l) by (applys_eq Hl; lia).
  destruct (TC_exit _ _ _ _ _ _ _ 0inf HC Hr) as [l1 [H1 S1]].
  destruct (LC_R100 _ _ _ _ 0inf H1) as [l2 [H2 S2]].
  exists (l2 |> 0inf); split.
  - follow10 S1; applys_eq (progress_evstep _ _ _ S2); st; reflexivity.
  - apply (Be n (1+h) k l2).
    + applys_eq H2; cbn [Nat.pow Nat.add]; nia.
    + cbn [Nat.pow Nat.add]; lia.
Qed.

Lemma S11_step n k h v l r :
  LC outer n (3+k) l -> TC ([1;1] *> 0inf) h v r ->
  3+k+v*3+3*3^h+1<=2^n ->
  exists c', l |q> e0 *> r -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hr Hg; destruct (Nat.lt_ge_cases (1+v) (3^h)) as [Hv|Hv].
  - destruct (TC_next _ _ _ _ _ _ _ _ Hl Hr Hv) as [l' [r' [HC [HT HS]]]].
    exists (l' |q> e0 *> r'); split; [exact HS|].
    eapply S11; [exact HC|exact HT|lia].
  - pose proof (TC_bound _ _ _ _ Hr) as Hb.
    assert (Ev:v=3^h-1) by lia; subst v.
    assert (HC:LC outer n (3*(3^h-(3^h-1))+k) l) by (applys_eq Hl; lia).
    destruct (TC_first _ _ _ _ _ _ _ 0inf HC Hr) as [l' [H1 HS]].
    exists (l' |q> e0 *> e0^^h *> [0;1] *> 0inf); split; [exact HS|].
    apply (S01 n k h 0 l' (e0^^h *> [0;1] *> 0inf)); [exact H1|apply TC_zero|lia].
Qed.

Lemma S01_step n k h v l r :
  LC outer n (3+k) l -> TC ([0;1] *> 0inf) h v r ->
  3+k+v*3+6*3^h+1<=2^n ->
  exists c', l |q> e0 *> r -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hr Hg; destruct (Nat.lt_ge_cases (1+v) (3^h)) as [Hv|Hv].
  - destruct (TC_next _ _ _ _ _ _ _ _ Hl Hr Hv) as [l' [r' [HC [HT HS]]]].
    exists (l' |q> e0 *> r'); split; [exact HS|].
    eapply S01; [exact HC|exact HT|lia].
  - pose proof (TC_bound _ _ _ _ Hr) as Hb.
    assert (Ev:v=3^h-1) by lia; subst v.
    apply (S01_exit n (1+k) h l r Hl Hr); lia.
Qed.

End Pair7Closure.

(* SOCPair7LowReturn.v. *)
Module Pair7LowReturn.
Import Pair7Ternary Pair7Counting Pair7Low Pair7Repair Pair7Scan Pair7Bounds.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

Lemma Good0 n l h v r tail : LC outer n 0 l -> TC tail h v r ->
  EndTail tail -> 0<v -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HE Hv HC.
  destruct (clear0 n l r Hl) as [l1 [H1 S1]].
  destruct (D26 n l1 h v r tail 2 H1 Hr HE ltac:(auto) Hv HC) as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Good1 n l h v r tail : LC outer n 1 l -> TC tail h v r ->
  EndTail tail -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HE HC.
  destruct (clear1 n l r Hl) as [l1 [H1 S1]].
  destruct (D3 n l1 h v r tail H1 Hr HE HC) as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Good2 n l h v r tail : LC outer n 2 l -> TC tail h v r ->
  EndTail tail -> S v<3^h -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HE Hv HC.
  destruct (clear2 tail n l h v r Hl Hr Hv) as [l1 [r1 [H1 [T1 S1]]]].
  destruct (D26 n l1 h (S v) r1 tail 6 H1 T1 HE ltac:(auto) ltac:(lia) HC)
    as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Zero11 n l h r : LC outer n 0 l -> TC ([1;1] *> 0inf) h 0 r ->
  3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HC.
  destruct (clear0 n l r Hl) as [l1 [H1 S1]].
  destruct (Z26 n l1 h 2 r H1 Hr ltac:(auto) HC) as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

(* A bounded number of ordinary increments, followed by a protected low exit. *)
Lemma RemainderReturn n h q b l : LC outer n (3*q+b) l ->
  b<=2 -> q<3^h -> (b=0%nat -> 0<q) -> (b=2 -> S q<3^h) -> 3*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> e0^^h *> [0;1;1;0] *> 0inf -->+ l' |> 0inf.
Proof.
  intros Hl Hb Hq H0 H2 HC.
  destruct (TC_steps q outer ([0;1;1;0] *> 0inf) n b l h 0 _ Hl (TC_zero _ h) Hq)
    as [l1 [r1 [H1 [T1 S1]]]].
  change (TC ([0;1;1;0] *> 0inf) h q r1) in T1.
  assert (HR:exists l' u, LC outer (n+h+3) (3+u*2) l' /\
    6+u*2<=2^(n+h+3) /\ l1 |q> e0 *> r1 -->+ l' |> 0inf).
  { destruct b as [|[|b]].
    - eapply Good0; eauto using End0110.
    - eapply Good1; eauto using End0110.
    - assert (b=0%nat) by lia; subst b; eapply Good2; eauto using End0110. }
  destruct HR as [l2 [u [HL [HG HS]]]].
  exists l2,u; repeat split; try assumption; exact (evstep_progress_trans _ _ _ _ S1 HS).
Qed.

Lemma remaining_safe n h p : p<=1 -> 6*3^h+p<=2^n -> 2^n+1+p<9*3^h ->
  exists q b, 2^n-6*3^h+p=3*q+b /\ b<=2 /\ q<3^h /\
    (b=0%nat -> 0<q) /\ (b=2 -> S q<3^h).
Proof.
  intros Hp HC HT; destruct p as [|p].
  - destruct (hard2_remainder n h ltac:(lia) ltac:(lia)) as [q [[HQ Hq]|[HQ Hq]]];
      [exists q,1%nat|exists q,2]; repeat split; lia.
  - assert (p=0%nat) by lia; subst p.
    destruct (hard0_remainder n h ltac:(lia) ltac:(lia)) as [q [[HQ [Hq Hq']]|[HQ Hq]]];
      [exists q,0%nat|exists q,2]; repeat split; lia.
Qed.

(* p=1 is deficit two; p=0 is deficit six.  The same finite second-overflow
   bridge handles both, with a different permitted low remainder. *)
Lemma HardScan n h p l : p<=1 -> 6*3^h+p<=2^n ->
  LC outer (n+2) (2^(n+2)-(6-4*p)) l ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |> e0^^h *> [0;1] *> 0inf -->+ l' |> 0inf.
Proof.
  intros Hp HC Hl; assert (Hd:6-4*p=2 \/ 6-4*p=6) by lia.
  assert (HC3:3*3^h<=2^n) by lia.
  destruct (Zero26 n h (6-4*p) l ([0;1] *> 0inf) Hd HC3 Hl) as [l1 [H1 S1]].
  set (K:=2^h*(4*2^n-12*3^h+(12-(6-4*p)))) in H1.
  assert (HK:K=2^(1+h)*(1+(2^n-3*3^h+1+p)*2)).
  { unfold K; cbn [Nat.pow Nat.add]; nia. }
  destruct (Nat.le_gt_cases (9*3^h) (2^n+1+p)) as [HT|HT].
  - assert (HG:4*6^(1+h)<K).
    { rewrite HK; apply (proj2 (normal_budget (1+h) (2^n-3*3^h+1+p))).
      cbn [Nat.pow Nat.add]; lia. }
    destruct (terminal outer (n+h+2) K l1 (1+h) (2^n-3*3^h+1+p)
      ([0;1] *> 0inf) End01 H1 HK HG) as [l2 [u [HL [HB HS]]]].
    exists l2,u; split; [applys_eq HL; lia|]; split.
    + replace (n+h+3) with (n+h+2+1) by lia; exact HB.
    + exact (evstep_progress_trans _ _ _ _ S1 HS).
  - assert (HB:LC outer (n+h+2)
      (2^(1+h)*(1+(1+3*3^h+(2^n-6*3^h+p))*2)) l1).
    { applys_eq H1; rewrite HK; nia. }
    destruct (HardEntry n h (2^n-6*3^h+p) l1 HB) as [l2 [H2 S2]].
    destruct (remaining_safe n h p Hp HC HT) as [q [b [HQ [Hb [Hq [H0 Htwo]]]]]].
    assert (HL:LC outer n (3*q+b) l2) by (applys_eq H2; lia).
    destruct (RemainderReturn n h q b l2 HL Hb Hq H0 Htwo HC3) as [l3 [u [H3 [H4 S3]]]].
    exists l3,u; repeat split; try assumption.
    exact (evstep_progress_trans _ _ _ _ S1 (progress_trans _ _ _ _ S2 S3)).
Qed.

Lemma Hard0 n l h r : LC outer n 0 l -> TC ([0;1] *> 0inf) h 0 r ->
  6*3^h+1<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HC; apply TC_zero_unique in Hr; subst r.
  destruct (Pair7Low.clear0 n l (e0^^h *> [0;1] *> 0inf) Hl) as [l1 [H1 S1]].
  destruct (HardScan n h 1 l1 ltac:(lia) HC H1) as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

Lemma Hard2 n l h r : LC outer n 2 l -> TC ([1;1] *> 0inf) h (3^h-1) r ->
  6*3^h<=2^n ->
  exists l' u, LC outer (n+h+3) (3+u*2) l' /\ 6+u*2<=2^(n+h+3) /\
    l |q> e0 *> r -->+ l' |> 0inf.
Proof.
  intros Hl Hr HC.
  destruct (Pair7Repair.clear2_full _ _ _ _ _ Hl Hr) as [l1 [r1 [H1 [T1 S1]]]].
  apply TC_zero_unique in T1; subst r1.
  destruct (HardScan n h 0 l1 ltac:(lia) ltac:(lia) H1) as [l2 [u [H2 [H3 S2]]]].
  exists l2,u; repeat split; try assumption; exact (progress_trans _ _ _ _ S1 S2).
Qed.

End Pair7LowReturn.

(* SOCPair7Nonhalt.v: final proof at TM7 top level. *)
Import Pair7Ternary Pair7Scan Pair7LowReturn Pair7Closure.
Notation "l |q> r" := (l |> [1;1] *> r) (at level 30).

Lemma Bo_return n c :
  (exists l u, LC outer n (3+u*2) l /\ 6+u*2<=2^n /\ c -->+ l |> 0inf) ->
  exists c', c -->+ c' /\ Allowed c'.
Proof.
  intros [l [u [Hl [Hg HS]]]].
  exists (l |> 0inf); split; [exact HS|eapply Bo; eassumption].
Qed.

Lemma S11_all n k h v l r : LC outer n k l -> TC ([1;1] *> 0inf) h v r ->
  k+v*3+3*3^h+1<=2^n ->
  exists c', l |q> e0 *> r -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hr Hg; destruct k as [|[|[|k]]].
  - destruct v as [|v]; apply (Bo_return (n+h+3)).
    + eapply Zero11; eauto; lia.
    + eapply Good0; eauto using End11; lia.
  - apply (Bo_return (n+h+3)); eapply Good1; eauto using End11; lia.
  - destruct (Nat.lt_ge_cases (S v) (3^h)) as [Hv|Hv].
    + apply (Bo_return (n+h+3)); eapply Good2; eauto using End11; lia.
    + pose proof (TC_bound _ _ _ _ Hr) as Hb.
      assert (Ev:v=3^h-1) by lia; subst v.
      apply (Bo_return (n+h+3)); eapply Hard2; eauto; lia.
  - apply (S11_step n k h v l r); assumption.
Qed.

Lemma S01_all n k h v l r : LC outer n k l -> TC ([0;1] *> 0inf) h v r ->
  k+v*3+6*3^h+1<=2^n ->
  exists c', l |q> e0 *> r -->+ c' /\ Allowed c'.
Proof.
  intros Hl Hr Hg; destruct k as [|[|[|k]]].
  - destruct v as [|v]; apply (Bo_return (n+h+3)).
    + eapply Hard0; eauto; lia.
    + eapply Good0; eauto using End01; lia.
  - apply (Bo_return (n+h+3)); eapply Good1; eauto using End01; lia.
  - destruct (Nat.lt_ge_cases (S v) (3^h)) as [Hv|Hv].
    + apply (Bo_return (n+h+3)); eapply Good2; eauto using End01; lia.
    + pose proof (TC_bound _ _ _ _ Hr) as Hb.
      assert (Ev:v=3^h-1) by lia; subst v.
      apply (S01_exit n 0 h l r); assumption.
  - apply (S01_step n k h v l r); assumption.
Qed.

Lemma Allowed_step c : Allowed c -> exists c', c -->+ c' /\ Allowed c'.
Proof.
  intro H; destruct H.
  - eapply Bo_step; eassumption.
  - eapply Be_step; eassumption.
  - eapply S11_all; eassumption.
  - eapply S01_all; eassumption.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  destruct init as [l [Hl HS]].
  eapply multistep_nonhalt; [exact HS|].
  eapply progress_nonhalt with (P:=Allowed).
  - intros c HC; destruct (Allowed_step c HC) as [c' [Hstep Hnext]].
    exists c'; split; assumption.
  - apply (Bo 5 12 l); [exact Hl|lia].
Qed.
End TM7.

Print Assumptions TM1.nonhalt.
Print Assumptions TM2.nonhalt.
Print Assumptions TM3.nonhalt.
Print Assumptions TM4.nonhalt.
Print Assumptions TM5.nonhalt.
Print Assumptions TM6.nonhalt.
Print Assumptions TM7.nonhalt.
