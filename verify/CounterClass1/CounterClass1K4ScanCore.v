Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K4PhaseProbe.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4SimpleRules P.

Lemma k4_phase_equalities H S D k:
  H=2*S+D -> 4*S+3*k+11<=H -> 2<=S -> 1<=k ->
  let A := H+D+3 in
  let Sp := 2*S+k+3 in
  let Dp := 2*D+1-k in
  let Hp := 2*H+k+7 in
  let W := 2*Hp-1 in
  2*A+11+2*(Sp-7)=W-4 /\
  2*A+11+2*((Sp-7)+2)=W /\
  A-1-(Sp-7)=Dp+5 /\
  A+6+(Sp-7)=Hp-2 /\
  18+4*(Sp-7)=4*Sp-10 /\
  0<Sp-7.
Proof.
  intros Hhs Hlarge Hs Hk. cbv zeta. repeat split; lia.
Qed.

Definition K4CoreEnd (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (H S D k: nat) : Prop :=
  let Hp := 2*H+k+7 in
  let Sp := 2*S+k+3 in
  let Dp := 2*D+1-k in
  let A := H+D+3 in
  let W := 2*Hp-1 in
  exists x y,
    K4PointerPrefix B (W-4) x y 2 0 0 /\
    K4Row P B true (W-4) x /\
    K4Row P B false (W-3) y /\
    y<=x<=Datatypes.S y /\
    K4ReachPrefix B (W-4) x y /\
    (forall j, j<=2 -> K4Particle P (W-4) (Dp+5-j) y) /\
    P (Hp-2) 0 (Dp+5) (4*Sp-10) /\
    (forall j, j<Sp-7 -> K4Particle P W (A+6+j) 0) /\
    K4Row P B true W 0 /\
    K4Row P B false (W+1) 0 /\
    (forall a, H+1<=a<=A -> K4Particle P W a 0) /\
    (forall a, A+2<=a<=A+5 -> K4Particle P W a 0) /\
    K4TopParticle P W (A+1) 0.

Definition K4FirstGen (P: nat -> nat -> nat -> nat -> Prop)
    (kind: K4Kind) (B: list bool) (H S D k: nat) : Prop :=
  let g := k4_gap kind in
  let u := 2*H+2*g+5 in
  let p := H-g+4 in
  let q := D-g in
  let e := H+g+3 in
  let A := H+D+3 in
  let Sp := 2*S+k+3 in
  let W := 2*(2*H+k+7)-1 in
  exists xg yg,
    K4PointerTrace B (u+2*(q+3)) xg yg (Sp-2) /\
    K4Row P B true (u+2*(q+3)) xg /\
    K4Row P B false (u+2*(q+3)+1) yg /\
    yg<=xg<=Datatypes.S yg /\
    (forall j, j<=q -> K4Particle P (u+2*(q+3)) (e+j) yg) /\
    P A 0 0 (2*A+4) /\
    K4Row P B true W 0 /\
    K4Row P B false (W+1) 0 /\
    (forall a, H+1<=a<=A -> K4Particle P W a 0).

Lemma k4_scan_first_data kind B H S D k:
  K4ScanData P kind B H S D k -> K4FirstGen P kind B H S D k.
Proof.
  intros HS0.
  set (g:=k4_gap kind).
  unfold K4ScanData in HS0. fold g in HS0.
  destruct HS0 as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [RT0 [RF0 [Htail Hex]]]]]]]]]].
  assert (Hg: g=5 \/ g=6) by
    (unfold g, k4_gap; destruct kind; auto).
  set (u:=2*H+2*g+5).
  set (p:=H-g+4).
  set (q:=D-g).
  set (e:=H+g+3).
  set (A:=H+D+3).
  set (Hp:=2*H+k+7).
  set (Sp:=2*S+k+3).
  set (Dp:=2*D+1-k).
  set (W:=2*Hp-1).
  assert (Htrace: K4PointerTrace B u p (p) (p+k4_rdrops B p)).
  { destruct (k4_pointer_scan B Hbase p) as [HT _].
    apply HT; unfold u,p; try rewrite Hlen; lia. }
  assert (Hdrop': k4_rdrops B p=k) by
    (unfold p; exact Hdrop).
  rewrite Hdrop' in Htrace.
  assert (RT: K4Row P B true u p).
  { unfold u,p,g. exact (ex_intro _ (4*k4_gap kind+1) RT0). }
  assert (RF: K4Row P B false (u+1) p).
  { unfold u,p,g. applys_eq (ex_intro _ (4*k4_gap kind+2) RF0); lia. }
  assert (Hfull: K4PointerPrefix B u p p (p+k) 0 0) by
    exact (k4_pointer_trace_prefix B u p p (p+k) Htrace).
  destruct (k4_pointer_trace_rows P R B u p p (p+k) Htrace RT RF)
    as [RTW RFW].
  assert (Htot: u+2*(p+k)=W) by
    (unfold u,p,W,Hp; lia).
  assert (RTW': K4Row P B true W 0) by (applys_eq RTW; lia).
  assert (RFW': K4Row P B false (W+1) 0) by (applys_eq RFW; lia).
  assert (Hq3: q+3<=p+k) by
    (unfold q,p; lia).
  destruct (k4_pointer_trace_split B u p p (p+k) (q+3) Hq3 Htrace)
    as (xg&yg&m&Hm&HPg&HTg).
  assert (Hm': m=Sp-2) by
    (unfold u,p,q,Sp in *; lia).
  subst m.
  destruct (k4_pointer_prefix_rows P R B u p p (q+3) xg yg HPg RT RF)
    as [RTg RFg].
  assert (RFg': K4Row P B false (u+2*(q+3)+1) yg) by
    (applys_eq RFg; lia).
  assert (Hpairg: yg<=xg<=Datatypes.S yg).
  { exact (k4_pointer_prefix_pair B u p p (q+3) xg yg
      ltac:(lia) HPg). }
  assert (Hqy: q+2<=p) by (unfold q,p; lia).
  assert (Hew: 2*e=u+1) by (unfold e,u; lia).
  assert (Heout: 2*q+(4*S+4*g+10)=u+5) by
    (unfold q,u; lia).
  assert (Hex': P e 0 q (4*S+4*g+10)).
  { unfold e,q,g. applys_eq Hex; lia. }
  assert (Hgen: forall j, j<=q ->
      K4Particle P (u+2*(q+3)) (e+j) yg).
  { abstract (
      intros j Hj; exact (k4_generated_synced P R B u p p q e
        (4*S+4*g+10) xg yg Hbase ltac:(lia) Hqy HPg RT RF Hex'
        Hew Heout j Hj)). }
  assert (HZ: P A 0 0 (2*A+4)).
  { applys_eq (k4_inc01_iter P R e q (4*S+4*g+10) Hex');
      unfold e,q,A,g; lia. }
  assert (Hfirst: forall a, H+1<=a<=A -> K4Particle P W a 0).
  { abstract (
      intros a Ha; destruct (Compare_dec.le_lt_dec e a) as [Hea|Hae];
      [ replace a with (e+(a-e)) by lia;
        applys_eq (k4_generated_particles P R B u p p q (p+k) e
          (4*S+4*g+10) Hbase ltac:(lia) Hqy Htrace RT RF
          ltac:(unfold e,g; applys_eq Hex; lia) Hew Heout (a-e));
          unfold W; lia
      | assert (Hj: H+g+2-a<=g+1) by (unfold e in Hae; lia);
        assert (HTa: P a (2+2*(H+g+2-a)) p (4*g+2)) by
          (applys_eq (Htail (H+g+2-a) Hj); lia);
        assert (HPa: K4Particle P u a p) by
          (exists (2+2*(H+g+2-a)),(4*g+2); repeat split;
           try assumption; unfold u,p; lia);
        applys_eq (k4_pointer_prefix_synced_particle P R B u p p (p+k)
          0 0 a Hfull RT RF HPa); unfold W; lia ]). }
  unfold K4FirstGen. fold g u p q e A Sp W.
  exists xg,yg.
  split; [exact HTg|].
  split; [exact RTg|].
  split; [exact RFg'|].
  split; [exact Hpairg|].
  split; [exact Hgen|].
  split; [exact HZ|].
  split; [exact RTW'|].
  split; [exact RFW'|].
  exact Hfirst.
Qed.

Definition K4SecondGen (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (H S D k: nat) : Prop :=
  let A := H+D+3 in
  let Sp := 2*S+k+3 in
  let W := 2*(2*H+k+7)-1 in
  exists xb yb,
    K4PointerPrefix B (2*A+11) xb yb ((Sp-7)+2) 0 0 /\
    K4Row P B true (2*A+11) xb /\
    K4Row P B false (2*A+11+1) yb /\
    yb<=xb<=Datatypes.S yb /\
    (forall j, j<=Sp-5 -> K4Particle P (2*A+11) (A-1-j) yb) /\
    P (A+6) 0 (A-1) 18 /\
    (forall a, A+2<=a<=A+5 -> K4Particle P W a 0) /\
    K4TopParticle P W (A+1) 0 /\
    (forall a, H+1<=a<=A -> K4Particle P W a 0) /\
    K4Row P B true W 0 /\
    K4Row P B false (W+1) 0.

Lemma k4_scan_second_data kind B H S D k:
  K4ScanData P kind B H S D k ->
  K4FirstGen P kind B H S D k -> K4SecondGen P B H S D k.
Proof.
  intros HS0 HF.
  set (g:=k4_gap kind).
  set (u:=2*H+2*g+5).
  set (p:=H-g+4).
  set (q:=D-g).
  set (e:=H+g+3).
  set (A:=H+D+3).
  set (Sp:=2*S+k+3).
  set (W:=2*(2*H+k+7)-1).
  unfold K4ScanData in HS0. fold g in HS0.
  destruct HS0 as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [RT0 [RF0 [Htail Hex]]]]]]]]]].
  assert (Hg: g=5 \/ g=6) by
    (unfold g, k4_gap; destruct kind; auto).
  unfold K4FirstGen in HF.
  fold g u p q e A Sp W in HF.
  destruct HF as (xg&yg&HTg&RTg&RFg&Hpairg&Hgen&HZ&RTW&RFW&Hfirst).
  assert (HUA: 2*A+5=u+2*(q+3)) by
    (unfold A,u,q; lia).
  destruct (k4_pointer_trace_split B (u+2*(q+3)) xg yg (Sp-2) 3)
    as (xb&yb&m2&Hm2&HPb&HTb); try assumption; try lia.
  assert (Hm2': m2=Sp-5) by lia. subst m2.
  assert (Hliveb: xb<>0 \/ yb<>0).
  { inversion HTb; subst; [unfold Sp in *; lia|assumption]. }
  assert (HA: K4Particle P (u+2*(q+3)) A yg).
  { replace A with (e+q) by (unfold A,e,q; lia). apply Hgen. lia. }
  destruct (k4_second_generator_start P R B (u+2*(q+3)) xg yg A xb yb
      Hbase Hpairg ltac:(unfold A; lia) HUA HPb Hliveb RTg RFg HA HZ) as
    (z3&z&zt&HRTb&HRFb&Hpairb&HOK3&HPA3&HOK&HPA2&HPA4&HPA5&HTOK&HPT&HE).
  assert (HPrem: K4PointerPrefix B (2*A+11) xb yb (2+(Sp-7)) 0 0).
  { applys_eq (k4_pointer_trace_prefix B
      (u+2*(q+3)+6) xb yb (Sp-5) HTb); lia. }
  assert (RTb': K4Row P B true (2*A+11) xb) by
    (applys_eq HRTb; lia).
  assert (RFb': K4Row P B false (2*A+11+1) yb) by
    (applys_eq HRFb; lia).
  assert (HPA20: K4Particle P (2*A+11) (A+2) z) by
    (applys_eq HPA2; lia).
  assert (HPA30: K4Particle P (2*A+11) (A+3) z3) by
    (applys_eq HPA3; lia).
  assert (HPA40: K4Particle P (2*A+11) (A+4) z) by
    (applys_eq HPA4; lia).
  assert (HPA50: K4Particle P (2*A+11) (A+5) z) by
    (applys_eq HPA5; lia).
  assert (HPT0: K4TopParticle P (2*A+11) (A+1) zt) by
    (applys_eq HPT; lia).
  assert (Hbridge: forall a, A+2<=a<=A+5 -> K4Particle P W a 0).
  { intros a Ha;
    assert (E: a=A+2 \/ a=A+3 \/ a=A+4 \/ a=A+5) by lia;
    destruct E as [E|[E|[E|E]]]; subst a;
    [ applys_eq (k4_pointer_prefix_live_particle P R B (2*A+11) xb yb
        (Sp-7) 0 0 z (A+2) Hbase HPrem RTb' RFb' HOK HPA20); unfold W; lia
    | applys_eq (k4_pointer_prefix_live_particle P R B (2*A+11) xb yb
        (Sp-7) 0 0 z3 (A+3) Hbase HPrem RTb' RFb' HOK3 HPA30); unfold W; lia
    | applys_eq (k4_pointer_prefix_live_particle P R B (2*A+11) xb yb
        (Sp-7) 0 0 z (A+4) Hbase HPrem RTb' RFb' HOK HPA40); unfold W; lia
    | applys_eq (k4_pointer_prefix_live_particle P R B (2*A+11) xb yb
        (Sp-7) 0 0 z (A+5) Hbase HPrem RTb' RFb' HOK HPA50); unfold W; lia ]. }
  assert (HTop: K4TopParticle P W (A+1) 0).
  { applys_eq (k4_pointer_prefix_live_top P R B (2*A+11)
      xb yb (Sp-7) 0 0 zt (A+1) Hpairb HPrem RTb' RFb' HTOK HPT0);
      unfold W; lia. }
  assert (Hdrivers: forall j, j<=Sp-5 ->
      K4Particle P (2*A+11) (A-1-j) yb).
  { intros j Hj;
    assert (Hea: e<=A-1-j<=A) by (unfold e,A,Sp; lia);
    assert (Hsrc: K4Particle P (u+2*(q+3)) (A-1-j) yg) by
      (replace (A-1-j) with (e+(A-1-j-e)) by lia;
       apply Hgen; unfold A,e,q; lia);
    applys_eq (k4_pointer_prefix_synced_particle P R B
      (u+2*(q+3)) xg yg 3 xb yb (A-1-j) HPb RTg RFg Hsrc); lia. }
  unfold K4SecondGen. fold A Sp W.
  exists xb,yb.
  split; [applys_eq HPrem; lia|].
  split; [exact RTb'|].
  split; [exact RFb'|].
  split; [exact Hpairb|].
  split; [exact Hdrivers|].
  split; [exact HE|].
  split; [exact Hbridge|].
  split; [exact HTop|].
  split; [exact Hfirst|].
  split; [exact RTW|].
  exact RFW.
Qed.

Lemma k4_scan_core_data kind B H S D k:
  K4ScanData P kind B H S D k -> K4CoreEnd P B H S D k.
Proof.
  intros HS0.
  pose proof (k4_scan_first_data kind B H S D k HS0) as HF.
  pose proof (k4_scan_second_data kind B H S D k HS0 HF) as HM.
  unfold K4ScanData in HS0.
  destruct HS0 as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [RT0 [RF0 [Htail Hex]]]]]]]]]].
  set (A:=H+D+3).
  set (Sp:=2*S+k+3).
  set (Dp:=2*D+1-k).
  set (Hp:=2*H+k+7).
  set (W:=2*Hp-1).
  unfold K4SecondGen in HM. fold A Sp W in HM.
  destruct HM as
    (xb&yb&HPearly&RTb&RFb&Hpairb&Hdrivers&HE&Hbridge&HTop&Hfirst&RTW&RFW).
  assert (HDearly: forall j, j<=(Sp-7)+2 ->
      K4Particle P (2*A+11) (A-1-j) yb).
  { intros j Hj. apply Hdrivers. lia. }
  destruct (k4_endpoint_early P R B (2*A+11) xb yb (Sp-7)
      (A+6) (A-1) 18 Hbase Hpairb ltac:(lia) ltac:(lia)
      HPearly RTb RFb HDearly HE ltac:(lia) ltac:(lia)) as
    (xt&yt&Hreach&HPt&RTt&RFt&Hpairt&HDt&HEt&Hzeros).
  destruct (k4_phase_equalities H S D k Hhs Hlarge Hs Hk) as
    (HterminalWeight&HzeroWeight&HdriverBase&HendpointBase&HendpointData&HphasePositive).
  assert (Hhigh: K4ReachPrefix B (W-4) xt yt).
  { exists (2*A+11),xb,yb,(Sp-7). split; [exact HphasePositive|].
    split; [exact Hpairb|]. split; [exact HterminalWeight|exact Hreach]. }
  unfold K4CoreEnd.
  fold Hp Sp Dp A W.
  exists xt,yt.
  split; [applys_eq HPt; unfold W; lia|].
  split; [applys_eq RTt; unfold W; lia|].
  split; [applys_eq RFt; unfold W; lia|].
  split; [exact Hpairt|].
  split; [exact Hhigh|].
  split.
  - intros j Hj. applys_eq (HDt j Hj); lia.
  - split.
    + applys_eq HEt; lia.
    + split.
      * intros j Hj. applys_eq (Hzeros j Hj); lia.
      * split; [exact RTW|].
        split; [exact RFW|].
        split; [exact Hfirst|].
        split; [exact Hbridge|].
        exact HTop.
Qed.

Lemma k4_scan_core kind runs B H S D k:
  K4ScanStart P kind runs B H S D k -> K4CoreEnd P B H S D k.
Proof.
  intros HS.
  apply (k4_scan_core_data kind).
  exact (k4_scan_start_data P kind runs B H S D k HS).
Qed.

End K4PhaseProbe.
