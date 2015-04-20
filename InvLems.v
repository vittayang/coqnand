(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import List.
Require Import ListEx.
Require Import LibEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import NandLems.

Require Import Bast0.
Require Import FTLProp.
Require Import FTLLems.

Require Import Inv.

(* == I_inv == lemmas =========================== *)

Lemma I_pbn_bit_valid_preserv_bit_update :
  forall pbn bit bi bit',
    valid_block_no pbn
    -> I_pbn_bit_valid bit 
    -> bit_update bit pbn bi = Some bit'
    -> I_pbn_bit_valid bit'.
Proof.
  intros pbn bit bi bit' Hv HI1 Hup.
  unfold I_pbn_bit_valid in * .
  intros pbn'.
  destruct (block_no_eq_dec pbn pbn').
    subst pbn'.
    destruct (HI1 pbn) as [H1 H2].
    split.
      intro Hx.
      exists bi.
      rewrite (bit_update_bit_get_eq _ _ _ _ Hup).
      trivial.
    intros [bi' Hget'].
    trivial.
  destruct (HI1 pbn') as [H1 H2].
  split.
    intro Hx.
    destruct (H1 Hx) as [bi' Hg'].
    exists bi'.
    rewrite (bit_update_bit_get_neq _ _ _ _ _ Hup (neq_sym H)).
    trivial.
  intros [bi' Hg'].
  apply H2.
  exists bi'.
  rewrite <- (bit_update_bit_get_neq _ _ _ _ _ Hup (neq_sym H)).
  trivial.
Qed.

Lemma I_pbn_fbq_valid_preserv_fbq_deq :
  forall fbq pbn fbq',
    I_pbn_fbq_valid fbq
    -> fbq_deq fbq = Some (pbn, fbq')
    -> I_pbn_fbq_valid fbq'.
Proof.
  induction fbq.
    intros.
    discriminate.
  intros pbn' fbq' Hv.
  simpl.
  intros H.
  injection H.
  intros.
  subst fbq' a.
  unfold I_pbn_fbq_valid in Hv.
  unfold I_pbn_fbq_valid.
  intros pbn Hin.
  apply Hv.
  unfold fbq_in.
  simpl.
  destruct (beq_nat pbn pbn').
  trivial.
  trivial.
Qed.

Lemma I_pbn_fbq_state_preserv_fbq_deq : 
  forall bit fbq pbn fbq',
    I_pbn_fbq_state bit fbq
    -> fbq_deq fbq = Some (pbn, fbq')
    -> I_pbn_fbq_state bit fbq'.
Proof.
  induction fbq.
    intros.
    discriminate.
  intros pbn' fbq' HI4.
  simpl.
  intros H.
  injection H.
  intros.
  subst fbq' a.
  unfold I_pbn_fbq_state in HI4.
  unfold I_pbn_fbq_state.
  intros pbn bi Hin Hg.
  apply HI4 with pbn. 
  unfold fbq_in.
  simpl.
  destruct (beq_nat pbn pbn').
  trivial.
  trivial.
  trivial.
Qed.

Lemma I_pbn_fbq_state_preserv_bit_update : 
  forall bit fbq pbn bi bit',
    I_pbn_fbq_state bit fbq
    -> bit_update bit pbn bi = Some bit'
    -> fbq_in fbq pbn = false
    -> I_pbn_fbq_state bit' fbq.
Proof.
  intros. unfold I_pbn_fbq_state. unfold I_pbn_fbq_state in H.
  intros pbn' bi' Hin' Hg'.
  apply (H pbn' bi'); trivial.
  destruct (block_no_eq_dec pbn pbn').
    subst pbn'.
    rewrite H1 in Hin'.
    discriminate.
  rewrite <- (bit_update_bit_get_neq _ _ _ _ _ H0); auto.
Qed.

Lemma allocated_pbn_not_in_fbq : 
  forall fbq pbn fbq',
    I_pbn_fbq_distinguishable fbq
    -> fbq_deq fbq = Some (pbn, fbq')
    -> fbq_in fbq' pbn = false.
Proof.
  intros fbq pbn fbq' HI8 Hdeq.
  assert (Hin : fbq_in fbq pbn = true).
    unfold fbq_deq, fbq_in in * .
    destruct fbq.
      discriminate.
    injection Hdeq.
    intros; subst fbq' b.
    simpl.
    simplbnat.
    trivial.
  destruct (fbq_in fbq' pbn) eqn:Hin'.
  destruct (fbq_in_fbq_get _ _ Hin') as [i Hg].
  assert (Hx:=fbq_get_fbq_rdeq_fbq_get _ _ _ _ _ Hg Hdeq).
  assert (Hy : fbq_get fbq 0 = Some pbn).
    eapply fbq_deq_fbq_get; eauto.
  assert (Hm : 0 <> S i).
    auto with arith.
  assert (HF:= HI8 0 (S i) pbn pbn Hm Hy Hx).
  destruct (HF (refl_equal)).
  trivial.
Qed.

Lemma I_pbn_habitation_in_fbq_implies_not_in_bmt :
  forall pbn bmt fbq,
    valid_block_no pbn
    -> I_pbn_habitation bmt fbq
    -> fbq_in fbq pbn = true
    -> ~ pbn_in_bmt bmt pbn.
Proof.
  intros.
  destruct (H0 pbn H).
    destruct H2 as [[lbn H3] H4].
    rewrite H1 in H4.
    discriminate.
  unfold pbn_in_bmt.
  intro Hx.
  destruct Hx as [lbn Hx].
  destruct H2 as [H3 H4].
  apply (H3 lbn Hx); trivial.
Qed.

Lemma I_pbn_habitation_in_bmt_implies_not_in_fbq :
  forall pbn bmt fbq,
    valid_block_no pbn
    -> I_pbn_habitation bmt fbq
    -> pbn_in_bmt bmt pbn
    -> fbq_in fbq pbn = false.
Proof.
  intros.
  destruct (H0 pbn H).
    destruct H2 as [[lbn H3] H4].
    trivial.
  unfold pbn_in_bmt in H1.
  destruct H1 as [lbn H1].
  destruct H2 as [H3 H4].
  destruct (H3 _ H1).
Qed.

Lemma I_pbn_bmt_valid_preserv_bmt_update_data_none : 
  forall bmt lbn pbn bmt',
    valid_block_no pbn
    -> I_pbn_bmt_valid bmt
    -> bmt_update bmt lbn (Some pbn, None) = Some bmt' 
    -> I_pbn_bmt_valid bmt'.
Proof.
  unfold I_pbn_bmt_valid.
  intros bmt lbn pbn bmt' Hv HI2 Hup.
  intros lbn' pbn' Hin.
  destruct (block_no_eq_dec lbn lbn') as [Hlbn | Hlbn].
    subst lbn'.
    assert (Hx:= bmt_update_bmt_get_eq _ _ _ _  Hup).
    destruct Hin as [Hin | Hin].
      destruct Hin as [x Hin].
      rewrite Hin in Hx.
      injection Hx.
      intros; subst x pbn'.
      trivial.
    destruct Hin as [x Hin].
    rewrite Hin in Hx.
    discriminate.
  assert (Hx := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hup Hlbn Hin).
  apply HI2 with lbn'; trivial.
Qed.

(* Lemma I_pbn_bmt_valid_preserv_bmt_update :  *)
(*   forall bmt lbn pbn bmt', *)
(*     valid_block_no pbn *)
(*     -> I_pbn_bmt_valid bmt *)
(*     -> (bmt_update bmt lbn (Some pbn, None) = Some bmt'  *)
(*         \/  bmt_update bmt lbn (None, Some pbn) = Some bmt') *)
(*     -> I_pbn_bmt_valid bmt'. *)
(* Proof. *)
(*   intros bmt lbn pbn bmt' Hv HI2 H *)
(* Qed. *)

Lemma I_pbn_bmt_valid_preserv_bmt_update_log : 
  forall bmt lbn pbn bmt',
    valid_block_no pbn
    -> I_pbn_bmt_valid bmt
    -> bmt_update_log bmt lbn pbn = Some bmt' 
    -> I_pbn_bmt_valid bmt'.
Proof.
  unfold bmt_update_log.
  intros bmt lbn pbn bmt' Hv HI2 Hul.
  destruct (bmt_get bmt lbn) as [[bmrdata bmrlog] | ] eqn:Hget; try discriminate.
  destruct (bmt_update bmt lbn (bmrdata, Some pbn)) as [bmt'' | ] eqn:Hu; try discriminate.
  injection Hul; intro; subst bmt''.
  unfold I_pbn_bmt_valid in * .
  intros lbn' pbn' Hin.
  destruct (block_no_eq_dec lbn lbn') as [Heq | Hneq].
    subst lbn'; trivial.
    unfold pbn_in_bmt_lbn in Hin.
    destruct Hin as [Hin | Hin].
      destruct Hin as [x Hin].
      rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin.
      injection Hin; intros; subst bmrdata x.
      assert (pbn_in_bmt_lbn bmt lbn pbn').
        left.
        exists bmrlog.
        trivial.
      eapply HI2; eauto.
    destruct Hin as [x Hin].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin.
    injection Hin; intros; subst x pbn'.
    trivial.
  apply HI2 with lbn'.
  unfold pbn_in_bmt_lbn in Hin |- * .
  destruct Hin as [Hin | Hin].
    left.
    unfold pbn_in_bmt_data in Hin.
    destruct Hin as [x Hin].
    exists x.
    rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq).
    trivial.
  right.
  unfold pbn_in_bmt_log in Hin.
  destruct Hin as [x Hin].
  exists x.
  rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq).
  trivial.
Qed.

Lemma I_pbn_bmt_valid_preserv_bmt_update_data : 
  forall bmt lbn pbn bmt',
    valid_block_no pbn
    -> I_pbn_bmt_valid bmt
    -> bmt_update_data bmt lbn pbn = Some bmt' 
    -> I_pbn_bmt_valid bmt'.
Proof.
  unfold bmt_update_data.
  intros bmt lbn pbn bmt' Hv HI2 Hud.
  destruct (bmt_get bmt lbn) as [[bmrdata bmrlog] | ] eqn:Hget; try discriminate.
  destruct (bmt_update bmt lbn (Some pbn, bmrlog)) as [bmt'' | ] eqn:Hu; try discriminate.
  injection Hud; intro; subst bmt''.
  unfold I_pbn_bmt_valid in * .
  intros lbn' pbn' Hin.
  destruct (block_no_eq_dec lbn lbn') as [Heq | Hneq].
    subst lbn'; trivial.
    unfold pbn_in_bmt_lbn in Hin.
    destruct Hin as [Hin | Hin].
      destruct Hin as [x Hin].
      rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin.
      injection Hin; intros; subst pbn' x.
      trivial.
    destruct Hin as [x Hin].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin.
    injection Hin; intros; subst bmrlog x.
    assert (pbn_in_bmt_lbn bmt lbn pbn').
      right.
      exists bmrdata.
      trivial.
    eapply HI2; eauto.
  apply HI2 with lbn'.
  unfold pbn_in_bmt_lbn in Hin |- * .
  destruct Hin as [Hin | Hin].
    left.
    unfold pbn_in_bmt_data in Hin.
    destruct Hin as [x Hin].
    exists x.
    rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq).
    trivial.
  right.
  unfold pbn_in_bmt_log in Hin.
  destruct Hin as [x Hin].
  exists x.
  rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq).
  trivial.
Qed.

Lemma I_pbn_freebq_valid_preserv_fbq_enq : 
  forall fbq pbn fbq',
    valid_block_no pbn
    -> I_pbn_fbq_valid fbq
    -> fbq_enq fbq pbn = Some fbq'
    -> I_pbn_fbq_valid fbq'.
Proof.
  unfold I_pbn_fbq_valid.
  intros fbq pbn fbq' Hv HI3 Hen.
  intros pbn' Hin'.
  destruct (block_no_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    trivial.
  apply HI3.
  rewrite <- (fbq_in_preserv_fbq_enq pbn' fbq pbn fbq'); eauto.
Qed.

Lemma I_pbn_freebq_state_preserv_fbq_enq : 
  forall bit fbq pbn bi bit' fbq',
    valid_block_no pbn
    -> bit_update bit pbn bi = Some bit'
    -> bi_state bi = bs_invalid
    -> I_pbn_fbq_state bit fbq
    -> fbq_enq fbq pbn = Some fbq'
    -> I_pbn_fbq_state bit' fbq'.
Proof.
  intros bit fbq pbn bi bit' fbq' Hv Hu Hbi HI4 Hen.
  unfold I_pbn_fbq_state in * .
  intros pbn' bi' Hin' Hget'.
  destruct (block_no_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    rewrite (bit_update_bit_get_eq _ _ _ _ Hu) in Hget'.
    injection Hget'; intro; subst bi'.
    left; trivial.
  assert (fbq_in fbq pbn' = true).
    rewrite <- (fbq_in_preserv_fbq_enq _ _ _ _ (neq_sym Hneq) Hen) .
    trivial.
  assert (bit_get bit pbn' = Some bi').
    rewrite <- (bit_update_bit_get_neq _ _ _ _ _ Hu (neq_sym Hneq)).
    trivial.
  eapply HI4; eauto.
Qed.

Lemma pbn_not_in_bmt_bmt_update :
  forall bmt lbn pbn (bmr: bmt_record) bmt',
    pbn_in_bmt_lbn bmt lbn pbn
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> bmt_update bmt lbn bmr = Some bmt'
    -> pbn_not_in_bmr pbn bmr
    -> pbn_not_in_bmt bmt' pbn.
Proof.
  intros bmt lbn pbn bmr bmt'.
  intros Hin HI71 HI72 Hup Hnot.
  unfold pbn_not_in_bmt.
  intro HF.
  unfold pbn_in_bmt in HF.
  destruct HF as [lbn' Hlbn'in].
  assert (Hx: lbn' = lbn \/ lbn' <> lbn).
    destruct (block_no_eq_dec lbn lbn').
      left; auto.
    right; auto.
  destruct Hx as [Heq | Hneq].
    subst lbn'.
    unfold I_pbn_bmt_distinguishable in HI71.
    unfold I_pbn_bmt_distinguishable_2 in HI72.
    unfold pbn_in_bmt_lbn in Hlbn'in.
    assert (H1 := bmt_update_bmt_get_eq _ _ _ _ Hup).
    destruct Hlbn'in as [H2 | H3].
      unfold pbn_in_bmt_data in H2.
      destruct H2 as [x Hx].
      unfold pbn_not_in_bmr in Hnot.
      destruct bmr as [bmr1 bmr2].
      destruct bmr1 as [b1 | ].
      rewrite H1 in Hx.    
      injection Hx.
      intros.
      subst pbn.
      destruct bmr2.
      destruct Hnot.
      apply H0; trivial.
      apply Hnot; trivial.
      rewrite H1 in Hx.    
      discriminate.
    unfold pbn_in_bmt_log in H3.
    destruct H3 as [x Hx].
    unfold pbn_not_in_bmr in Hnot.
    destruct bmr as [bmr1 bmr2].
    destruct bmr1 as [b1 | ].
    destruct bmr2 as [b2 | ].
    rewrite H1 in Hx.    
    injection Hx.
    intros.
    subst pbn.
    destruct Hnot.
    apply H2; trivial.
    rewrite H1 in Hx.    
    discriminate.
    destruct bmr2 as [b2 | ].
    rewrite H1 in Hx.    
    injection Hx.
    intros.
    subst pbn.
    apply Hnot; trivial.
    rewrite H1 in Hx.
    discriminate.
  unfold I_pbn_bmt_distinguishable in HI71.
  unfold pbn_in_bmt_lbn in Hlbn'in.
  destruct Hlbn'in.
  unfold pbn_in_bmt_data in H.
  destruct H as [x Hx].
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hup (neq_sym Hneq)) in Hx.
  assert (H1 : pbn_in_bmt_lbn bmt lbn' pbn).
    unfold pbn_in_bmt_lbn.
    left.
    unfold pbn_in_bmt_data.
    exists x; trivial.
  assert (Hy:= HI71 lbn lbn' pbn pbn (neq_sym Hneq) Hin H1).
  apply Hy; trivial.
  unfold pbn_in_bmt_log in H.
  destruct H as [x Hx].
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hup (neq_sym Hneq)) in Hx.
  assert (H1 : pbn_in_bmt_lbn bmt lbn' pbn).
    unfold pbn_in_bmt_lbn.
    right.
    unfold pbn_in_bmt_log.
    exists x; trivial.
  assert (Hy:= HI71 lbn lbn' pbn pbn (neq_sym Hneq) Hin H1).
  apply Hy; trivial.
Qed.

Lemma pbn_in_bmt_implies_pbn_in_bmt_again :
  forall bmt lbn pbn lbn',
    I_pbn_bmt_distinguishable bmt
    -> pbn_in_bmt_lbn bmt lbn pbn
    -> lbn' <> lbn
    -> ~ pbn_in_bmt_lbn bmt lbn' pbn.
Proof.
  intros bmt lbn pbn lbn'.
  intros HI71 Hin Hneq.
  unfold I_pbn_bmt_distinguishable in HI71.
  intro Hin2.
  apply (HI71 lbn' lbn pbn pbn Hneq Hin2 Hin); trivial.
Qed.

(* 
 Lemmas for I7

 *)

Lemma I_pbn_bmt_distinguishable_preserv_bmt_update_data_none: 
  forall bmt lbn pbn bmt', 
  I_pbn_bmt_distinguishable bmt
  -> bmt_update bmt lbn (Some pbn, None) = Some bmt'
  -> ~ pbn_in_bmt bmt pbn
  -> I_pbn_bmt_distinguishable bmt'.
Proof.
  intros bmt lbn pbn bmt'.
  intros HI71 Hup Hnin.
  unfold I_pbn_bmt_distinguishable in * .
  intros lbn1 lbn2 pbn1 pbn2 Hneq12 Hin11 Hin22.
  destruct (pbn_eq_dec lbn lbn1) as [Heq1 | Hneq1].
  destruct (pbn_eq_dec lbn lbn2) as [Heq2 | Hneq2].

  subst lbn1.
  destruct (Hneq12 Heq2).
  subst lbn1.
  assert (pbn1 = pbn).
    assert (bmt_get bmt' lbn = Some (Some pbn, None)).
      rewrite (bmt_update_bmt_get_eq _ _ _ _ Hup); trivial.
    unfold pbn_in_bmt_lbn in Hin11.
    unfold pbn_in_bmt_data, pbn_in_bmt_log in Hin11.
    destruct Hin11 as [Hin11 | Hin11].
    destruct Hin11 as [x Hin11].
    rewrite Hin11 in H .
    injection H; intros; subst; trivial.
    destruct Hin11 as [x Hin11].
    rewrite Hin11 in H .
    discriminate.
  subst pbn1.
  apply (bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hup Hneq2) in Hin22.
  intro HF.
  subst pbn2.
  unfold pbn_in_bmt in Hnin.
  apply Hnin.
  exists lbn2; trivial.

  destruct (pbn_eq_dec lbn lbn2) as [Heq2 | Hneq2].
  subst lbn2.
  assert (pbn2 = pbn).
    assert (bmt_get bmt' lbn = Some (Some pbn, None)).
      rewrite (bmt_update_bmt_get_eq _ _ _ _ Hup); trivial.
    unfold pbn_in_bmt_lbn in Hin22.
    unfold pbn_in_bmt_data, pbn_in_bmt_log in Hin22.
    destruct Hin22 as [Hin22 | Hin22].
    destruct Hin22 as [x Hin22].
    rewrite Hin22 in H .
    injection H; intros; subst; trivial.
    destruct Hin22 as [x Hin22].
    rewrite Hin22 in H .
    discriminate.
  subst pbn2.
  apply (bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hup Hneq1) in Hin11.
  intro HF.
  subst pbn1.
  unfold pbn_in_bmt in Hnin.
  apply Hnin.
  exists lbn1; trivial.
  
  apply (bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hup Hneq2) in Hin22.
  apply (bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hup Hneq1) in Hin11.
  apply (HI71 lbn1 lbn2); eauto.
Qed.

Lemma I_pbn_bmt_distinguishable_preserv_bmt_update_log: 
  forall bmt lbn pbn bmt', 
  I_pbn_bmt_distinguishable bmt
  -> bmt_update_log bmt lbn pbn = Some bmt'
  -> ~ pbn_in_bmt bmt pbn
  -> I_pbn_bmt_distinguishable bmt'.
Proof.
  intros bmt lbn pbn bmt'.
  unfold bmt_update_log, I_pbn_bmt_distinguishable, pbn_in_bmt.
  intros HI71 Hul Hnin.
  intros lbn1 lbn2 pbn1 pbn2 Hlbn12 Hpbn1 Hpbn2.
  destruct (bmt_get bmt lbn) as [bmr | ] eqn:Hbmt; try discriminate.
  destruct bmr as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) as [bmt'' | ] eqn:Hu; try discriminate.
  injection Hul; intros; subst bmt''.
  destruct (block_no_eq_dec lbn lbn1) as [Heq | Hneq ].
    subst lbn1.
    destruct Hpbn1 as [Hin1 | Hin1].
      destruct Hin1 as [x Hin1].
      assert (Hx := bmt_update_bmt_get_eq _ _ _ _ Hu).
      rewrite Hin1 in Hx.
      injection Hx.
      intros.
      subst x bmrd.
      assert (Hy := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu Hlbn12 Hpbn2).
      eapply HI71; eauto.
      left.
      exists bmrl.
      trivial.
    destruct Hin1 as [x Hin1].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin1.
    injection Hin1; intros; subst x pbn.
    clear Hin1.
    intro Hx.
    subst pbn2.
    assert (Hy := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu Hlbn12 Hpbn2).
    apply Hnin.    
    exists lbn2; trivial.
  destruct (block_no_eq_dec lbn lbn2) as [Heq | Hneq2 ].
    subst lbn2.
    destruct Hpbn2 as [Hin2 | Hin2].
      destruct Hin2 as [x Hin2].
      assert (Hx := bmt_update_bmt_get_eq _ _ _ _ Hu).
      rewrite Hin2 in Hx.
      injection Hx.
      intros.
      subst x bmrd.
      assert (Hy := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu (neq_sym Hlbn12) Hpbn1).
      eapply HI71; eauto.
      left.
      exists bmrl.
      trivial.
    destruct Hin2 as [x Hin2].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hin2.
    injection Hin2; intros; subst x pbn.
    clear Hin2.
    intro Hx.
    subst pbn1.
    assert (Hy := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu (neq_sym Hlbn12) Hpbn1).
    apply Hnin.    
    exists lbn1; trivial.
  assert (Hx := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu Hneq Hpbn1).
  assert (Hy := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu Hneq2 Hpbn2).
  apply (HI71 _ _ _ _ Hlbn12); eauto.
Qed.
      
Lemma I_pbn_bmt_distinguishable_2_preserv_bmt_update_data_none: 
  forall bmt lbn pbn bmt', 
  I_pbn_bmt_distinguishable_2 bmt
  -> bmt_update bmt lbn (Some pbn, None) = Some bmt'
  -> I_pbn_bmt_distinguishable_2 bmt'.
Proof.
  intros bmt lbn pbn bmt' HI72 Hu.
  unfold I_pbn_bmt_distinguishable_2 in * .
  intros lbn' pbn1 pbn2 Hget.
  destruct (block_no_eq_dec lbn lbn') as [Heq | Hneq ].
    subst lbn'.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hget.
    discriminate Hget.
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq) in Hget.
  eapply HI72; eauto.
Qed.

Lemma I_pbn_bmt_distinguishable_2_preserv_bmt_update_log: 
  forall bmt lbn pbn bmt', 
  I_pbn_bmt_distinguishable_2 bmt
  -> bmt_update_log bmt lbn pbn = Some bmt'
  -> ~ pbn_in_bmt bmt pbn
  -> I_pbn_bmt_distinguishable_2 bmt'.
Proof.
  intros bmt lbn pbn bmt' HI72 Hu Hnin.
  unfold I_pbn_bmt_distinguishable_2 in * .
  intros lbn' pbn1 pbn2 Hget.
  unfold bmt_update_log in Hu.
  destruct (bmt_get bmt lbn) as [[bmrd bmrl] | ] eqn:Hg; [ | try discriminate].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) as [bmt'x | ] eqn:Hbu ; [ | try discriminate].
  injection Hu; intros; subst bmt'x.
  clear Hu.
  destruct (block_no_eq_dec lbn lbn') as [Heq | Hneq ].
    subst lbn'.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hbu) in Hget.
    injection Hget; intros; subst bmrd pbn.
    clear Hget.
    intros He.
    subst pbn2.
    apply Hnin.
    exists lbn.
    left.
    exists bmrl.
    trivial.
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hbu Hneq) in Hget.
  eapply HI72; eauto.
Qed.

(* 
 Lemmas for I5

 *)

Lemma I_pbn_bmt_used_preserv_bit_update_irre : 
  forall bit bmt pbn bi bit',
    I_pbn_bmt_used bit bmt
    -> bit_update bit pbn bi = Some bit'
    -> (~ pbn_in_bmt bmt pbn)
    -> I_pbn_bmt_used bit' bmt.
Proof.
  intros bit bmt pbn bi bit' HI5 Hup Hnin.
  unfold I_pbn_bmt_used in * .
  intros lbn pbn' bi' Hget'. 
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    rewrite (bit_update_bit_get_eq _ _ _ _ Hup) in Hget'.
    injection Hget'.
    intro H; subst bi'; clear Hget'.
    split.
      intros H.
      unfold pbn_in_bmt in Hnin.
      apply False_ind.
      apply Hnin.
      exists lbn.
      unfold pbn_in_bmt_lbn.
      left; trivial.
    intros H.
    unfold pbn_in_bmt in Hnin.
    apply False_ind.
    apply Hnin.
    exists lbn.
    unfold pbn_in_bmt_lbn.
    right; trivial.
  rewrite (bit_update_bit_get_neq _ _ _ _ _ Hup (neq_sym Hneq)) in Hget'.
  apply HI5; auto.
Qed.

Lemma I_pbn_bmt_used_preserv_bmt_update_data_none :
  forall bit bmt pbn lbn bi bit' bmt',
    I_pbn_bmt_used bit bmt 
    -> I_pbn_bmt_distinguishable bmt
    -> pbn_not_in_bmt bmt pbn
    -> bmt_update bmt lbn (Some pbn, None) = Some bmt' 
    -> bit_update bit pbn bi = Some bit'
    -> bi_state bi = bs_data lbn
    -> I_pbn_bmt_used bit' bmt'.
Proof.
  intros bit bmt pbn lbn bi bit' bmt'.
  intros HI5 HI71 Hnin Hbmtup Hup Hbs.
  assert (HI71' : I_pbn_bmt_distinguishable bmt').
    eapply I_pbn_bmt_distinguishable_preserv_bmt_update_data_none; eauto.
  unfold I_pbn_bmt_used in * .
  intros lbn' pbn' bi' Hget'.
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    rewrite (bit_update_bit_get_eq _ _ _ _ Hup) in Hget'.
    injection Hget'.
    intro H; subst bi'; clear Hget'.
    split.
      intros H.
      assert (H1: pbn_in_bmt_lbn bmt' lbn' pbn).
        left; trivial.
      assert (H2: pbn_in_bmt_lbn bmt' lbn pbn).
        eapply (bmt_update_pbn_in_bmt_lbn_eq _ _ _ _ _ Hbmtup); eauto.
        simpl; trivial.
      assert (lbn' = lbn).
        destruct (pbn_eq_dec lbn' lbn) as [Hx | Hx]; trivial.
        apply False_ind.
        eapply HI71'; eauto.
      subst lbn'.
      trivial.
    intro H.
    assert (H1: pbn_in_bmt_lbn bmt' lbn' pbn).
      right; trivial.
    assert (H2: pbn_in_bmt_lbn bmt' lbn pbn).
      eapply (bmt_update_pbn_in_bmt_lbn_eq _ _ _ _ _ Hbmtup); eauto.
      simpl; trivial.
    assert (lbn' = lbn).
      destruct (pbn_eq_dec lbn' lbn) as [Hx | Hx]; trivial.
      apply False_ind.
      eapply HI71'; eauto.
    subst lbn'.
    unfold pbn_in_bmt_log in H.
    assert (H3: bmt_get bmt' lbn = Some (Some pbn, None)).
      eapply bmt_update_bmt_get_eq; eauto.
    destruct H as [x H].
    rewrite H in H3.
    discriminate.
  (* pbn <> pbn' *)
  assert (bit_get bit pbn' = Some bi').
    rewrite (bit_update_bit_get_neq _ _ _ _ _ Hup (neq_sym Hneq)) in Hget'.
    trivial.
  destruct (HI5 lbn' pbn' bi' H) as [H1 H2].
  split.
    intro Hx.
    apply H1.
    destruct (pbn_eq_dec lbn lbn') as [Heq1 | Hneq1].
      subst lbn'.
      assert (pbn_in_bmt_data bmt' lbn pbn).
        exists None.
        apply (bmt_update_bmt_get_eq _ _ _ _ Hbmtup).
      assert (pbn = pbn').
        eapply pbn_in_bmt_data_inj; eauto.
      destruct (Hneq H3).

    unfold pbn_in_bmt_data in Hx |- * .
    destruct Hx as [x Hx].
    exists x.
    rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hbmtup Hneq1).
    trivial.
  intro Hx.
  apply H2.
  destruct (pbn_eq_dec lbn lbn') as [Heq1 | Hneq1].
    subst lbn'.
    unfold pbn_in_bmt_log in Hx.
    destruct Hx as [x Hx].
    assert (bmt_get bmt' lbn = Some (Some pbn, None)).
      eapply bmt_update_bmt_get_eq; eauto.
    rewrite H0 in Hx.
    discriminate. 
  unfold pbn_in_bmt_log in Hx |- * .
  destruct Hx as [x Hx].
  exists x.
  rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hbmtup Hneq1).
  trivial.
Qed.

Lemma I_pbn_bmt_used_preserv_bmt_update_log :
  forall bit bmt pbn lbn bi pmt bit' bmt',
    I_pbn_bmt_used bit bmt 
    -> ~ pbn_in_bmt bmt pbn
    -> bmt_update_log bmt lbn pbn = Some bmt'
    -> bit_update bit pbn bi = Some bit'
    -> bi_state bi = bs_log lbn pmt
    -> I_pbn_bmt_used bit' bmt'.
Proof.
  unfold I_pbn_bmt_used.
  intros bit bmt pbn lbn bi pmt bit' bmt' HI5 Hnin Hbmtul Hbitu Hbi.
  intros lbn' pbn' bi' Hget'.
  split.
    intros Hin'.
    destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
      subst pbn'.
      assert (Hin'x := bmt_update_log_pbn_in_bmt_data_preserv_rev _ _ _ _ _ _ Hbmtul Hin').
      apply False_ind.
      apply Hnin.
      exists lbn'.
      left; trivial.
    rewrite (bit_update_bit_get_neq _ _ _ _ _ Hbitu (neq_sym Hneq)) in Hget'.
    assert (Hin'x := bmt_update_log_pbn_in_bmt_data_preserv_rev _ _ _ _ _ _ Hbmtul Hin').
    destruct (HI5 lbn' _ _ Hget') as [HI5_1 HI5_2].
    apply HI5_1; trivial.
  intro Hin'.
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
      subst lbn'.
      rewrite (bit_update_bit_get_eq _ _ _ _ Hbitu) in Hget'.
      injection Hget'; intro; subst bi'; clear Hget'.
      exists pmt; trivial.
    assert (Hin'x := bmt_update_log_pbn_in_bmt_log_preserv_rev _ _ _ _ _ _ Hbmtul Hneq2 Hin').
    apply False_ind.
    apply Hnin.
    exists lbn'.
    right.
    trivial.
  rewrite (bit_update_bit_get_neq _ _ _ _ _ Hbitu (neq_sym Hneq)) in Hget'.
  destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
    subst lbn'.
    assert (Hin'' := bmt_update_log_pbn_in_bmt_log_eq _ _ _ _ Hbmtul).
    assert (pbn = pbn').
      unfold pbn_in_bmt_log in Hin', Hin''.
      destruct Hin' as [x1 Hin'].
      destruct Hin'' as [x2 Hin''].
      rewrite Hin' in Hin''.
      injection Hin''; intro; subst pbn'; trivial.
    subst pbn'.
    destruct (Hneq (refl_equal _)).
  destruct (HI5 lbn' pbn' bi' Hget') as [Hx Hy].
  apply Hy.
  eapply bmt_update_log_pbn_in_bmt_log_preserv_rev; eauto.
Qed.

Lemma I_pbn_bmt_used_preserv_bmt_update_none_log :
  forall bit bmt pbn lbn bi pmt bit' bmt',
    I_pbn_bmt_used bit bmt 
    -> ~ pbn_in_bmt bmt pbn
    -> bmt_update bmt lbn (None, Some pbn) = Some bmt'
    -> bit_update bit pbn bi = Some bit'
    -> bi_state bi = bs_log lbn pmt
    -> I_pbn_bmt_used bit' bmt'.
Proof.
  unfold I_pbn_bmt_used.
  intros bit bmt pbn lbn bi pmt bit' bmt' HI5 Hnin Hbmtu Hbitu Hbi.
  intros lbn' pbn' bi' Hget'.
  split.
    intros Hin'.
    destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
      subst pbn'.
      destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
        subst lbn'.
        destruct Hin' as [x Hbmtget'].
        rewrite (bmt_update_bmt_get_eq _ _ _ _ Hbmtu) in Hbmtget'.
        discriminate Hbmtget'.
      assert (Hin'x := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ pbn _ Hbmtu Hneq2).
      assert (Hinl : pbn_in_bmt_lbn bmt' lbn' pbn).
        left; trivial.
      apply Hin'x in Hinl.
      apply False_ind.
      apply Hnin.
      exists lbn'.
      trivial.
    rewrite (bit_update_bit_get_neq _ _ _ _ _ Hbitu (neq_sym Hneq)) in Hget'.
      destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
        subst lbn'.
        destruct Hin' as [x Hbmtget'].
        rewrite (bmt_update_bmt_get_eq _ _ _ _ Hbmtu) in Hbmtget'.
        discriminate Hbmtget'.
    assert (Hin'2: pbn_in_bmt_lbn bmt' lbn' pbn').
      left; trivial.
    assert (Hin'x := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hbmtu Hneq2 Hin'2).
    destruct (HI5 lbn' _ _ Hget') as [HI5_1 HI5_2].
    apply HI5_1; trivial.
    unfold pbn_in_bmt_data in Hin' .
    destruct Hin' as [x Hin'].
    rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hbmtu Hneq2) in Hin'.
    exists x; trivial.
  intro Hinl'.
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
      subst lbn'.
      rewrite (bit_update_bit_get_eq _ _ _ _ Hbitu) in Hget'.
      injection Hget'; intro; subst bi'; clear Hget'.
      exists pmt; trivial.
    assert (Hin'x := bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ pbn _ Hbmtu Hneq2).
    assert (Hin' : pbn_in_bmt_lbn bmt' lbn' pbn).
      right; trivial.
    apply Hin'x in Hin'.
    apply False_ind.
    apply Hnin.
    exists lbn'.
    trivial.
  rewrite (bit_update_bit_get_neq _ _ _ _ _ Hbitu (neq_sym Hneq)) in Hget'.
  destruct (pbn_eq_dec lbn lbn') as [Heq2 | Hneq2].
    subst lbn'.
    destruct Hinl' as [x Hinl'].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hbmtu) in Hinl'.
    injection Hinl'; intros; subst pbn'; clear Hinl'.
    destruct (Hneq (refl_equal _)).
  destruct (HI5 lbn' pbn' bi' Hget') as [Hx Hy].
  apply Hy.
  destruct Hinl' as [x Hinl'].
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hbmtu Hneq2) in Hinl'.
  exists x; trivial.
Qed.

Lemma I_pbn_bmt_used_preserv_write_log_block: 
  forall bit bmt pbn lbn bi bit',
    I_pbn_bmt_used bit bmt
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> bit_update bit pbn bi = Some bit'
    -> pbn_in_bmt_log bmt lbn pbn
    -> (exists pmt, bi_state bi = bs_log lbn pmt)
    -> I_pbn_bmt_used bit' bmt.
Proof.
  intros bit bmt pbn lbn bi bit' HI5 HI7_1 HI7_2 Hup Hin Hbs.
  unfold I_pbn_bmt_used in * .
  intros lbn' pbn' bi' Hget'.
  assert (pbn' = pbn \/ pbn' <> pbn).
    destruct (block_no_eq_dec pbn pbn').
      left; auto.
    right; auto.
  destruct H.
    subst pbn'.
    split.
      destruct (block_no_eq_dec lbn lbn').
        subst lbn'.
        intro Hx.
        unfold pbn_in_bmt_data in Hx.
        destruct Hx as [x Hx].
        destruct Hin as [y Hy].
        rewrite Hy in Hx.
        injection Hx.
        intros; subst x y.
        destruct (HI7_2 lbn pbn pbn Hy (refl_equal _)). 
      intros Hx.
      destruct (HI7_1 lbn lbn' pbn pbn H (or_intror Hin) (or_introl Hx) (refl_equal _)).
    intros Hx.
    assert (bi = bi').
      rewrite (bit_update_bit_get_eq _ _ _ _ Hup) in Hget'.
      injection Hget'; auto.
    subst bi'.
    assert (lbn' = lbn \/ lbn <> lbn').
      destruct (block_no_eq_dec lbn lbn'); auto.
    destruct H.
      subst lbn'.
      trivial.
    assert (HF := HI7_1 lbn lbn' pbn pbn H). 
    apply False_ind.
    apply HF.
    right; trivial.
    right; trivial.
    trivial.
  apply HI5.
  erewrite <- bit_update_bit_get_neq; eauto.
Qed.

(* Lemma lbn_pbn_in_bmt_after_bmt_update_lbn : *)
Lemma pbn_in_bmt_after_bmt_update_lbn :
  forall bmt lbn pbn bmr bmt',
    pbn_in_bmt_lbn bmt lbn pbn
    -> I_pbn_bmt_distinguishable bmt
    -> bmt_update bmt lbn bmr = Some bmt'
    -> ~ pbn_in_bmr pbn bmr 
    -> ~ pbn_in_bmt bmt' pbn.
Proof.
  intros bmt lbn pbn bmr bmt' Hin HI71 Hu Hnin.
  intro Hnin'.
  unfold pbn_in_bmt in * .
  destruct Hnin' as [lbn' Hnin'].
  destruct (pbn_eq_dec lbn lbn') as [Heq | Hneq].
  subst lbn'. 
    apply Hnin.
    destruct (pbn_in_bmt_lbn_bmt_get _ _ _ Hnin') as [bmrx [Hget' Hxin]].
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu) in Hget'.
    injection Hget'; intro; subst bmrx; clear Hget'.
    trivial.
  assert (Hin':= bmt_update_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hu Hneq Hnin').
  assert (Hx := HI71  _ _ _ _ Hneq Hin Hin').
  apply Hx; trivial.
Qed.

(* ---------------------------------------------------------------- *)

Lemma I_pbn_habitation_implies_I_bmt_fbq_distinguiable:  (* Derivable Invariant *)
  forall bmt fbq ,
    I_pbn_habitation bmt fbq
    -> I_bmt_fbq_distinguiable bmt fbq.
Proof.
  intros bmt fbq HI6 pbn pbn' lbn Hpbn Hpbn' Hinbmt Hinfbq.
  assert (Hx := I_pbn_habitation_in_fbq_implies_not_in_bmt pbn' bmt fbq Hpbn' HI6 Hinfbq); trivial.
  intro Heq.
  subst pbn'.
  apply Hx.
  exists lbn.
  destruct Hinbmt.
  left; trivial.
  right; trivial.
Qed.

(* ---------------------------------------------------------------- *)
(* I8 Lemmas *)

Lemma I_pbn_fbq_distinguishable_implies_fbq_deq_fbq_not_in : 
  forall fbq pbn fbq',
    I_pbn_fbq_distinguishable fbq
    -> fbq_deq fbq = Some (pbn, fbq') 
    -> fbq_in fbq' pbn = false.
Proof.
  unfold I_pbn_fbq_distinguishable.
  intros fbq pbn fbq' HI8 Hdeq.
  assert (Hg1 : fbq_get fbq 0 = Some pbn).
    apply fbq_deq_fbq_get with fbq'; trivial.
  destruct (fbq_in fbq' pbn) eqn:HF; trivial.
  destruct (fbq_in_fbq_get _ _ HF) as [i Hgi].
  assert (Hg2:= fbq_get_fbq_rdeq_fbq_get _ _ _ _ _ Hgi Hdeq).
  apply False_ind.
  apply (HI8 0 (S i) pbn pbn); trivial.
Qed.

Lemma I_pbn_fbq_distinguishable_preserv_fbq_enq :
  forall fbq pbn fbq',
    I_pbn_fbq_distinguishable fbq
    -> fbq_in fbq pbn = false
    -> fbq_enq fbq pbn = Some fbq'
    -> I_pbn_fbq_distinguishable fbq'.
Proof.
  unfold I_pbn_fbq_distinguishable.
  intros fbq pbn fbq' HI8 Hin Henq.
  intros i1 i2 pbn1 pbn2 Hi1i2  Hg1 Hg2.

  destruct (fbq_get_fbq_enq_fbq_get_rev fbq fbq' i1 pbn1 pbn Henq Hg1) as [[Hpbn1  Hi1] | Hg1' ].
    destruct (fbq_get_fbq_enq_fbq_get_rev fbq fbq' i2 pbn2 pbn Henq Hg2) as [[Hpbn2  Hi2] | Hg2' ].
      subst i1 i2.
      destruct (Hi1i2 (refl_equal _)).
    subst pbn1.
    intro HF.
    subst pbn2.
    apply (fbq_not_in_fbq_get_some_implies_false _ _ Hin _ Hg2').
  destruct (fbq_get_fbq_enq_fbq_get_rev fbq fbq' i2 pbn2 pbn Henq Hg2) as [[Hpbn2  Hi2] | Hg2' ].
    subst pbn2.
    intro HF.
    subst pbn1.
    apply (fbq_not_in_fbq_get_some_implies_false _ _ Hin _ Hg1').
  apply (HI8 i1 i2); trivial.
Qed.

Lemma I_pbn_fbq_distinguishable_preserv_fbq_deq: 
  forall fbq pbn fbq',
    I_pbn_fbq_distinguishable fbq
    -> fbq_deq fbq = Some (pbn, fbq')
    -> I_pbn_fbq_distinguishable fbq'.
Proof.
  unfold I_pbn_fbq_distinguishable.
  intros fbq pbn fbq' HI8 Hdeq.
  intros i1 i2 pbn1 pbn2 Hi1i2  Hg1 Hg2.
  apply (HI8 (S i1) (S i2) pbn1 pbn2).
    auto with arith.
    apply (fbq_get_fbq_deq_fbq_get_rev _ _ _ _ _ Hdeq); trivial.
  apply (fbq_get_fbq_deq_fbq_get_rev _ _ _ _ _ Hdeq); trivial.
Qed.

(* ---------------------------------------------------------------- *)
(* I6 Lemmas *)
Lemma I_pbn_habitation_alloc_merge : (* an ad hoc lemma *)
  forall bmt fbq lbn pbnx pbn1 pbn2 bmt' fbq' fbq'' fbq''',
    I_pbn_habitation bmt fbq
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> I_pbn_fbq_distinguishable fbq
    -> valid_block_no pbn1
    -> valid_block_no pbn2
    -> valid_block_no pbnx
    -> bmt_get bmt lbn = Some (Some pbn1, Some pbn2)
    -> fbq_deq fbq = Some (pbnx, fbq')
    -> bmt_update bmt lbn (Some pbnx, None) = Some bmt'
    -> fbq_enq fbq' pbn2 = Some fbq''
    -> fbq_enq fbq'' pbn1 = Some fbq'''
    -> I_pbn_habitation bmt' fbq'''.
Proof.
  intros bmt fbq lbn pbnx pbn1 pbn2 bmt' fbq' fbq'' fbq'''.
  intros HI6 HI7_1 HI7_2 HI8 Hpbn1 Hpbn2 Hpbnx Hlbn Hdeq Hbmtup Henq1 Henq2.
  unfold I_pbn_habitation in * .
  intros pbn Hpbnv.
  assert (Hn12 : pbn1<>pbn2).
     apply (HI7_2 lbn pbn1 pbn2); trivial.
  assert (Hn1x : pbn1<>pbnx).
    intro HF.
    subst pbnx.
    destruct (HI6 pbn1 Hpbn1) as [Hx | Hx].
      destruct Hx as [[lbn' Hy1] Hy2].
      rewrite (fbq_deq_fbq_in fbq pbn1 fbq') in Hy2; trivial.
      discriminate.
    destruct Hx as [Hx1 Hx2].
    apply (Hx1 lbn).
    left.
    exists (Some pbn2).
    trivial.
  assert (Hn2x : pbn2<>pbnx).
    intro HF.
    subst pbnx.
    destruct (HI6 pbn2 Hpbn2) as [Hx | Hx].
      destruct Hx as [[lbn' Hy1] Hy2].
      rewrite (fbq_deq_fbq_in fbq pbn2 fbq') in Hy2; trivial.
      discriminate.
    destruct Hx as [Hx1 Hx2].
    apply (Hx1 lbn).
    right.
    exists (Some pbn1).
    trivial.
  destruct (block_no_eq_dec pbn pbn1)  as [H1 | H2].
    subst pbn.
    right.
    assert (Hx : pbn_not_in_bmt bmt' pbn1).
      assert (Hin : pbn_in_bmt_lbn bmt lbn pbn1).
        left.
        exists (Some pbn2).
        trivial.
      assert (Hnin: ~ pbn_in_bmr pbn1 (Some pbnx, None)).
        unfold pbn_in_bmr.
        trivial.
      apply (pbn_in_bmt_after_bmt_update_lbn _ _ _ _ _ Hin HI7_1 Hbmtup Hnin).
    split.
      intro lbn'.
      unfold pbn_not_in_bmt in Hx.
      unfold pbn_in_bmt in Hx.
      intro HF.
      apply Hx.      
      exists lbn'; trivial. 
      apply fbq_enq_fbq_in with fbq''; trivial.
  destruct (pbn_eq_dec pbn pbn2) as [H21 | H22].
    subst pbn.
    right.
    assert (Hx : pbn_not_in_bmt bmt' pbn2).
      assert (Hin : pbn_in_bmt_lbn bmt lbn pbn2).
        right.
        exists (Some pbn1).
        trivial.
      assert (Hnin: ~ pbn_in_bmr pbn2 (Some pbnx, None)).
        unfold pbn_in_bmr.
        trivial.
      apply (pbn_in_bmt_after_bmt_update_lbn _ _ _ _ _ Hin HI7_1 Hbmtup Hnin).
    split.
      intro lbn'.
      unfold pbn_not_in_bmt in Hx.
      unfold pbn_in_bmt in Hx.
      intro HF.
      apply Hx.      
      exists lbn'; trivial.
      rewrite (fbq_in_preserv_fbq_enq pbn2 fbq'' pbn1 fbq'''); eauto.
      apply fbq_enq_fbq_in with fbq'; trivial.
  assert (Hdec : pbn = pbnx \/ pbn <> pbnx).
    apply (pbn_eq_dec pbn pbnx); trivial.
  destruct Hdec as [H31 | H32].
    subst pbnx.
    left.
    split.
      exists lbn.
      unfold pbn_in_bmt_lbn.
      left.
      exists None.
      apply bmt_update_bmt_get_eq with bmt; trivial.
    apply (fbq_not_in_preserv_fbq_enq fbq'' pbn fbq''' pbn1); auto.
    apply (fbq_not_in_preserv_fbq_enq fbq' pbn fbq'' pbn2); auto.
    apply (I_pbn_fbq_distinguishable_implies_fbq_deq_fbq_not_in fbq pbn fbq'); trivial.
    
  destruct (HI6 pbn Hpbnv) as [H | H].
    destruct H as [[lbn' Hlbn'] Hqnin].
    assert (lbn' <> lbn).
      intro HF.
      subst lbn'.
      unfold pbn_in_bmt_lbn in Hlbn'.
      destruct Hlbn' as [Hlbn' | Hlbn'].
        destruct Hlbn' as [x Hlbn'].
        rewrite Hlbn in Hlbn'.
        injection Hlbn'.
        intros Hx1 Hx2.
        apply H2.
        auto.
      destruct Hlbn' as [x Hlbn'].
      rewrite Hlbn in Hlbn'.
      injection Hlbn'.
      intros Hx1 Hx2.
      apply H22.
      subst pbn2.
      trivial.
    left.
    split.
      exists lbn'.
      apply (bmt_update_pbn_in_bmt_lbn_neq bmt lbn _ bmt' lbn' pbn Hbmtup H) in Hlbn'; eauto.
    apply (fbq_not_in_preserv_fbq_enq fbq'' pbn fbq''' pbn1); auto.
    apply (fbq_not_in_preserv_fbq_enq fbq' pbn fbq'' pbn2); auto.
    apply (fbq_not_in_preserv_fbq_deq fbq pbn fbq' pbnx); auto.
  right.
  destruct H as [Hx1 Hx2].
  split.    
    intros lbn'.
    intro HF.
    apply (Hx1 lbn').
    assert (lbn' <> lbn).
      intros Hy.
      subst lbn'.
      assert (bmt_get bmt' lbn = Some (Some pbnx, None)).
        apply (bmt_update_bmt_get_eq bmt lbn _ bmt' Hbmtup); trivial.
      unfold pbn_in_bmt_lbn in HF.
      destruct HF as [HF | HF].
        unfold pbn_in_bmt_data in HF.
        destruct HF as [x Hg].
        rewrite Hg in H.
        injection H.
        intros.
        apply H32.
        trivial.
      unfold pbn_in_bmt_log in HF.
      destruct HF as [x Hg].
      rewrite Hg in H.
      discriminate.
    apply (bmt_update_pbn_in_bmt_lbn_neq_rev bmt bmt' lbn lbn' pbn _ Hbmtup) in HF; eauto.

  rewrite (fbq_in_preserv_fbq_enq pbn fbq'' pbn1 fbq'''); auto.
  rewrite (fbq_in_preserv_fbq_enq pbn fbq' pbn2 fbq''); auto.
  rewrite (fbq_in_preserv_fbq_deq fbq pbn fbq' pbnx ); auto.
Qed.    

Lemma I_pbn_habitation_alloc_merge_2 : (* an ad hoc lemma *)
  forall bmt fbq lbn pbnx pbn2 bmt' fbq' fbq'',
    I_pbn_habitation bmt fbq
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> I_pbn_fbq_distinguishable fbq
    -> valid_block_no pbn2
    -> valid_block_no pbnx
    -> bmt_get bmt lbn = Some (None, Some pbn2)
    -> fbq_deq fbq = Some (pbnx, fbq')
    -> bmt_update bmt lbn (Some pbnx, None) = Some bmt'
    -> fbq_enq fbq' pbn2 = Some fbq''
    -> I_pbn_habitation bmt' fbq''.
Proof.
  intros bmt fbq lbn pbnx pbn2 bmt' fbq' fbq''.
  intros HI6 HI7_1 HI7_2 HI8 Hpbn2 Hpbnx Hlbn Hdeq Hbmtup Henq.
  unfold I_pbn_habitation in * .
  intros pbn Hpbnv.
  assert (Hn2x : pbn2<>pbnx).
    intro HF.
    subst pbnx.
    destruct (HI6 pbn2 Hpbn2) as [Hx | Hx].
      destruct Hx as [[lbn' Hy1] Hy2].
      rewrite (fbq_deq_fbq_in fbq pbn2 fbq') in Hy2; trivial.
      discriminate.
    destruct Hx as [Hx1 Hx2].
    apply (Hx1 lbn).
    right.
    exists (None).
    trivial.
  destruct (pbn_eq_dec pbn pbn2) as [H21 | H22].
    subst pbn.
    right.
    assert (Hx : pbn_not_in_bmt bmt' pbn2).
      assert (Hin : pbn_in_bmt_lbn bmt lbn pbn2).
        right.
        exists None.
        trivial.
      assert (Hnin: ~ pbn_in_bmr pbn2 (Some pbnx, None)).
        unfold pbn_in_bmr.
        trivial.
      apply (pbn_in_bmt_after_bmt_update_lbn _ _ _ _ _ Hin HI7_1 Hbmtup Hnin).
    split.
      intro lbn'.
      unfold pbn_not_in_bmt in Hx.
      unfold pbn_in_bmt in Hx.
      intro HF.
      apply Hx.      
      exists lbn'; trivial.
      apply fbq_enq_fbq_in with fbq'; trivial.
  assert (Hdec : pbn = pbnx \/ pbn <> pbnx).
    apply (pbn_eq_dec pbn pbnx); trivial.
  destruct Hdec as [H31 | H32].
    subst pbnx.
    left.
    split.
      exists lbn.
      unfold pbn_in_bmt_lbn.
      left.
      exists None.
      apply bmt_update_bmt_get_eq with bmt; trivial.
    apply (fbq_not_in_preserv_fbq_enq fbq' pbn fbq'' pbn2); auto.

    apply (I_pbn_fbq_distinguishable_implies_fbq_deq_fbq_not_in fbq pbn fbq'); trivial.

  destruct (HI6 pbn Hpbnv) as [H | H].
    destruct H as [[lbn' Hlbn'] Hqnin].
    assert (lbn' <> lbn).
      intro HF.
      subst lbn'.
      unfold pbn_in_bmt_lbn in Hlbn'.
      destruct Hlbn' as [Hlbn' | Hlbn'].
        destruct Hlbn' as [x Hlbn'].
        rewrite Hlbn in Hlbn'.
        discriminate.
      destruct Hlbn' as [x Hlbn'].
      rewrite Hlbn in Hlbn'.
      injection Hlbn'.
      intros Hx1 Hx2.
      apply H22.
      subst pbn2.
      trivial.
    left.
    split.
      exists lbn'.
      apply (bmt_update_pbn_in_bmt_lbn_neq bmt lbn _ bmt' lbn' pbn Hbmtup H) in Hlbn'; eauto.
    apply (fbq_not_in_preserv_fbq_enq fbq' pbn fbq'' pbn2); auto.
    apply (fbq_not_in_preserv_fbq_deq fbq pbn fbq' pbnx); auto.
  right.
  destruct H as [Hx1 Hx2].
  split.    
    intros lbn'.
    intro HF.
    apply (Hx1 lbn').
    assert (lbn' <> lbn).
      intros Hy.
      subst lbn'.
      assert (bmt_get bmt' lbn = Some (Some pbnx, None)).
        apply (bmt_update_bmt_get_eq bmt lbn _ bmt' Hbmtup); trivial.
      unfold pbn_in_bmt_lbn in HF.
      destruct HF as [HF | HF].
        unfold pbn_in_bmt_data in HF.
        destruct HF as [x Hg].
        rewrite Hg in H.
        injection H.
        intros.
        apply H32.
        trivial.
      unfold pbn_in_bmt_log in HF.
      destruct HF as [x Hg].
      rewrite Hg in H.
      discriminate.
    apply (bmt_update_pbn_in_bmt_lbn_neq_rev bmt bmt' lbn lbn' pbn _ Hbmtup) in HF; eauto.

  rewrite (fbq_in_preserv_fbq_enq pbn fbq' pbn2 fbq''); auto.
  rewrite (fbq_in_preserv_fbq_deq fbq pbn fbq' pbnx ); auto.
Qed.

Lemma I_pbn_habitation_preserv_bmt_update_log: 
  forall bmt fbq lbn pbn1 pbn2 bmt' fbq',
    I_pbn_habitation bmt fbq
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> I_pbn_fbq_distinguishable fbq
    -> valid_block_no pbn1
    -> valid_block_no pbn2
    -> bmt_get bmt lbn = Some (Some pbn1, None)
    -> fbq_deq fbq = Some (pbn2, fbq')
    -> bmt_update_log bmt lbn pbn2 = Some bmt'
    -> I_pbn_habitation bmt' fbq'.
Proof.
  intros bmt fbq lbn pbn1 pbn2 bmt' fbq'. 
  intros HI6 HI7_1 HI7_2 HI8 Hpbn1 Hpbn2 Hget Hdeq Hul.
  unfold I_pbn_habitation in * .
  intros pbn Hpbnv.
  assert (Hn1x : pbn1<>pbn2).
    intro HF.
    subst pbn2.
    destruct (HI6 pbn1 Hpbn1) as [Hx | Hx].
      destruct Hx as [[lbn' Hy1] Hy2].
      rewrite (fbq_deq_fbq_in fbq pbn1 fbq') in Hy2; trivial.
      discriminate.
    destruct Hx as [Hx1 Hx2].
    apply (Hx1 lbn).
    left.
    exists (None).
    trivial.
  destruct (pbn_eq_dec pbn pbn1) as [H11 | H12].
    subst pbn.
    left.
    split.
      exists lbn.
      left.
      apply (bmt_update_log_pbn_in_bmt_data_preserv _ _ _ _ _ _ Hul).
      exists None; trivial.
    apply (fbq_not_in_preserv_fbq_deq fbq pbn1 fbq' pbn2); auto.
    destruct (HI6 pbn1 Hpbn1).
      destruct H as [[lbn' H1] H2]; trivial.
    destruct H as [H1 H2].
    apply False_ind.
    apply (H1 lbn).
    left; exists (None); trivial.
  destruct (pbn_eq_dec pbn pbn2) as [H21 | H22].
    subst pbn.
    left.
    split.
      exists lbn.
      right.
      apply (bmt_update_log_pbn_in_bmt_log_eq _ _ _ _ Hul).
    apply (I_pbn_fbq_distinguishable_implies_fbq_deq_fbq_not_in fbq pbn2 fbq'); trivial.
    
  destruct (HI6 pbn Hpbnv) as [H | H].
    destruct H as [[lbn' Hlbn'] Hqnin].
    assert (lbn' <> lbn).
      intro HF.
      subst lbn'.
      unfold pbn_in_bmt_lbn in Hlbn'.
      destruct Hlbn' as [Hlbn' | Hlbn'].
        destruct Hlbn' as [x Hlbn'].
        rewrite Hget in Hlbn'.
        apply H12.
        injection Hlbn'; auto.
      destruct Hlbn' as [x Hlbn'].
      rewrite Hget in Hlbn'.
      discriminate.
    left.
    split.
      exists lbn'.
      apply (bmt_update_log_pbn_in_bmt_lbn_neq bmt lbn _ bmt' lbn' pbn Hul (neq_sym H)) in Hlbn'; eauto.
    apply (fbq_not_in_preserv_fbq_deq fbq pbn fbq' pbn2); auto.
  right.
  destruct H as [Hx1 Hx2].
  split.    
    intros lbn'.
    intro HF.
    apply (Hx1 lbn').
    assert (lbn' <> lbn).
      intros Hy.
      subst lbn'.
      destruct HF.
        apply (Hx1 lbn).
        left.
        apply (bmt_update_log_pbn_in_bmt_data_preserv_rev _ _ _ _ _ _ Hul H); auto.
      apply H22.
      apply pbn_in_bmt_log_inj with bmt' lbn; trivial.
      apply bmt_update_log_pbn_in_bmt_log_eq with bmt; auto.
    apply (bmt_update_log_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hul (neq_sym H)) in HF; eauto.
  rewrite (fbq_in_preserv_fbq_deq fbq pbn fbq' pbn2 ); auto.
Qed.

Lemma I_pbn_habitation_preserv_bmt_update_log_case2: 
  forall bmt fbq lbn pbn2 bmt' fbq',
    I_pbn_habitation bmt fbq
    -> I_pbn_bmt_distinguishable bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> I_pbn_fbq_distinguishable fbq
    -> valid_block_no pbn2
    -> bmt_get bmt lbn = Some (None, None)
    -> fbq_deq fbq = Some (pbn2, fbq')
    -> bmt_update_log bmt lbn pbn2 = Some bmt'
    -> I_pbn_habitation bmt' fbq'.
Proof.
  intros bmt fbq lbn pbn2 bmt' fbq'. 
  intros HI6 HI7_1 HI7_2 HI8 Hpbn2 Hget Hdeq Hul.
  unfold I_pbn_habitation in * .
  intros pbn Hpbnv.
  destruct (pbn_eq_dec pbn pbn2) as [H21 | H22].
    subst pbn.
    left.
    split.
      exists lbn.
      right.
      apply (bmt_update_log_pbn_in_bmt_log_eq _ _ _ _ Hul).
    apply (I_pbn_fbq_distinguishable_implies_fbq_deq_fbq_not_in fbq pbn2 fbq'); trivial.
    
  destruct (HI6 pbn Hpbnv) as [H | H].
    destruct H as [[lbn' Hlbn'] Hqnin].
    assert (lbn' <> lbn).
      intro HF.
      subst lbn'.
      unfold pbn_in_bmt_lbn in Hlbn'.
      destruct Hlbn' as [Hlbn' | Hlbn'].
        destruct Hlbn' as [x Hlbn'].
        rewrite Hget in Hlbn'.
        discriminate.
      destruct Hlbn' as [x Hlbn'].
      rewrite Hget in Hlbn'.
      discriminate.
    left.
    split.
      exists lbn'.
      apply (bmt_update_log_pbn_in_bmt_lbn_neq bmt lbn _ bmt' lbn' pbn Hul (neq_sym H)) in Hlbn'; eauto.
    apply (fbq_not_in_preserv_fbq_deq fbq pbn fbq' pbn2); auto.
  right.
  destruct H as [Hx1 Hx2].
  split.    
    intros lbn'.
    intro HF.
    apply (Hx1 lbn').
    assert (lbn' <> lbn).
      intros Hy.
      subst lbn'.
      destruct HF.
        apply (Hx1 lbn).
        left.
        apply (bmt_update_log_pbn_in_bmt_data_preserv_rev _ _ _ _ _ _ Hul H); auto.
      apply H22.
      apply pbn_in_bmt_log_inj with bmt' lbn; trivial.
      apply bmt_update_log_pbn_in_bmt_log_eq with bmt; auto.
    apply (bmt_update_log_pbn_in_bmt_lbn_neq_rev _ _ _ _ _ _ Hul (neq_sym H)) in HF; eauto.
  rewrite (fbq_in_preserv_fbq_deq fbq pbn fbq' pbn2 ); auto.
Qed.

Lemma I_valid_lbn_has_entry_in_bmt_preserv_bmt_update : 
  forall bmt lbn bmr bmt',
    I_valid_lbn_has_entry_in_bmt bmt
    -> bmt_update bmt lbn bmr = Some bmt'
    -> I_valid_lbn_has_entry_in_bmt bmt'.
Proof.
  unfold I_valid_lbn_has_entry_in_bmt.
  intros bmt lbn bmr bmt' HI10 Hu.
  intros lbn'.
  destruct (pbn_eq_dec lbn lbn') as [Heq | Hneq ].
    subst lbn'.
    destruct (HI10 lbn) as [H1 H2].
    split.
      intro Hlbn.
      rewrite (bmt_update_bmt_get_eq _ _ _ _ Hu).
      exists bmr; trivial.
    intros [bme Hlbn].
    apply H2; trivial.
    apply (bmt_update_bmt_get_eq_rev _ _ _ _ Hu); trivial.
  split.
    intro Hlbn'.
    destruct (HI10 lbn') as [H1 H2].
    rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq).
    apply H1; trivial.
  intros [bmr' H'].
  destruct (HI10 lbn') as [H1 H2].
  apply H2.
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hu Hneq) in H'.
  exists bmr'; trivial.
Qed.

Lemma I_valid_lbn_has_entry_in_bmt_preserv_bmt_update_log : 
  forall bmt lbn pbn bmt',
    I_valid_lbn_has_entry_in_bmt bmt
    -> bmt_update_log bmt lbn pbn = Some bmt'
    -> I_valid_lbn_has_entry_in_bmt bmt'.
Proof.
  unfold I_valid_lbn_has_entry_in_bmt.
  intros bmt lbn pbn bmt' HI10 Hul.
  intros lbn'.
  destruct (pbn_eq_dec lbn lbn') as [Heq | Hneq ].
    subst lbn'.
    destruct (HI10 lbn) as [H1 H2].
    split.
      intro Hlbn.
      assert (Hx := bmt_update_log_pbn_in_bmt_log_eq _ _ _ _ Hul).
      destruct Hx as [x Hl].
      rewrite Hl.
      eexists; eauto.
    intros [bme Hlbn].
    apply H2; trivial.
    apply (bmt_update_log_bmt_get_eq_rev _ _ _ _ Hul); trivial.
  split.
    intro Hlbn'.
    destruct (HI10 lbn') as [H1 H2].
    rewrite (bmt_update_log_bmt_get_neq _ _ _ _ _ Hul Hneq).
    apply H1; trivial.
  intros [bmr' H'].
  destruct (HI10 lbn') as [H1 H2].
  apply H2.
  rewrite (bmt_update_log_bmt_get_neq _ _ _ _ _ Hul Hneq) in H'.
  exists bmr'; trivial.
Qed.

(* ---------------------------------------------------------------- *)

Lemma I_pbn_bmt_used_implies_pbn_is_used :
  forall bit bmt pbn lbn bi,
  I_pbn_bmt_used bit bmt
  -> bit_get bit pbn = Some bi
  -> pbn_in_bmt_lbn bmt lbn pbn 
  -> check_used_block bi = true.
Proof.
  intros.
  unfold I_pbn_bmt_used in H.
  destruct (H lbn pbn bi H0) as [Hx Hy].
  unfold pbn_in_bmt_lbn in H1.
  destruct H1.
    unfold check_used_block.
    rewrite (Hx H1). trivial.
  destruct (Hy H1) as [pmt Hbs].
  unfold check_used_block.
  rewrite Hbs; trivial.
Qed.

Lemma J_bi_block_coherent_preserv_used_set_invalid : 
  forall bit c pbn bi bit',
    J_bi_block_coherent c bit
    -> bit_get bit pbn = Some bi
    -> check_used_block bi = true
    -> bit_update bit pbn (bi_set_state bi bs_invalid) = Some bit'
    -> J_bi_block_coherent c bit'.
Proof.
  intros bit c pbn bi bit' HJ Hget Hck Hup.
  unfold J_bi_block_coherent in * .
  intros pbn' bi' Hget'.
  unfold chip_bi_coherent.
  assert (Hdec: pbn = pbn' \/ pbn <> pbn').
    apply (pbn_eq_dec pbn pbn'); trivial.
  destruct Hdec as [Heq | Hneq].
    subst pbn'.
    assert (bi' = bi_set_state bi bs_invalid).
      rewrite (bit_update_bit_get_eq bit pbn (bi_set_state bi bs_invalid) bit') in Hget'; trivial.
      injection Hget'.
      intros; auto.
    assert (Hx := HJ pbn bi Hget).
    unfold chip_bi_coherent in Hx.
    destruct Hx as [b [Hb Hx]].
    exists b.
    split; trivial.
    rewrite H.
    unfold bi_set_state.
    simpl.
    destruct (check_used_implies_check_data_log Hck) as [Hck1 | Hck2].
      unfold check_data_block in Hck1.
      destruct (bi_state bi); try discriminate.
      unfold block_coherent_data in Hx.
      destruct Hx as [lbn' [_ [_ [Hx _]]]].
      trivial.
    unfold check_log_block in Hck2.
    destruct (bi_state bi); try discriminate.
    unfold block_coherent_log in Hx.
    destruct Hx as [pmt' [lbn' [_ [_ [Hx _]]]]].
    trivial.
  apply HJ.
  rewrite <- (bit_update_bit_get_neq bit pbn' bit' (bi_set_state bi bs_invalid) pbn) ; eauto.
Qed.

Lemma J_bi_block_coherent_preserv_write_block_log :
  forall c bit pbn bi b' c' bit',
    J_bi_block_coherent c bit
    -> bit_update bit pbn bi = Some bit'
    -> chip_get_block c' pbn = Some b'
    -> (forall pbn' : block_no,
          pbn' <> pbn -> chip_get_block c' pbn' = chip_get_block c pbn')
    -> block_coherent_log bi b'
    -> J_bi_block_coherent c' bit'.
Proof.
  intros.
  unfold J_bi_block_coherent in * .
  intros pbn'  bi' Hgetbi'.
  unfold chip_bi_coherent in * .
  assert (Hdec: pbn' = pbn \/ pbn' <> pbn).
    destruct (nat_eq_dec pbn' pbn).
    left; trivial.
    right; trivial.
  destruct Hdec as [Heq | Hneq].
    subst pbn'.
    assert (bi = bi').
      erewrite bit_update_bit_get_eq in Hgetbi'; eauto.
      injection Hgetbi'.
      trivial.
    subst bi'.
    exists b'.
    split; trivial.
    unfold block_coherent_log in H3.
    destruct ((fun x => x) H3) as [pmt [lbn [H4 [H5 H6]]]].
    rewrite H4.
    trivial.
  assert (H4: bit_get bit pbn' = Some bi').
    erewrite <- (bit_update_bit_get_neq bit pbn' bit' bi pbn); eauto.
  destruct (H pbn' bi' H4) as [b [Hb Hx]].
  exists b.
  split; trivial.
  erewrite H2; eauto.
Qed.  

Lemma J_bi_block_coherent_preserv_bit_update_merge :
  forall c' bit' pbn_free bi' c'' bit'' lbn,
    J_bi_block_coherent c' bit'
    -> (exists b' : block,
          chip_get_block c'' pbn_free = Some b' /\
          block_coherent_data_partial PAGES_PER_BLOCK b')
    -> (forall pbn' : block_no,
        pbn' <> pbn_free -> chip_get_block c'' pbn' = chip_get_block c' pbn')
    -> bit_get bit' pbn_free = Some bi'
    -> bit_update bit' pbn_free (mk_bi (bs_data lbn) PAGES_PER_BLOCK (bi_erase_count bi')) = Some bit''
    -> J_bi_block_coherent c'' bit''.
Proof.
  intros c bit pbn bi c' bit' lbn.  
  intros HJ Hm1 Hm2 Hget Hup.  
  unfold J_bi_block_coherent in * .
  intros pbn' bi' Hget'.
  destruct (nat_eq_dec pbn pbn') as [Heq | Hneq].
  subst pbn'.
  rewrite (bit_update_bit_get_eq bit pbn _ bit' Hup) in Hget'.
  inversion Hget'.
  subst bi'.
  unfold chip_bi_coherent.
  simpl.
  destruct Hm1 as [b [Hb Hco]].
  exists b.
  split; trivial.
  unfold block_coherent_data.
  simpl.
  exists lbn.
  split; trivial.
  unfold block_coherent_data_partial in Hco.
  destruct Hco as [Hnb [Hbs Hco]].
  split; auto.
  split; auto.
  split; auto.
  intros loc Hloc.
  destruct (Hco loc Hloc) as [Hco1 Hco2].
  apply Hco1.
  unfold valid_page_off in Hloc.
  exact Hloc.
  
  assert (pbn' <> pbn).
    auto.
  unfold chip_bi_coherent.
  rewrite (bit_update_bit_get_neq bit pbn' bit' _ pbn Hup H) in Hget'.
  assert (chip_bi_coherent c pbn' bi').
    apply HJ; trivial.
  unfold chip_bi_coherent in H0.
  destruct H0 as [b [Hb Hx]].
  exists b.
  split; trivial.
  rewrite Hm2; trivial.
Qed.

(* used in the 2nd case of alloc_block *)
Lemma J_bi_block_coherent_preserv_erased_set_erased: 
  forall c bit pbn bi bit' bi',
    J_bi_block_coherent c bit
    -> bit_get bit pbn = Some bi
    -> bi_state bi = bs_erased
    -> bi' = mk_bi bs_erased 0 (bi_erase_count bi)
    -> bit_update bit pbn bi' = Some bit'
    -> J_bi_block_coherent c bit'.
Proof.
  intros c bit pbn bi bit' bi' HJ Hget Hbis Hbi' Hup.
  unfold J_bi_block_coherent in * .
  rename bi' into bix.
  intros pbn' bi' Hget'.
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    rewrite (bit_update_bit_get_eq _ _ _ _ Hup) in Hget'.
    injection Hget'.
    intro; subst bix.
    subst bi'.
    unfold chip_bi_coherent.
    simpl.
    clear Hget'.
    assert (Hx := HJ pbn bi Hget).
    unfold chip_bi_coherent in Hx.
    destruct Hx as [b [Hb Hx]].
    exists b.
    split; trivial.
    rewrite Hbis in Hx.
    unfold block_coherent_erased in * .
    simpl.
    destruct Hx as [H1 [H2 [H3 [H4 H5]]]].
    rewrite H4.
    rewrite H3.
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
  rewrite (bit_update_bit_get_neq bit pbn' bit' _ pbn Hup (neq_sym Hneq)) in Hget'.
  apply HJ; trivial.
Qed.

Lemma J_bi_block_coherent_preserv_bit_update_chip_erase: 
  forall c bit pbn bi b c' bit' bi',
    J_bi_block_coherent c bit
    -> bit_get bit pbn = Some bi
    -> bi' = mk_bi bs_erased 0 (S (bi_erase_count bi))
    -> bit_update bit pbn bi' = Some bit'
    -> chip_get_block c pbn = Some b
    -> chip_set_block c pbn (erased_block (block_erase_count b)) = Some c'
    -> J_bi_block_coherent c' bit'.
Proof.
  intros c bit pbn bi b c' bit' bix.
  unfold J_bi_block_coherent.
  intros HJ Hget Hbi' Hup Hgetc Hsetc.
  intros pbn' bi' Hget'.
  destruct (chip_set_block_elim c pbn _ c' Hsetc) as [Hbv [Hgetc'1 Hgetc'2]].
  destruct (pbn_eq_dec pbn pbn') as [Heq | Hneq].
    subst pbn'.
    rewrite (bit_update_bit_get_eq _ _ _ _ Hup) in Hget'.
    injection Hget'.
    intro H; subst bi'; clear Hget'.
    unfold chip_bi_coherent.
    exists (erased_block (block_erase_count b)).
    split; trivial.
    subst bix; simpl.
    unfold block_coherent_erased.
    simpl.
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    intros loc Hloc.
    unfold erased_block.
    unfold block_get_page.
    rewrite Hloc.
    unfold block_pages.
    exists init_page.
    split.
    assert (Hx: loc < PAGES_PER_BLOCK).
      unfold valid_page_off in Hloc.
      unfold bvalid_page_off in Hloc.
      desbnat.
      trivial.
    rewrite (@list_get_list_repeat_list _ _ _ _ Hx).
    trivial.
    unfold init_page.
    simpl; trivial.
  rewrite (bit_update_bit_get_neq bit pbn' bit' _ pbn Hup (neq_sym Hneq)) in Hget'.
  unfold chip_bi_coherent.
  destruct (HJ pbn' bi' Hget') as [bx [Hbx Hx]].
  exists bx.
  split; trivial.
  rewrite (Hgetc'2 pbn' Hneq).
  trivial.
Qed.

Lemma blank_pmt_shape:
  forall loc,
    (bvalid_page_off loc = true
    -> pmt_get blank_pmt loc = Some pmte_empty)
    /\ (bvalid_page_off loc = false 
        -> pmt_get blank_pmt loc = None). 
Proof.
  intros.
  split.
    intros.
    unfold bvalid_page_off in H.
    unfold pmt_get.
    unfold blank_pmt.
    desbnat.
    rewrite (@list_get_list_repeat_list _ loc pmte_empty PAGES_PER_BLOCK H).
    trivial.
  intros.
  unfold bvalid_page_off in H.
  unfold pmt_get, blank_pmt.
  desbnat.
  rewrite (@list_get_list_repeat_list_none _ loc pmte_empty PAGES_PER_BLOCK H).
  trivial.
Qed.

Lemma blank_pmt_shape':
  pmt_shape blank_pmt 0.
Proof.
  unfold pmt_shape.
  intros.
  destruct (blank_pmt_shape loc) as [H1 H2].
  split.
    intro Hloc.
    simplbnat.
  intro Hloc.
  rewrite (H1 H).
  trivial.
Qed.

Lemma blank_pmt_is_domain_complete : 
  pmt_domain_is_complete blank_pmt.
Proof.
  unfold pmt_domain_is_complete.
  intros.
  unfold pmt_len.
  simpl.
  trivial.
Qed.


Lemma pmt_update_pmt_find_rev :
  forall pmt loc off pmt',
  pmt_domain_is_complete pmt
  -> pmt_shape pmt loc 
  -> pmt_update pmt loc off = Some pmt'
  -> pmt_find_rev pmt' (pmte_log off) = Some loc.
Proof.
  intros pmt loc off pmt' Hpd Hps Hu.
  unfold pmt_find_rev.
  assert (Hg:= pmt_update_pmt_get_eq _ _ _ _ Hu).
  unfold pmt_shape in Hps.
  assert (Hlen: pmt_len pmt' = PAGES_PER_BLOCK).
    unfold pmt_domain_is_complete in Hpd.
    rewrite (pmt_update_pmt_len _ _ _ _ Hu).
    trivial.
  assert (forall loc' pmte,
            loc' > loc
            -> pmt_get pmt' loc' = Some pmte
            -> pmte_log off <> pmte).
    intros loc' pmte Hneq Hgloc'.
    intros HF.
    subst pmte.
    assert (valid_page_off loc').
      unfold valid_page_off.
      unfold bvalid_page_off.
      destruct (blt_nat loc' PAGES_PER_BLOCK) eqn:Hloc'b; trivial.
      destruct (pmt_len_pmt_get _ _ Hlen loc') as [H1 H2].
      rewrite (H2 Hloc'b) in Hgloc'.
      discriminate.
    destruct (Hps loc' H) as [H1 H2].
    assert (Hx : blt_nat loc' loc = false).    
      clear - Hneq.
      solvebnat.
    apply H2 in Hx.
    assert (Hy : loc' <> loc).
      clear - Hneq.
      omega.
    rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hu Hy) in Hgloc'.
    rewrite Hgloc' in Hx.
    discriminate.
  apply list_get_list_find_rev; trivial.
  apply beq_pmt_entry_eq_true; trivial.
  apply beq_pmt_entry_true_eq; trivial.
Qed.
