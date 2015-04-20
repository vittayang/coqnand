(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)


(* ************* ************************************* *****)
(* ftl interface *)

Require Import LibEx.
Require Import ListEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import NandLems.

Require Import Bast0.
Require Import FTLProp.

Lemma check_used_implies_check_data_log : 
  forall bi,
    check_used_block bi = true 
    -> check_data_block bi = true \/ check_log_block bi = true.
Proof.
  intros bi.
  destruct bi.
  simpl; intros.
  unfold check_used_block in H.
  simpl in H.
  unfold check_data_block, check_log_block.
  simpl.
  destruct (bi_state); try discriminate.
  left; trivial.
  right; trivial.
Qed.
Arguments check_used_implies_check_data_log [bi] _.

(*  -------------------------------------------------------------

  Lemmas for block info table 

*)

Lemma bit_update_same :
  forall bit pbn bi,
    bit_get bit pbn = Some bi
    -> bit_update bit pbn bi = Some bit.
Proof.
  unfold bit_get, bit_update.
  intros.
  rewrite (list_set_same H).
  trivial.
Qed.

Lemma bit_update_bit_get_neq : 
  forall bit pbn bit' bi' pbn',
    bit_update bit pbn' bi' = Some bit'
    -> pbn <> pbn'
    -> bit_get bit' pbn = bit_get bit pbn.
Proof.
  unfold bit_update, bit_get.
  intros.
  rewrite (list_get_list_set_neq H (neq_sym H0)).
  trivial.
Qed.

Lemma bit_update_bit_get_eq : 
  forall bit pbn bi bit',
    bit_update bit pbn bi = Some bit'
    -> bit_get bit' pbn = Some bi.
Proof.
  unfold bit_update, bit_get.
  intros.
  rewrite (list_get_list_set_eq H).
  trivial.
Qed.

Lemma bit_update_some :
  forall bit pbn bi bi',
    bit_get bit pbn = Some bi
    -> exists bit', bit_update bit pbn bi' = Some bit'.
Proof.
  unfold bit_get, bit_update.
  intros.
  destruct (list_get_list_set bi' H) as [bit' Hbit'].
  exists bit'.
  trivial.
Qed.

(* Lemma bit_get_update_neq :  *)
(*   forall bit pbn bi bit' bi' pbn', *)
(*     bit_get bit pbn = Some bi *)
(*     -> pbn <> pbn' *)
(*     -> bit_update bit pbn' bi' = Some bit' *)
(*     -> bit_get bit' pbn = Some bi. *)
(* Proof. *)
(* Qed. *)

Lemma bit_update_spec : 
  forall bit pbn bi bi',
    bit_get bit pbn = Some bi
    -> exists bit',bit_update bit pbn bi' = Some bit'
                  /\ bit_get bit' pbn = Some bi'
                  /\ (forall pbn', pbn <> pbn'
                                   -> bit_get bit' pbn' = bit_get bit pbn').
Proof.
  unfold bit_update, bit_get.
  intros.
  destruct (list_get_list_set bi' H) as [bit' Hbit'].
  exists bit'.
  split; trivial.
  rewrite (list_get_list_set_eq Hbit').
  split; trivial.
  intros.
  rewrite (list_get_list_set_neq Hbit' H0).
  trivial.
Qed.

Lemma bit_update_spec_rev : 
  forall bit pbn bi bit',
    bit_update bit pbn bi = Some bit'
    -> exists bi', bit_get bit pbn = Some bi'.
Proof.
  unfold bit_update, bit_get.
  intros bit pbn bi bit' Hset.
  destruct (list_set_list_get_rev Hset) as [bi' Hget].
  exists bi'.
  trivial.
Qed.

(*  -------------------------------------------------------------

  Lemmas for free_block_queue 

*)

(* Old name: Lemma pbn_not_in_fbq_presev_fbq_enq :  *)
Lemma fbq_not_in_presev_fbq_enq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = false
    -> fbq_enq fbq pbn' = Some fbq'
    -> pbn <> pbn' 
    -> fbq_in fbq' pbn = false.
Proof.
  induction fbq.
    unfold fbq_in, fbq_enq.
    intros pbn fbq' pbn' Hin Henq Hneq.
    injection Henq.
    intro H.
    subst fbq'.
    simpl.
    simplbnat.
    trivial.

  unfold fbq_in.
  simpl.
  intros pbn fbq' pbn' Hin Henq Hneq.
  destruct fbq'.
    unfold fbq_enq in Henq.
    simpl in Henq.
    discriminate.
  inversion Henq.
  subst b.
  simpl.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq; eauto.
  unfold fbq_enq.
  trivial.
Qed.

(* Old name: Lemma fbq_in_fbq_enq_fbq_in :  *)
Lemma fbq_in_preserv_fbq_enq : 
  forall pbn fbq pbn' fbq',
    pbn <> pbn'
    -> fbq_enq fbq pbn' = Some fbq' 
    -> fbq_in fbq' pbn = fbq_in fbq pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_enq, fbq_in in * .
    simpl in H0.
    inversion H0.
    subst fbq'.
    simpl.
    simplbnat.
    trivial.
  destruct fbq'.
    intros.
    unfold fbq_enq in H0.
    discriminate.
  intros.
  unfold fbq_enq in * .
  simpl in * .
  inversion H0.
  subst b fbq'.
  simpl.
  unfold fbq_in in * .
  simpl.
  clear H0.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq; eauto.
Qed.

Lemma fbq_enq_fbq_in : 
  forall pbn fbq fbq',
    fbq_enq fbq pbn = Some fbq' 
    -> fbq_in fbq' pbn = true.
Proof.
  unfold fbq_enq, fbq_in.
  induction fbq.
    intros.
    injection H.
    intro; subst fbq'.
    simpl.
    simplbnat.
    trivial.
  intros.
  injection H.
  intro; subst fbq'.
  simpl.
  destruct (beq_nat pbn a) eqn:Hb.
    trivial.
  eapply IHfbq.
  trivial.
Qed.

Lemma fbq_enq_fbq_length_addone : 
  forall fbq pbn fbq',
    fbq_enq fbq pbn = Some fbq'
    -> length fbq' = 1 + length fbq.
Proof.
  induction fbq.
    intros.
    unfold fbq_enq in H.
    injection H.
    intro; subst fbq'.
    simpl.
    trivial.
  intros.
  unfold fbq_enq in H.
  injection H.
  intro; subst fbq'.
  simpl.
  rewrite (IHfbq pbn (list_append fbq pbn)); eauto.
Qed.

Lemma fbq_deq_fbq_length_subone : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq')
    -> length fbq = S (length fbq').
Proof.
  unfold fbq_deq.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H; intros; subst a fbq'.
  trivial.
Qed.

Lemma fbq_not_in_preserv_fbq_deq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = false 
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_in fbq' pbn = false.
Proof.
  induction fbq; unfold fbq_in, fbq_deq; simpl; intros; auto.
    discriminate.
  injection H0; intros; subst a fbq'.
  destruct (beq_nat pbn pbn') eqn:Hpbn; trivial.
  discriminate.
Qed.

Lemma fbq_not_in_preserv_fbq_enq : 
  forall fbq pbn fbq' pbn',
    pbn <> pbn' 
    -> fbq_in fbq pbn = false
    -> fbq_enq fbq pbn' = Some fbq'
    -> fbq_in fbq' pbn = false.
Proof.
  unfold fbq_in, fbq_enq.
  induction fbq; simpl; intros; auto.
    injection H1; intros; subst fbq'.
    simpl.
    simplbnat.
    trivial.
  injection H1; intros; subst fbq'.
  simpl.
  destruct (beq_nat pbn a) eqn: Ha.
    discriminate.
  eauto.
Qed.

Lemma fbq_in_fbq_get: 
  forall fbq pbn,
    fbq_in fbq pbn = true 
    -> exists i, fbq_get fbq i = Some pbn.
Proof.
  induction fbq.
    unfold fbq_in, fbq_get. 
    simpl.
    intros; discriminate.
  unfold fbq_in, fbq_get.
  simpl.
  intros.
  destruct (beq_nat pbn a) eqn:Ha.
    exists 0.
    rewbnat Ha.
    trivial.
  assert (pbn <> a).
    intro HF.
    subst a.
    simplbnat.
  destruct (IHfbq pbn H) as [i IH].
  exists (S i).
  trivial.
Qed.

Lemma fbq_get_fbq_deq_fbq_get: 
  forall fbq i pbn pbn' fbq',
    fbq_get fbq (S i) = Some pbn
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_get fbq' i = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get, fbq_deq in * .
    discriminate.
  intros.
  unfold fbq_get in H.
  unfold fbq_deq in H0.
  injection H0.
  intros; subst fbq' a.
  simpl in H.
  trivial.
Qed.

Lemma fbq_get_fbq_rdeq_fbq_get: 
  forall fbq i pbn pbn' fbq',
    fbq_get fbq i = Some pbn
    -> fbq_deq fbq' = Some (pbn', fbq)
    -> fbq_get fbq' (S i) = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get in H .
    unfold list_get in H.
    destruct i; discriminate.
  intros.
  unfold fbq_get in H.
  destruct fbq'.
    simpl in H0.
    discriminate.
  simpl in H0.
  injection H0.
  intros; subst fbq' b.
  unfold fbq_get.
  simpl.
  apply H.
Qed.

Lemma fbq_deq_fbq_get : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq')
    -> fbq_get fbq 0 = Some pbn.
Proof.
  induction fbq.
    intros.
    simpl in * .
    discriminate.
  intros pbn fbq' H.
  unfold fbq_deq in H.
  injection H.
  intros; subst fbq' a.
  unfold fbq_get.
  simpl.
  trivial.
Qed.

Lemma fbq_deq_fbq_in : 
  forall fbq pbn fbq',
    fbq_deq fbq = Some (pbn, fbq') 
    -> fbq_in fbq pbn = true.
Proof.
  unfold fbq_deq, fbq_in.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H; intros; subst a fbq'.
  simplbnat.
  trivial.
Qed.
  
Lemma fbq_in_preserv_fbq_deq : 
  forall fbq pbn fbq' pbn',
    fbq_in fbq pbn = true
    -> pbn' <> pbn
    -> fbq_deq fbq = Some (pbn', fbq')
    -> fbq_in fbq' pbn = true.
Proof.
  unfold fbq_in, fbq_deq.
  induction fbq; simpl; intros; auto.
    discriminate.
  injection H1; intros; subst a fbq'.
  simplbnat.
  trivial.
Qed.

Lemma fbq_enq_spec : 
  forall fbq pbn,
    exists fbq', fbq_enq fbq pbn = Some fbq'.
Proof.
  intros.
  unfold fbq_enq.
  exists (list_append fbq pbn).
  trivial.
Qed.

Lemma fbq_get_fbq_enq_fbq_get_rev: 
  forall fbq fbq' i pbn pbn',
    fbq_enq fbq pbn' = Some fbq'
    -> fbq_get fbq' i = Some pbn
    -> pbn = pbn' /\ i = length fbq \/ fbq_get fbq i = Some pbn .
Proof.
  induction fbq; simpl; intros; trivial.
    unfold fbq_enq in H.
    injection H; intro; subst fbq'; clear H.
    unfold fbq_get in H0.
    simpl in H0.
    destruct i.
      injection H0; intro; subst pbn'; trivial.
      left; split; trivial.
    destruct i; discriminate.
  destruct i.
    unfold fbq_enq in H.
    injection H; intro; subst fbq'; auto.
  destruct fbq'.
    unfold fbq_enq in H.
    discriminate H.
  assert (fbq_enq fbq pbn' = Some fbq').
    clear - H.
    unfold fbq_enq in * .
    simpl in H.
    injection H; intros; subst.
    trivial.
  assert (fbq_get fbq' i = Some pbn).
    clear - H0.
    unfold fbq_get in * .
    simpl in H0.
    trivial.
  destruct (IHfbq fbq' i pbn pbn' H1 H2).
    destruct H3.
    left; subst; split; trivial.
  right.
  clear - H3.
  unfold fbq_get in * .
  simpl.
  trivial.
Qed.

Lemma fbq_not_in_fbq_get_some_implies_false: 
  forall fbq pbn,
    fbq_in fbq pbn = false
    -> forall i, fbq_get fbq i = Some pbn 
                 -> False.
Proof.
  unfold fbq_get.
  induction fbq; simpl; intros; auto.
    destruct i; discriminate.
  assert (fbq_in fbq pbn = false).
    unfold fbq_in in * .
    simpl in * .
    destruct (beq_nat pbn a).
      discriminate.
    trivial.
  destruct i.
    injection H0; intro; subst a; auto.
    unfold fbq_in in H.
    simpl in H.
    simplbnat.
  apply IHfbq with pbn i ; auto.
Qed.

Lemma fbq_get_fbq_deq_fbq_get_rev: 
  forall fbq i pbn pbn' fbq',
    fbq_deq fbq = Some (pbn', fbq')
    -> fbq_get fbq' i = Some pbn
    -> fbq_get fbq (S i) = Some pbn.
Proof.
  induction fbq.
    intros.
    unfold fbq_get, fbq_deq in * .
    discriminate.
  intros.
  destruct i.
    simpl in *.
    unfold fbq_get.
    simpl.
    injection H; intros; subst fbq'; trivial. 
  unfold fbq_deq in H.
  injection H; intros; subst a fbq'; auto.
Qed.

(*  -------------------------------------------------------------

  Lemmas for block mapping table

*)

Lemma pbn_in_bmt_lbn_bmt_get : 
  forall bmt lbn pbn,
    pbn_in_bmt_lbn bmt lbn pbn
    -> exists bmr, bmt_get bmt lbn = Some bmr
       /\ pbn_in_bmr pbn bmr.
Proof.
  intros bmt lbn pbn Hin.
  unfold pbn_in_bmt_lbn in Hin.
  destruct Hin.
    destruct H as [bmr Hget].
    exists (Some pbn, bmr).
    split; trivial.
    simpl.
    destruct bmr.
      left; trivial.
    trivial.
  destruct H as [bmr Hget].
  exists (bmr, Some pbn).
  split; trivial.
  unfold pbn_in_bmr.
  destruct bmr; trivial.
  right; trivial.
Qed.    

Lemma bmt_get_bmt_update_some : 
  forall bmt lbn mbr mbr',
    bmt_get bmt lbn = Some mbr 
    -> exists bmt', bmt_update bmt lbn mbr' = Some bmt'.
Proof.
  unfold bmt_get, bmt_update.
  intros.
  destruct (list_get_list_set mbr' H) as [bmt' Hbmt'].
  exists bmt'.
  destruct mbr'; trivial.
Qed.

Lemma bmt_update_bmt_get_eq : 
  forall bmt lbn bmr bmt',
    bmt_update bmt lbn bmr = Some bmt'
    -> bmt_get bmt' lbn = Some bmr. 
Proof.
  unfold bmt_update, bmt_get.
  intros.
  destruct bmr.
  rewrite (list_get_list_set_eq H).
  trivial.
Qed.

Lemma bmt_update_bmt_get_neq : 
  forall bmt lbn bmr bmt' lbn',
    bmt_update bmt lbn bmr = Some bmt'
    -> lbn <> lbn'
    -> bmt_get bmt' lbn' = bmt_get bmt lbn'. 
Proof.
  unfold bmt_update, bmt_get.
  intros.
  destruct bmr.
  rewrite (list_get_list_set_neq H H0).
  trivial.
Qed.


Lemma bmt_update_bmt_get_eq_rev : 
  forall bmt lbn bmr bmt',
    bmt_update bmt lbn bmr = Some bmt'
    -> exists bmr', bmt_get bmt lbn = Some bmr'.
Proof.
  unfold bmt_get, bmt_update.
  intros.
  destruct bmr as [bmrd bmrl].
  destruct (list_set_list_get_rev H) as [bmr' H'].
  exists bmr'; trivial.
Qed.

Lemma bmt_update_spec : 
  forall bmt lbn mbr mbr',
    bmt_get bmt lbn = Some mbr 
    -> exists bmt', bmt_update bmt lbn mbr' = Some bmt'
                    /\ bmt_get bmt' lbn = Some mbr'
                    /\ forall lbn', lbn' <> lbn 
                                    -> bmt_get bmt' lbn' = bmt_get bmt lbn'.
Proof.
  unfold bmt_get, bmt_update.
  intros.
  destruct (list_get_list_set mbr' H) as [bmt' Hbmt'].
  exists bmt'.
  destruct mbr'.
  split; trivial.
  rewrite (list_get_list_set_eq Hbmt').
  split; trivial.
  intros.
  rewrite (list_get_list_set_neq Hbmt' (neq_sym H0)).
  trivial.
Qed.

Lemma bmt_update_pbn_in_bmt_lbn_neq : 
  forall bmt lbn bmr bmt' lbn' pbn,
    bmt_update bmt lbn bmr = Some bmt'
    -> lbn' <> lbn
    -> pbn_in_bmt_lbn bmt lbn' pbn
    -> pbn_in_bmt_lbn bmt' lbn' pbn.
Proof.
  unfold pbn_in_bmt_lbn.
  intros bmt lbn bmr bmt' lbn' pbn Hu Hneq H.
  destruct H.
    left.
    unfold pbn_in_bmt_data in * .
    destruct H as [x H].
    rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hu (neq_sym Hneq)).
    exists x; trivial.
  right.
  unfold pbn_in_bmt_log in * .
  destruct H as [x H].
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hu (neq_sym Hneq)).
  exists x; trivial.
Qed.

Lemma bmt_update_pbn_in_bmt_lbn_eq : 
  forall bmt lbn pbn bmr bmt',
    bmt_update bmt lbn bmr = Some bmt'
    -> pbn_in_bmr pbn bmr
    -> pbn_in_bmt_lbn bmt' lbn pbn. 
Proof.
  unfold pbn_in_bmr, pbn_in_bmt_lbn.
  intros.
  destruct bmr as [bd bl].
  destruct bd; destruct bl.
    destruct H0.
    left.
    exists (Some b0).
    rewrite (bmt_update_bmt_get_eq _ _ _ _ H).
    subst; trivial.
    right.
    exists (Some b).
    subst b0.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ H).
    trivial.

    left.
    exists None.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ H).
    subst; trivial.
    
    right.
    exists None.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ H).
    subst; trivial.

    contradiction.
Qed.

Lemma bmt_update_pbn_in_bmt_lbn_neq_rev : 
(* Lemma bmt_update_pbn_in_bmt_neq :  *)
  forall bmt bmt' lbn lbn' pbn bmr,
    bmt_update bmt lbn bmr = Some bmt'
    -> lbn <> lbn'
    -> pbn_in_bmt_lbn bmt' lbn' pbn
    -> pbn_in_bmt_lbn bmt lbn' pbn. 
Proof.
  unfold pbn_in_bmt_lbn.
  intros.
  destruct H1.
    left.
    unfold pbn_in_bmt_data in * .
    destruct H1.
    exists x.
    rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ H H0).
    trivial.
  right.
  destruct H1.
  exists x. 
  rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ H H0).
  trivial.
Qed.

Lemma bmt_update_log_bmt_get_neq : 
  forall bmt lbn pbn bmt' lbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> lbn <> lbn'
    -> bmt_get bmt' lbn' = bmt_get bmt lbn'. 
Proof.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b.
  destruct (bmt_update bmt lbn (o, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b.
  erewrite bmt_update_bmt_get_neq; eauto.
Qed.

Lemma bmt_update_log_spec :
  forall bmt lbn pbn bmr,
    bmt_get bmt lbn = Some bmr
    -> exists bmt', bmt_update_log bmt lbn pbn = Some bmt'
                    /\ bmt_get bmt' lbn = Some (fst bmr, Some pbn)
                    /\ (forall lbn', 
                         lbn' <> lbn
                         -> bmt_get bmt' lbn' = bmt_get bmt lbn').
Proof.
  unfold bmt_update_log.
  intros.
  rewrite H.
  destruct bmr.
  destruct (bmt_update_spec bmt lbn _ (o, Some pbn) H) as [bmt' [Hup [Hget Hget']]].
  exists bmt'.
  rewrite Hup.
  split; trivial.
  simpl.
  split; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_log_eq : 
  forall bmt lbn pbn bmt',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> pbn_in_bmt_log bmt' lbn pbn.
Proof.
  unfold pbn_in_bmt_log.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b.
  rewrite (bmt_update_bmt_get_eq _ _ _ _ Hup).
  exists bmrd; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_data_preserv : 
  forall bmt lbn pbn bmt' lbn' pbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> pbn_in_bmt_data bmt lbn' pbn'
    -> pbn_in_bmt_data bmt' lbn' pbn'.
Proof.
  unfold pbn_in_bmt_data.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b.
  destruct (pbn_eq_dec lbn lbn') as [Heq | Hneq].
    subst lbn'.
    destruct H0 as [x H0].
    exists (Some pbn).
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hup).
    rewrite Hget in H0.
    injection H0; intros; subst bmrd x.
    trivial.
  destruct H0 as [x H0].
  clear H.
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hup Hneq).
  rewrite H0.
  exists x; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_data_preserv_rev : 
  forall bmt lbn pbn bmt' lbn' pbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> pbn_in_bmt_data bmt' lbn' pbn'
    -> pbn_in_bmt_data bmt lbn' pbn'.
Proof.
  unfold pbn_in_bmt_data.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b.
  destruct (pbn_eq_dec lbn lbn') as [Heq | Hneq].
    subst lbn'.
    destruct H0 as [x H0].
    exists bmrl.
    rewrite (bmt_update_bmt_get_eq _ _ _ _ Hup) in H0.
    injection H0; intros; subst bmrd x.
    trivial.
  destruct H0 as [x H0].
  clear H.
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hup Hneq) in H0.
  exists x; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_log_preserv_rev : 
  forall bmt lbn pbn bmt' lbn' pbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> lbn <> lbn'
    -> pbn_in_bmt_log bmt' lbn' pbn'
    -> pbn_in_bmt_log bmt lbn' pbn'.
Proof.
  unfold pbn_in_bmt_log.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b; clear H.
  destruct H1 as [x H1].
  rewrite (bmt_update_bmt_get_neq _ _ _ _ _ Hup H0) in H1.
  exists x; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_lbn_neq : 
  forall bmt lbn pbn bmt' lbn' pbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> lbn <> lbn'
    -> pbn_in_bmt_lbn bmt lbn' pbn'
    -> pbn_in_bmt_lbn bmt' lbn' pbn'.
Proof.
  unfold pbn_in_bmt_lbn.
  unfold bmt_update_log.
  unfold pbn_in_bmt_data, pbn_in_bmt_log.
  intros.
  destruct (bmt_get bmt lbn) eqn:Hget; try discriminate.
  destruct b as [bmrd bmrl].
  destruct (bmt_update bmt lbn (bmrd, Some pbn)) eqn:Hup; try discriminate.
  injection H; intros; subst b; clear H.
  destruct H1 as [[x H1] | [x H1]].
    left.
    rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hup H0) in H1.
    exists x; trivial.
  right.
  rewrite <- (bmt_update_bmt_get_neq _ _ _ _ _ Hup H0) in H1.
  exists x; trivial.
Qed.

Lemma bmt_update_log_pbn_in_bmt_lbn_neq_rev : 
  forall bmt lbn pbn bmt' lbn' pbn',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> lbn <> lbn'
    -> pbn_in_bmt_lbn bmt' lbn' pbn'
    -> pbn_in_bmt_lbn bmt lbn' pbn'.
Proof.
  unfold pbn_in_bmt_lbn.
  intros.
  destruct H1 as [H1 | H1].
  left.
  apply (bmt_update_log_pbn_in_bmt_data_preserv_rev _ _ _ _ _ _ H); trivial.
  right.
  apply (bmt_update_log_pbn_in_bmt_log_preserv_rev _ _ _ _ _ _ H); trivial.
Qed.

Lemma bmt_update_log_bmt_get_eq_rev : 
  forall bmt lbn pbn bmt',
    bmt_update_log bmt lbn pbn = Some bmt'
    -> exists bmr, bmt_get bmt lbn = Some bmr.
Proof.
  unfold bmt_update_log.
  intros.
  destruct (bmt_get bmt lbn) as [ bmr | ] eqn:Hget.
    destruct bmr as [bmrd bmrl].
    destruct (bmt_update bmt lbn(bmrd, Some pbn)) as [ bmt'' | ] eqn:Hu.
      injection H; intro; subst bmt''; clear H.
      exists (bmrd, bmrl); trivial.
    discriminate.
  discriminate.
Qed.

Lemma bmt_get_pbn_in_bmt_r : 
  forall bmt lbn x pbn2,
    bmt_get bmt lbn = Some (x, Some pbn2)
    -> pbn_in_bmt bmt pbn2.
Proof.
  intros bmt lbn x pbn2 Hget.
  exists lbn; right.
  exists x; trivial.
Qed.

Lemma bmt_get_pbn_in_bmt_l : 
  forall bmt lbn pbn1 x,
    bmt_get bmt lbn = Some (Some pbn1, x)
    -> pbn_in_bmt bmt pbn1.
Proof.
  intros bmt lbn pbn1 x Hget.
  exists lbn; left.
  exists x; trivial.
Qed.

(************** *)

Lemma pmt_update_pmt_len :
  forall pmt loc off pmt',
    pmt_update pmt loc off = Some pmt'
    -> pmt_len pmt' = pmt_len pmt.
Proof.
  unfold pmt_update, pmt_len.
  intros.
  erewrite list_set_length_preserv; eauto.
Qed.

Lemma pmt_update_pmt_get_eq : 
  forall pmt loc off pmt',
    pmt_update pmt loc off = Some pmt'
    -> pmt_get pmt' loc = Some (pmte_log off).
Proof.
  unfold pmt_update, pmt_get.
  intros.
  rewrite (list_get_list_set_eq H).
  trivial.
Qed.

Lemma pmt_update_pmt_get_neq : 
  forall pmt loc off pmt' loc',
    pmt_update pmt loc off = Some pmt'
    -> loc' <> loc
    -> pmt_get pmt' loc' = pmt_get pmt loc'.
Proof.
  unfold pmt_update, pmt_get.
  intros.
  rewrite (list_get_list_set_neq H (neq_sym H0)).
  trivial.
Qed.

Lemma beq_pmt_entry_true_eq : 
  forall a1 a2 : pmt_entry, beq_pmt_entry a1 a2 = true -> a1 = a2.
Proof.
  intros a1 a2 H.
  destruct a1; destruct a2; simpl in H; simpl; try discriminate; trivial.
  rewbnat H.
  trivial.
Qed.

Lemma beq_pmt_entry_eq_true : 
  forall a1 a2 : pmt_entry, a1 = a2 -> beq_pmt_entry a1 a2 = true.
Proof.
  intros a1 a2 H.
  destruct a1; destruct a2; simpl in H; simpl; try discriminate; trivial.
  injection H; intro; subst; trivial.
  simplbnat.
  trivial.
Qed.

Lemma beq_pmt_entry_false_neq : 
  forall a1 a2 : pmt_entry, beq_pmt_entry a1 a2 = false -> a1 <> a2.
Proof.
  intros a1 a2 H.
  destruct a1; destruct a2; simpl in H; simpl; try discriminate; trivial.
  intro HF.
  injection HF; intro; subst off0.
  simplbnat.
Qed.

Lemma beq_pmt_entry_neq_false : 
  forall a1 a2 : pmt_entry, a1 <> a2 -> beq_pmt_entry a1 a2 = false.
Proof.
  intros a1 a2 H.
  destruct a1; destruct a2; simpl in H; simpl; try discriminate; trivial.
    destruct (H (refl_equal _)).
  destruct (beq_nat off off0) eqn: Hbeq.    
    apply False_ind.
    apply H.
    rewbnat Hbeq.
    trivial.
  trivial.
Qed.

Lemma pmt_find_rev_pmt_get :
  forall pmt off loc,
    pmt_find_rev pmt (pmte_log off) = Some loc
    -> pmt_get pmt loc = Some (pmte_log off).
Proof.
  unfold pmt_find_rev, pmt_get.
  intros pmt off loc Hfind.
  rewrite (list_find_rev_list_get Hfind); trivial.
  apply beq_pmt_entry_true_eq; trivial.
Qed.

Lemma pmt_len_pmt_get:
  forall pmt len,
    pmt_len pmt = len
    -> forall loc, 
         (blt_nat loc len = true -> exists pmte, pmt_get pmt loc = Some pmte)
         /\ (blt_nat loc len = false -> pmt_get pmt loc = None).
Proof.
  intros.
  unfold pmt_len, pmt_get in * .
  destruct (length_elim H loc) as [H1 H2].
  split; trivial.
Qed.

Lemma pmt_update_pmt_find_rev_neq :
  forall pmt loc off pmt' off', 
    pmt_get pmt loc = Some pmte_empty
    -> pmt_update pmt loc off = Some pmt'
    -> off' <> off
    -> pmt_find_rev pmt' (pmte_log off') = pmt_find_rev pmt (pmte_log off').
Proof.
  unfold pmt_get, pmt_update, pmt_find_rev.
  intros.
  apply list_set_list_find_rev_neq with loc pmte_empty (pmte_log off); trivial.
  intro HF.
  apply H1.
  injection HF; auto.
  intro HF; discriminate.
  apply beq_pmt_entry_neq_false; trivial.
  apply beq_pmt_entry_false_neq; trivial.
Qed.

Lemma pmt_update_spec: 
  forall pmt loc off,
    bvalid_page_off loc = true
    -> pmt_get pmt loc = Some pmte_empty
    -> exists pmt', pmt_update pmt loc off = Some pmt'
                    /\ pmt_get pmt' loc = Some (pmte_log off)
                    /\ (forall loc', 
                          loc' <> loc
                          -> pmt_get pmt' loc' = pmt_get pmt loc').
Proof.
  intros pmt loc off Hloc Hget.
  assert (exists pmt', pmt_update pmt loc off = Some pmt').
    unfold pmt_update, pmt_get in * .
    destruct (@list_get_list_set _ pmt loc pmte_empty (pmte_log off) Hget) as [pmt' Hx].
    exists pmt'; trivial.
  destruct H as [pmt' H].
  rewrite H.
  exists pmt'.
  split; trivial.
  split.
    rewrite (pmt_update_pmt_get_eq _ _ _ _ H).
    trivial.
  intros loc' Hneq.
  rewrite (pmt_update_pmt_get_neq _ _ _ _ _ H Hneq).
  trivial.
Qed.


(************** *)

Lemma pbn_in_bmt_data_inj :
  forall bmt lbn pbn pbn',
    pbn_in_bmt_data bmt lbn pbn
    -> pbn_in_bmt_data bmt lbn pbn'
    -> pbn = pbn'.
Proof.
  unfold pbn_in_bmt_data.
  intros bmt lbn pbn pbn' Hpbn Hpbn'.
  destruct Hpbn as [x1 Hpbn].
  destruct Hpbn' as [x2 Hpbn'].
  rewrite Hpbn in Hpbn'.
  injection Hpbn'; intros; auto.
Qed.

Lemma pbn_in_bmt_log_inj :
  forall bmt lbn pbn pbn',
    pbn_in_bmt_log bmt lbn pbn
    -> pbn_in_bmt_log bmt lbn pbn'
    -> pbn = pbn'.
Proof.
  unfold pbn_in_bmt_log.
  intros bmt lbn pbn pbn' [x1 Hpbn] [x2 Hpbn'].
  rewrite Hpbn in Hpbn'.
  injection Hpbn'; intros; auto.
Qed.

(************** *)

Lemma invalid_off_implies_read_data_block_none : 
  forall c pbn loc,
    ~ valid_page_off loc
    -> read_data_block c pbn loc = None.
Proof.
  intros c pbn loc H.
  unfold read_data_block.
  assert (bvalid_page_off loc = false).
    unfold valid_page_off in H.
    destruct (bvalid_page_off loc).
    destruct (H (refl_equal _)).
    trivial.
  rewrite (invalid_off_implies_nand_read_page_none _ _ _ H0); eauto.
Qed.

Lemma read_data_block_unchanged :
  forall c pbn off c',
    chip_get_block c pbn = chip_get_block c' pbn
    -> read_data_block c pbn off = read_data_block c' pbn off.
Proof.
  intros c pbn off c' Hg.
  unfold read_data_block.
  erewrite nand_read_page_eq_in_same_block; eauto.
Qed.


Lemma read_log_block_unchanged :
  forall c pbn off bi c',
    chip_get_block c pbn = chip_get_block c' pbn
    -> read_log_block c bi pbn off = read_log_block c' bi pbn off.
Proof.
  intros c pbn off bi c' Hg.
  unfold read_log_block.
  destruct (find_page_in_log_block bi off) as [loc | ].
  erewrite nand_read_page_eq_in_same_block; eauto.
  trivial.
Qed.

Lemma abundant_elim : 
  forall fbq, 
    check_freebq_count fbq = fbqs_abundant 
    -> exists b fbq', fbq_deq fbq = Some (b, fbq')
                      /\ fbq_in fbq b = true.
Proof.
  unfold check_freebq_count.
  intros fbq H.
  destruct (ble_nat MIN_FREE_BLOCKS (length fbq)) eqn:Hfbq; try discriminate.
  clear H.
  destruct fbq as [ | b fbq' ].
    simpl in Hfbq.
    unfold ble_nat in Hfbq.
    unfold MIN_FREE_BLOCKS in Hfbq.
    simpl in Hfbq.
    discriminate.
  exists b, fbq'.
  simpl.
  split; trivial.
  unfold fbq_in.
  unfold list_inb.
  simplbnat.
  trivial.
Qed.
