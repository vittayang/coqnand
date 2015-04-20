(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import LibEx.
Require Import ListEx.
Require Import Data.
Require Import Monad.

Require Import Params.
Require Import Nand.

(*  -------------------------------------------------------------

  Lemmas 

*)

Lemma page_off_eq_dec : 
  forall (loc loc' : page_off),
    loc = loc' \/ loc <> loc'.
Proof.
  intros.
  destruct (nat_eq_dec loc loc').
  left.
  subst;  trivial.
  right.  
  intro HF; subst; trivial.
  apply n.
  trivial.
Qed.


Lemma pbn_eq_dec : 
  forall (pbn pbn' : block_no),
    pbn = pbn' \/ pbn <> pbn'.
Proof.
  intros.
  destruct (nat_eq_dec pbn pbn').
  left.
  subst;  trivial.
  right.  
  intro HF; subst; trivial.
  apply n.
  trivial.
Qed.

Lemma block_no_eq_dec : 
  forall pbn pbn' : block_no, pbn = pbn' \/ pbn <> pbn'.
Proof.
  intros.
  destruct (nat_eq_dec pbn pbn'); auto.
Qed.


Lemma nand_erase_block_spec: 
  forall c pbn b,
    bvalid_block_no pbn = true
    -> chip_get_block c pbn = Some b
    -> block_state b = bs_programmed
    -> exists c', nand_erase_block c pbn = Some c'
                  /\ chip_set_block c pbn (erased_block (block_erase_count b)) = Some c'
                  /\ chip_get_block c' pbn = Some (erased_block (block_erase_count b))
                  /\ (forall pbn', pbn <> pbn'
                                   -> chip_get_block c pbn' = chip_get_block c' pbn').
Proof.
  intros c pbn b.
  intros Hvb Hc Hbs.
  unfold chip_get_block in Hc.
  unfold nand_erase_block.
  rewrite Hvb.
  unfold chip_get_block.
  rewrite Hc.
  unfold chip_set_block.
  rewrite Hvb.
  destruct (list_get_list_set (l:=(chip_blocks c)) (erased_block (block_erase_count b)) Hc) as [l' Hset].
  rewrite Hset.
  exists (mkchip l').
  split; trivial.
  split; trivial.
  split.
    simpl.
    apply (list_get_list_set_eq Hset); auto.
  intros pbn' Hneq.
  simpl.
  rewrite (list_get_list_set_neq Hset Hneq).
  trivial.
Qed.

Lemma chip_set_block_elim : 
  forall c pbn b c' ,
    chip_set_block c pbn b = Some c'
    -> bvalid_block_no pbn = true
       /\ chip_get_block c' pbn = Some b
       /\ forall pbn',
            pbn <> pbn' 
            -> chip_get_block c' pbn' = chip_get_block c pbn'.
Proof.
  intros c pbn b c' Hsetc.
  split.
    unfold chip_set_block in Hsetc.
    destruct (bvalid_block_no pbn) eqn: Hvb; try discriminate.
    trivial.
  split.
    unfold chip_get_block.
    unfold chip_set_block in Hsetc.
    destruct (bvalid_block_no pbn) eqn: Hvb; try discriminate.
    destruct (list_set (chip_blocks c) pbn b) eqn: Hset; try discriminate.
    injection Hsetc.
    intro; subst c'.
    simpl.
    rewrite (list_get_list_set_eq Hset).
    trivial.
  intros pbn' H.
  unfold chip_get_block.
  unfold chip_set_block in Hsetc.
  destruct (bvalid_block_no pbn) eqn: Hvb; try discriminate.
  destruct (list_set (chip_blocks c) pbn b) eqn: Hset; try discriminate.
  injection Hsetc.
  intro; subst c'.
  simpl.
  rewrite (list_get_list_set_neq Hset H).
  trivial.
Qed.

Lemma nand_read_page_eq_in_same_block : 
  forall c pbn off c',
    chip_get_block c pbn = chip_get_block c' pbn
    -> nand_read_page c pbn off = nand_read_page c' pbn off.
Proof.
  intros c pbn off c' Hc.
  unfold nand_read_page.
  destruct (bvalid_block_no pbn) eqn:Hpbn.
  rewrite <- Hc.
  trivial.
  trivial.
Qed.

Lemma invalid_off_implies_nand_read_page_none : 
  forall c pbn loc,
    bvalid_page_off loc = false
    -> nand_read_page c pbn loc = None.
Proof.
  intros c pbn loc H.
  unfold nand_read_page.
  rewrite H.
  destruct (bvalid_block_no pbn); trivial.
  destruct (chip_get_block c pbn); trivial.
Qed.

Lemma nand_write_page_spec: 
  forall c pbn off d o b p,
    bvalid_block_no pbn = true
    -> bvalid_page_off off = true
    -> chip_get_block c pbn = Some b
    -> block_get_page b off = Some p
    -> ble_nat (next_page b) off = true
    -> page_state p = ps_free
    -> exists c', nand_write_page c pbn off d o = Some c'
               /\ (exists b', chip_get_block c' pbn = Some b'
                              /\ next_page b' = S off
                              /\ block_erase_count b' = block_erase_count b
                              /\ block_state b' = bs_programmed
                              /\ (exists p', block_get_page b' off = Some p'
                                            /\ p' = mkpage d o ps_programmed)
                              /\ forall off',
                                   off' <> off 
                                   -> bvalid_page_off off' = true
                                   -> block_get_page b' off' = block_get_page b off')
               /\ (forall pbn', 
                     pbn' <> pbn
                     -> chip_get_block c pbn' = chip_get_block c' pbn').
Proof.
  intros c pbn off d o b p.
  intros Hvb Hvo Hc Hb Hnp Hps.
  unfold nand_write_page.
  rewrite Hvb.
  rewrite Hc.
  rewrite Hvo.
  rewrite Hnp.
  rewrite Hb.
  destruct (check_page_state_is_free (page_state p)) eqn:Hck.
  assert (exists b', block_set_page b off (mkpage d o ps_programmed) = Some b').
    unfold block_set_page.
    rewrite Hvo.
    unfold block_get_page in Hb.
    rewrite Hvo in Hb.
    destruct (list_get (block_pages b) off) eqn: Hgb; (try discriminate).
    injection Hb.
    intro; subst p0.
    destruct (list_get_list_set (mkpage d o ps_programmed) Hgb) as [b' Hsetb'].
    rewrite Hsetb'.
    eexists; eauto.
  destruct H as [b' Hb'].
  rewrite Hb'.
  unfold block_set_next_page.
  assert (exists c', chip_set_block c pbn 
                                    (mkblock (block_pages b') (S off) 
                                             (block_erase_count b') (block_state b')) = Some c').
    unfold chip_set_block.
    rewrite Hvb.
    unfold chip_get_block in Hc.
    destruct (list_get (chip_blocks c) pbn) eqn: Hgb; (try discriminate).
    injection Hc.
    intro; subst b0.
    destruct (list_get_list_set (mkblock (block_pages b') (S off) 
                                             (block_erase_count b') (block_state b')) Hgb) as [c' Hsetc'].
    rewrite Hsetc'.
    eexists; eauto.
  destruct H as [c' Hc'].
  rewrite Hc'.
  exists c'. 
  split; trivial.
  split.
    exists (mkblock (block_pages b') (S off) 
                    (block_erase_count b') (block_state b')).
    split.
      unfold chip_get_block.
      unfold chip_set_block in Hc'.
      rewrite Hvb in Hc'.
      destruct (list_set (chip_blocks c) pbn (mkblock (block_pages b') (S off) 
                    (block_erase_count b') (block_state b'))) eqn: Hset; try discriminate.
      injection Hc'; intro; subst c'.
      simpl.
      apply list_get_list_set_eq with (chip_blocks c); trivial.
    split.
      simpl.
      trivial.  
    split.
      simpl.
      unfold block_set_page in Hb'.
      rewrite Hvo in Hb'.
      destruct (list_set (block_pages b) off (mkpage d o ps_programmed)) eqn: Hset; try discriminate.
      injection Hb'; intro; subst.
      simpl.
      trivial.
    split.
      simpl.
      unfold block_set_page in Hb'.
      rewrite Hvo in Hb'.
      destruct (list_set (block_pages b) off (mkpage d o ps_programmed)) eqn: Hset; try discriminate.
      injection Hb'; intro; subst.
      simpl.
      trivial.
    split.
      exists (mkpage d o ps_programmed).
      split; trivial.
      unfold block_get_page.
      rewrite Hvo.
      simpl.
      unfold block_set_page in Hb'.
      rewrite Hvo in Hb'.
      destruct (list_set (block_pages b) off (mkpage d o ps_programmed)) eqn: Hset; try discriminate.
      injection Hb'; intro; subst b'.
      simpl in * .
      rewrite (list_get_list_set_eq Hset).
      trivial.
    intros off' Hoff' Hvo'.
    unfold block_get_page.
    unfold block_set_page in Hb'.
    rewrite Hvo in Hb'.
    rewrite Hvo'.
    simpl.
    destruct (list_set (block_pages b) off (mkpage d o ps_programmed)) eqn:Hset; try discriminate.
    rewrite <- (list_get_list_set_neq Hset (neq_sym Hoff')).
    injection Hb'; intro; subst b'.
    simpl in * .
    trivial.
  intros pbn' Hneq.
  unfold chip_get_block.
  unfold chip_set_block in Hc'.
  rewrite Hvb in Hc'.
  destruct (list_set (chip_blocks c) pbn (mkblock (block_pages b') (S off) 
                    (block_erase_count b') (block_state b'))) eqn:Hset; try discriminate.
  injection Hc'; intro; subst c'.
  simpl.
  rewrite (list_get_list_set_neq Hset (neq_sym Hneq)).
  trivial.
  
  unfold check_page_state_is_free in Hck.
  rewrite Hps in Hck.
  discriminate.
Qed.
