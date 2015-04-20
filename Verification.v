(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)


Require Import LibEx.
Require Import bnat.
Require Import List.
Require Import ListEx.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import Bast0.
Require Import FTLProp.

Require Import Framework.

Require Import Inv.
Require Import FTLLems4.

(* To prove the theorem above, we need define a relation, R, saying the flash_device 
   is equal to a hard_disk at every address.
*)

Definition Inv (fld: flash_device) : Prop := 
  let (c, f) := fld in Inv.Inv c f.

Lemma R_init : R hdd_init fld_init.
Proof.
  unfold R, hdd_init, fld_init.
  intros sec.
  unfold hdd_read, fld_read.
  destruct (bvalid_sector_no sec) eqn:Hvsec.
  rewrite list_get_list_repeat_list.
  destruct (lpn_to_lbn_off sec) as [lbn off] eqn:Hlpn.
  assert (Hvoff : bvalid_page_off off = true).
    apply valid_lpn_implies_valid_off with sec lbn; trivial.
  assert (Hvlbn : bvalid_logical_block_no lbn = true).
    apply valid_lpn_implies_valid_lbn with sec off; trivial.
  rewrite ftl_read_ftl_init; trivial.
    apply blt_true_lt; trivial.
  destruct (lpn_to_lbn_off sec) as [lbn off] eqn:Hlpn.
  assert (Hvoff : bvalid_page_off off = true).
    apply invalid_lpn_implies_valid_off with sec lbn; trivial.
  assert (Hvlbn : bvalid_logical_block_no lbn = false).
    apply invalid_lpn_implies_invalid_lbn with sec off; trivial.
  unfold FTL_read.
  rewrite Hvoff.
  unfold ftl_init.
  unfold bmt_get, bmt_init.
  unfold ftl_bm_table.
  rewrite list_get_list_repeat_list_none; trivial.
  apply blt_false_le; trivial.
Qed.

Lemma fld_write_R_preservation : 
  forall hdd hdd' fld fld' sec d,
    Inv fld
    -> R hdd fld
    -> hdd_write hdd sec d = Some hdd'
    -> fld_write fld sec d = Some fld'
    -> R hdd' fld'.
Proof.
  unfold R; intros.
  destruct (beq_nat_dec sec sec0).
    desbnat.
    subst sec0.
    destruct fld as [c f]. 
    destruct fld' as [c' f'].
    unfold fld_write in H2.
    destruct (lpn_to_lbn_off sec) as [lbn lpo] eqn:Hsec.
    unfold fld_read.
    rewrite hdd_read_write_at_same_addr with hdd sec d hdd'; trivial.
    rewrite Hsec.
    rewrite ftl_read_write_at_same_addr with c f lbn lpo d c' f'; trivial.
  desbnat.
  unfold fld_read.
  destruct fld as [c f]. 
  destruct fld' as [c' f'].
  rewrite hdd_read_write_not_same_addr with hdd sec sec0 d hdd'; trivial.
  rewrite H0.
  unfold fld_read.
  destruct (lpn_to_lbn_off sec0) as [lbn' lpo'] eqn:Hsec0.
  unfold fld_write in H2.
  destruct (lpn_to_lbn_off sec) as [lbn lpo] eqn:Hsec.
  rewrite (ftl_read_write_not_same_addr c f  lbn lpo d c' f' H H2 lbn' lpo'); trivial.
  destruct (addr_neq_trans_implies_neq sec sec0 lbn lpo lbn' lpo'); trivial.
  left; trivial.
  destruct H3.
  right; auto.
Qed.

Lemma fld_run_deterministic : 
  forall fld cmd fld1 bh1 fld2 bh2,
    fld_run fld cmd fld1 bh1 
    -> fld_run fld cmd fld2 bh2
    -> fld1 = fld2 /\ bh1 = bh2.
Proof.
  intros.
  destruct cmd.
    simpl in * .
    destruct H as [d1 [H11 [H12 H13]]].
    destruct H0 as [d2 [H21 [H22 H23]]].
    rewrite H11 in H21.
    inversion H21.
    subst.
    split; trivial.
  simpl in * .
  destruct H as [H11 H12].
  destruct H0 as [H21 H22].
  rewrite H11 in H21.
  inversion H21; subst.
  split; trivial.
Qed.

Lemma Inv_fld_init : Inv fld_init.
Proof.
  unfold Inv, fld_init.
  apply Inv_ftl_init; trivial.
Qed.

Lemma fld_write_Inv : 
  forall hdd hdd' fld sec d,
    Inv fld
    -> hdd_write hdd sec d = Some hdd'
    -> exists fld', fld_write fld sec d = Some fld'
                    /\ Inv fld'.
Proof.
  intros.
  destruct fld as [c f].
  unfold fld_write.
  destruct (lpn_to_lbn_off sec) as [lbn off] eqn:Ha.
  assert (Hv: valid_sector_no sec).
    eapply hdd_write_some_implies_valid_addr; eauto.
  assert (Hb: valid_logical_block_no lbn).
    eapply valid_lpn_implies_valid_lbn; eauto.
  assert (Ho: valid_page_off off).
    eapply valid_lpn_implies_valid_off; eauto.
  destruct (ftl_write_Inv c f lbn off d) as [c' [f' [Hx Hy]]]; auto.
  exists (c', f').
  split; trivial.
Qed.

Lemma simu_one_step_progress : 
  forall cmd : command, 
    forall (hdd hdd': hard_disk) (bh: behav) (fld: flash_device),
      Inv fld
      -> R hdd fld
      -> hdd_run hdd cmd hdd' bh
      -> exists fld': flash_device, fld_run fld cmd fld' bh.
Proof.  
  intros.
  destruct cmd.
  intros.
  exists fld.
  inversion H1.
  subst hdd0 sec hdd' bh.
  unfold fld_run.
  inversion H1.
  subst hdd0 lpn0 d0.
  clear H3.
  exists d.
  split.
    unfold R in H0.
    rewrite <- H0; trivial.
  split; trivial.
  inversion H1.
  subst hdd0 sec d0 hdd'0 bh.
  destruct (fld_write_Inv hdd hdd' fld lpn d H Hdw) as [fld' [Hfld' Hinv]].
  exists fld'; trivial.
  unfold fld_run.
  split; trivial.
Qed.    

 Lemma simu_one_step_preservation : 
  forall cmd : command, 
    forall (hdd hdd': hard_disk) (bh: behav) (fld fld': flash_device),
      Inv fld
      -> R hdd fld
      -> hdd_run hdd cmd hdd' bh
      -> fld_run fld cmd fld' bh
      -> Inv fld' /\ R hdd' fld'.
Proof.  
  intros.
  destruct cmd.
  inversion H1.
  subst hdd0 sec hdd' bh.
  unfold fld_run in H2.
  destruct H2 as [dx [Hfr [Hdx Hfld']]].
  subst fld'.
  injection Hdx.
  intro; subst dx.
  split; trivial.
  inversion H1.
  subst hdd0 sec hdd'0 d0 bh.
  unfold fld_run in H2.
  destruct H2 as [Hfw _].
  destruct (fld_write_Inv hdd hdd' fld lpn d H Hdw) as [fld'' [Hfld' Hinv']].
  assert (fld'' = fld').
    rewrite Hfw in Hfld'.
    injection Hfld'; auto.
  subst fld''.
  split; trivial.
  apply fld_write_R_preservation with hdd fld lpn d; trivial. 
Qed.

Lemma simu_multi_steps_progress : 
  forall cl : list command, 
    forall (hd hd': hard_disk) (B: behavior) (fl: flash_device),
      Inv fl
      -> R hd fl
      -> hdd_run_cmd_list hd cl hd' B
      -> exists fl': flash_device, fld_run_cmd_list fl cl fl' B.
Proof.
  induction cl.
    intros.
    destruct B.
      exists fl; trivial.
    simpl in H1.
    simpl. trivial.
    simpl in H1.
    destruct H1.
  intros.
  destruct B.
    simpl in H1.
    destruct H1.
  simpl in H1.
  destruct H1 as [hd'' [H1 H2]].
  rename a into cmd.
  rename b into bh.
  destruct (simu_one_step_progress cmd hd hd'' bh fl H H0 H1) as [fl'' Hfl''].
  destruct (simu_one_step_preservation cmd hd hd'' bh fl fl'' H H0 H1 Hfl'') as [Hx1 Hx2].
  assert (Hx := IHcl hd'' hd' B fl'' Hx1 Hx2 H2).
  destruct Hx as [fl' Hfl'].
  exists fl'.
  simpl.
  exists fl''; split; trivial.
Qed.

Lemma simu_multi_steps_preservation : 
  forall cl : list command, 
    forall (hd hd': hard_disk) (B: behavior) (fl fl': flash_device),
      Inv fl
      -> R hd fl
      -> hdd_run_cmd_list hd cl hd' B
      -> fld_run_cmd_list fl cl fl' B
      -> Inv fl' /\ R hd' fl'.
Proof.
  induction cl.
    intros.
    destruct B.
      simpl in H1.
      simpl in H2.
      subst; trivial.
      split; trivial.
    simpl in H1.
    destruct H1.
  intros.
  destruct B.
    simpl in H1.
    destruct H1.
  simpl in H1.
  destruct H1 as [hd'' [H11 H12]].
  rename a into cmd.
  rename b into bh.
  simpl in H2.
  destruct H2 as [fl'' [H21 H22]].
  destruct (simu_one_step_preservation cmd hd hd'' bh fl fl'' H H0 H11 H21) as [Hx1 Hx2].
  eapply IHcl; eauto.
Qed.

Theorem Correctness : 
  forall cl : list command, 
    forall (hd hd': hard_disk) (B: behavior) (fl: flash_device),
      hdd_run_cmd_list hdd_init cl hd' B
      -> exists fl': flash_device, fld_run_cmd_list fld_init cl fl' B.
Proof.
  intros.
  apply simu_multi_steps_progress with hdd_init hd'; trivial.
  apply Inv_fld_init.
  apply R_init.
Qed.

