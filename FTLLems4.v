(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Hui Zhang <sa512073@mail.ustc.edu.cn>                            *)
(*                                     School of Software Engineering, USTC   *)
(*                                                                            *)
(*           Longying Yang <vittayang@gmail.com>                              *)
(*                          School of Computer Science and Technology, USTC   *)
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
Require Import FTLLems3.

(* Hypothesis 1. *)

Lemma Inv_ftl_init : Inv nand_init ftl_init.
Proof.
  unfold Inv.
  split.
    unfold F_Inv. 
    unfold ftl_init. 
    simpl.
    split (* I1 *).
      unfold I_pbn_bit_valid, bit_init.
      intros pbn.
      split.
        intro Hv.
        unfold bit_get.
        exists blank_bi.
        apply list_get_list_repeat_list.
        unfold valid_block_no in Hv.
        unfold bvalid_block_no in Hv.
        apply blt_true_lt; trivial.
      intros [bi Hbi].
      unfold valid_block_no.
      destruct (bvalid_block_no pbn) eqn:Hpbn; trivial.
      unfold bit_get in Hbi.
      rewrite (@list_get_list_repeat_list_none _ pbn blank_bi BLOCKS) in Hbi; try discriminate.
      apply blt_false_le; trivial.
    split (* I2 *).
      unfold I_pbn_bmt_valid, bmt_init.
      intros.
      unfold pbn_in_bmt_lbn in H.
      destruct H as [H | H].
        destruct H.
        unfold bmt_get in H.
        destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn:Hlbn; trivial.
          rewrite list_get_list_repeat_list in H.
            discriminate.
          apply blt_true_lt; trivial.
        rewrite list_get_list_repeat_list_none in H.
        discriminate.
      apply blt_false_le; trivial.
      destruct H.
      unfold bmt_get in H.
      destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn:Hlbn; trivial.
        rewrite list_get_list_repeat_list in H.
          discriminate.
        apply blt_true_lt; trivial.
      rewrite list_get_list_repeat_list_none in H.
      discriminate.
      apply blt_false_le; trivial.
    split (* I2 *).
      unfold I_pbn_fbq_valid, fbq_init.
      intros pbn.
      unfold fbq_in.
      intro H.
      destruct (@list_inb_true_elim _ _ _ _ H beq_true_eq) as [i Hg].
      apply list_make_nat_list_get_some_elim in Hg.
      apply Hg.
    split (* I4 *).
      unfold I_pbn_fbq_state, bit_init, fbq_init.
      intros pbn bi Hfbq Hbit.
      unfold bit_get in Hbit.      
      destruct (@list_get_list_repeat_list_some_elim _ pbn blank_bi bi BLOCKS Hbit) as [H1 H2].
      unfold blank_bi in H2.
      subst bi.
      simpl.
      right; trivial.
    split (* I5 *).
      unfold I_pbn_bmt_used, bit_init, bmt_init.
      intros lbn pbn bi Hgbi.
      split.
        intro H.
        destruct H as [x H].
        unfold bmt_get in H.
        destruct (@list_get_list_repeat_list_some_elim _ pbn blank_bi bi BLOCKS Hgbi) as [H1 H2].
        unfold bmt_record in H.
        assert (Hx := @list_get_list_repeat_list (bmt_record) lbn (None, None) MAX_LOGICAL_BLOCKS).
        unfold bmt_record in Hx.
        rewrite H in Hx.
        destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn: Hlbn.
          desbnat.
          apply Hx in Hlbn.
          discriminate.
        rewrite (@list_get_list_repeat_list_none _ lbn (None, None) MAX_LOGICAL_BLOCKS) in H.
        discriminate.
        clear - Hlbn.
        desbnat.
        trivial.
      intro H.
      destruct H as [x H].
      unfold bmt_get in H.
      destruct (@list_get_list_repeat_list_some_elim _ pbn blank_bi bi BLOCKS Hgbi) as [H1 H2].
      unfold bmt_record in H.
      assert (Hx := @list_get_list_repeat_list (bmt_record) lbn (None, None) MAX_LOGICAL_BLOCKS).
      unfold bmt_record in Hx.
      rewrite H in Hx.
      destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn: Hlbn.
        desbnat.
        apply Hx in Hlbn.
        discriminate.
      rewrite (@list_get_list_repeat_list_none _ lbn (None, None) MAX_LOGICAL_BLOCKS) in H.
      discriminate.
      clear - Hlbn.
      desbnat.
      trivial.
    split (* I6 *).
      unfold I_pbn_habitation, bmt_init, fbq_init.
      intros pbn Hvpbn.
      right.
      split.
        intros lbn HF.
        destruct HF as [[x HF] | [x HF]]. 
          unfold bmt_get in HF.
          destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn: Hlbn.
            desbnat.
            assert (Hx := @list_get_list_repeat_list (bmt_record) lbn (None, None) MAX_LOGICAL_BLOCKS Hlbn). 
            unfold bmt_record in Hx. 
            unfold bmt_record in HF.
            rewrite HF in Hx.
            discriminate.
          assert (Hx := @list_get_list_repeat_list_none bmt_record lbn (None, None) MAX_LOGICAL_BLOCKS).
          unfold bmt_record in Hx. 
          unfold bmt_record in HF.
          rewrite HF in Hx.
          desbnat.
          discriminate (Hx Hlbn).
        unfold bmt_get in HF.
        destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn: Hlbn.
          desbnat.
          assert (Hx := @list_get_list_repeat_list (bmt_record) lbn (None, None) MAX_LOGICAL_BLOCKS Hlbn). 
          unfold bmt_record in Hx. 
          unfold bmt_record in HF.
          rewrite HF in Hx.
          discriminate.
        assert (Hx := @list_get_list_repeat_list_none bmt_record lbn (None, None) MAX_LOGICAL_BLOCKS).
        unfold bmt_record in Hx. 
        unfold bmt_record in HF.
        rewrite HF in Hx.
        desbnat.
        discriminate (Hx Hlbn).
      unfold fbq_in.
     apply list_inb_true_intro with pbn.
       apply list_make_nat_list_get_some_intro.
       trivial.
     apply beq_false_neq.
    split (* I7_1 *).
      unfold I_pbn_bmt_distinguishable, bmt_init.
      intros lbn lbn' pbn pbn' Hneq Hin Hin'.
      destruct Hin as [H | H]; destruct H as [x H].
        unfold bmt_get in H.
        destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn:Hx.
          rewrite list_get_list_repeat_list in H; trivial.
            discriminate.
          apply blt_true_lt; trivial.
        rewrite list_get_list_repeat_list_none in H.
          discriminate.
        apply blt_false_le; trivial.
      unfold bmt_get in H.
      destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn:Hx.
        rewrite list_get_list_repeat_list in H; trivial.
          discriminate.
        apply blt_true_lt; trivial.
      rewrite list_get_list_repeat_list_none in H.
        discriminate.
      apply blt_false_le; trivial.
    split (* I7_2 *).
      unfold I_pbn_bmt_distinguishable_2, bmt_init.
      intros lbn pbn pbn' Hin.
      unfold bmt_get in Hin.
      destruct (blt_nat lbn MAX_LOGICAL_BLOCKS) eqn:Hx.
        rewrite list_get_list_repeat_list in Hin; trivial.
          discriminate.
        apply blt_true_lt; trivial.
      rewrite list_get_list_repeat_list_none in Hin.
        discriminate.
      apply blt_false_le; trivial.
    split (* I8 *).
      unfold I_pbn_fbq_distinguishable, fbq_init.
      unfold fbq_get.
      intros i i' pbn pbn' Hneq Hi Hi'.
      destruct (list_make_nat_list_get_some_elim Hi) as [Hi1 Hi2].
      destruct (list_make_nat_list_get_some_elim Hi') as [Hi'1 Hi'2].
      subst pbn pbn'.
      trivial.
    (* I10 *)
    unfold I_valid_lbn_has_entry_in_bmt.
    unfold bmt_get, bmt_init.
    intro lbn.
    split.
      intros Hlbn.
      exists (None, None).
      apply list_get_list_repeat_list.
      apply blt_true_lt.
      trivial.
    intros [bmt Hlbn].
    destruct (list_get_list_repeat_list_some_elim Hlbn).
    trivial.
  (* R_Inv *)
  unfold R_Inv.
  unfold ftl_init.
  simpl.
  unfold J_bi_block_coherent, bit_init.
  intros pbn bi Hgbi.
  unfold chip_bi_coherent.
  exists init_block.
  split.
    unfold chip_get_block, nand_init.
    unfold chip_blocks.
    apply list_get_list_repeat_list.
    destruct (list_get_list_repeat_list_some_elim Hgbi).
    apply blt_true_lt; trivial.
  unfold bit_get in Hgbi.
  destruct (list_get_list_repeat_list_some_elim Hgbi).
  subst bi.
  simpl.
  unfold block_coherent_erased.
  unfold blank_bi; simpl.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  intros loc Hvloc.
  exists init_page.
  split.
    unfold block_get_page, init_block.
    unfold block_pages.
    rewrite Hvloc.
    rewrite list_get_list_repeat_list; trivial.
    apply blt_true_lt.
    trivial.
  unfold init_page.
  simpl.
  trivial.
Qed.

(* Hypothesis 2. *)

Lemma ftl_read_ftl_init : 
  forall lbn lpo,
    valid_logical_block_no lbn 
    -> valid_page_off lpo
    -> FTL_read nand_init ftl_init lbn lpo = Some (zero_data SECTOR_DATA_SIZE).
Proof.
  intros lbn lpo Hvlbn Hvlpo.
  unfold nand_init, ftl_init.
  unfold FTL_read.
  assert (Hvoff : bvalid_page_off lpo = true).
    unfold valid_page_off in Hvlpo.
    trivial.
  simpl.
  rewrite Hvoff.
  unfold bmt_get, bmt_init.
  rewrite list_get_list_repeat_list; trivial.
  apply blt_true_lt; trivial.
Qed.

(* Hypothesis 3. *)

Lemma ftl_read_write_at_same_addr : 
  forall c f lbn lpo v c' f',
    Inv c f 
    -> FTL_write c f lbn lpo v = Some (c', f')
    -> FTL_read c' f' lbn lpo = Some v.
Proof.
  intros c f lbn lpo v c' f' HI Hw.
  assert (Hv: valid_logical_block_no lbn).
    destruct (ftl_write_some_implies_valid_addr _ _ _ _ _ _ _ HI Hw) as [Hx Hy].
    trivial.
  assert (Ho: valid_page_off lpo).
    destruct (ftl_write_some_implies_valid_addr _ _ _ _ _ _ _ HI Hw) as [Hx Hy].
    trivial.
  destruct (ftl_write_spec c f lbn lpo v HI Hv Ho) as [c'' [f'' [Hw'' [HI'' [Hr'' _]]]]].
  rewrite Hw in Hw''.
  injection Hw''; intros; subst c'' f''.
  trivial.
Qed.

(* Hypothesis 4. *)

Lemma ftl_read_write_not_same_addr : 
  forall c f lbn  lpo v c' f',
    Inv c f
    -> FTL_write c f lbn lpo v = Some (c', f')
    -> forall lbn' lpo', 
         (lbn <> lbn' \/ lpo <> lpo')
         -> FTL_read c' f' lbn' lpo' = FTL_read c f lbn' lpo'.
Proof.
  intros c f lbn lpo v c' f' HI Hw lbn' lpo' Hneq.
  assert (Hv: valid_logical_block_no lbn).
    destruct (ftl_write_some_implies_valid_addr _ _ _ _ _ _ _ HI Hw) as [Hx Hy].
    trivial.
  assert (Ho: valid_page_off lpo).
    destruct (ftl_write_some_implies_valid_addr _ _ _ _ _ _ _ HI Hw) as [Hx Hy].
    trivial.
  destruct (ftl_write_spec c f lbn lpo v HI Hv Ho) as [c'' [f'' [Hw'' [HI'' [Hr'' [Hx Hy]]]]]].
  rewrite Hw in Hw''.
  injection Hw''; intros; subst c'' f''.
  destruct Hneq as [Hr1 | Hr2].
    rewrite (Hy lbn' lpo'); auto.
  destruct (nat_eq_dec lbn lbn') as [Heq | Hneq].
    subst lbn'.
    apply Hx; auto.
  apply Hy; auto.
Qed.

(* Hypothesis 5. *)

Lemma ftl_write_Inv : 
  forall c f lbn lpo d,
    Inv c f
    -> valid_logical_block_no lbn 
    -> valid_page_off lpo
    -> exists c' f', FTL_write c f lbn lpo d = Some (c', f')
                    /\ Inv c' f'.
Proof.
  unfold R; intros.
  destruct (ftl_write_spec c f lbn lpo d H H0 H1) as [c'' [f'' [Hw'' [HI'' [Hr'' [Hx Hy]]]]]].
  exists c'', f''.
  split; trivial.
Qed.
