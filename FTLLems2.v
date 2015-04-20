(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import LibEx.
Require Import List.
Require Import ListEx.
Require Import Arith.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.
Require Import NandLems.

Require Import Bast0.
Require Import FTLProp.
Require Import FTLLems.
Require Import Framework.

Require Import Inv.
Require Import InvLems.
Require Import Inv2.

Lemma write_data_block_spec_write_nonemp: 
  forall c pbn b bi loc d, 
    chip_get_block c pbn = Some b
    -> bvalid_block_no pbn = true
    -> bvalid_page_off loc = true
    -> block_coherent_data_partial loc b
    -> bi_used_pages bi = loc
    -> exists c' bi', 
         write_data_block c bi pbn loc d = Some (c', bi')
         /\ bi_used_pages bi' = S (bi_used_pages bi)
         /\ bi_state bi' = bi_state bi
         /\ bi_erase_count bi' = bi_erase_count bi
         /\ (exists b', chip_get_block c' pbn = Some b' 
                        /\ block_coherent_data_partial (S loc) b')
         /\ read_data_block c' pbn loc = Some d
         /\ (forall loc', 
               loc <> loc'
               -> read_data_block c' pbn loc' = read_data_block c pbn loc')
         /\ (forall pbn',
               pbn' <> pbn
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c pbn b bi loc d Hb Hpbn Hloc Hbco Hbi.
  unfold write_data_block.
  unfold block_coherent_data_partial in Hbco.
  destruct Hbco as [Hbloc [Hbs Hbco]].
  assert (Hloc2: valid_page_off loc).
    unfold valid_page_off.
    trivial.
  assert (Hbloc2: blt_nat loc loc = false).
    simplbnat.
    trivial.
  assert (Hbloc3: ble_nat (next_page b) loc = true).
    unfold ble_nat.
    rewrite Hbloc.
    simplbnat.
    trivial.
  destruct (Hbco loc Hloc2) as [Hbco1 Hbco2].
  destruct (Hbco2 Hbloc2) as [p [Hp1 Hp2]].
  destruct (nand_write_page_spec c pbn loc d init_page_oob b p Hpbn Hloc Hb Hp1 Hbloc3 Hp2) 
    as [c' [Hw [Hrp Hrb]]].
  exists c'; exists (mk_bi (bi_state bi) (bi_used_pages bi + 1) (bi_erase_count bi)).
  rewrite Hw.
  simpl.
  split; trivial.
  split. 
    rewrite plus_comm.
    simpl; trivial.
  split; trivial.
  split; trivial.
  split.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hr Hnr]]]]]].
    exists b'.
    split; trivial.
    unfold block_coherent_data_partial.
    split; trivial.
    split; trivial.
    intros off Hoff.
    clear Hbco1 Hbco2.
    destruct (Hbco off Hoff) as [Hbco1 Hbco2].
    split.
      intros Hloc'.
      assert (Hx: blt_nat off loc = true \/ beq_nat off loc = true).
        clear - Hloc'.
        desbnat.
        apply lt_n_Sm_le in Hloc'.
        assert (off < loc \/ off = loc).
        apply le_lt_or_eq in Hloc'.
        trivial.
        destruct H; [left | right]. 
        apply lt_blt_true; trivial.
        subst off.
        simplbnat;  trivial.
      destruct Hx as [Hx | Hx].
      destruct (Hbco1 Hx) as [px [Hgpx Hpxs]].
      assert (Hy: off <> loc).
        clear - Hx.
        intro HF.
        subst off.
        simplbnat.
      rewrite (Hnr off Hy Hoff).
      apply Hbco1; trivial.
      assert (off = loc).
        rewbnat Hx.
        trivial.
      subst off.
      destruct Hr as [p' [Hgp' Hp']].
      exists p'.
      split; trivial.
      rewrite Hp'.
      simpl; trivial.
    intro Hoff'.
    assert (off <> loc).
      desbnat.
      clear - Hoff'.
      omega.
    rewrite (Hnr off H Hoff).
    assert (blt_nat off loc = false).
      clear - Hoff' H.
      desbnat.
      solvebnat.
    apply Hbco2; trivial.
  split.
    unfold read_data_block.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hloc.
    destruct Hp' as [p' [Hgp' Hp']].
    rewrite Hgp'.
    rewrite Hp'.
    simpl.
    trivial.
  split.
    intros loc' Hloc'.
    unfold read_data_block.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hb.
    destruct (bvalid_page_off loc') eqn:Hvloc'; trivial.
    rewrite (Hp'2 loc' (neq_sym Hloc') Hvloc').
    destruct (block_get_page b loc') eqn:Hgloc'; trivial.
  intros pbn' Hpbn'.
  rewrite Hrb; trivial.
Qed.

Lemma write_data_block_spec_write_emp: 
  forall c pbn b bi loc d, 
    chip_get_block c pbn = Some b
    -> bvalid_block_no pbn = true
    -> bvalid_page_off loc = true
    -> block_coherent_erased bi b
    -> bi_used_pages bi = loc
    -> exists c' bi', 
         write_data_block c bi pbn loc d = Some (c', bi')
         /\ bi_used_pages bi' = S (bi_used_pages bi)
         /\ bi_state bi' = bi_state bi
         /\ bi_erase_count bi' = bi_erase_count bi
         /\ (exists b', chip_get_block c' pbn = Some b' 
                        /\ block_coherent_data_partial 1 b')
         /\ read_data_block c' pbn loc = Some d
         /\ (forall loc', 
               loc <> loc'
               -> read_data_block c' pbn loc' = read_data_block c pbn loc')
         /\ (forall pbn',
               pbn' <> pbn
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c pbn b bi loc d Hb Hpbn Hloc Hbco Hbi.
  unfold write_data_block.
  unfold block_coherent_erased in Hbco.
  destruct Hbco as [Hbibs [Hbu [Hbs [Hnp Hbco]]]].
  assert (Hloc2: valid_page_off loc).
    unfold valid_page_off.
    trivial.
  destruct (Hbco loc Hloc2) as [p [Hp1 Hp2]].
  assert (Hbloc3: ble_nat (next_page b) loc = true).
    rewrite Hnp.
    unfold ble_nat.
    simplbnat.
    trivial.
  destruct (nand_write_page_spec c pbn loc d init_page_oob b p Hpbn Hloc Hb Hp1 Hbloc3 Hp2) 
    as [c' [Hw [Hrp Hrb]]].
  exists c'; exists (mk_bi (bi_state bi) (bi_used_pages bi + 1) (bi_erase_count bi)).
  rewrite Hw.
  simpl.
  split; trivial.
  split. 
    rewrite plus_comm.
    simpl; trivial.
  split; trivial.
  split; trivial.
  split.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hr Hnr]]]]]].
    exists b'.
    split; trivial.
    unfold block_coherent_data_partial.
    unfold bi_used_pages in Hbi.
    assert (loc = 0).
      destruct bi.
      rewrite Hnp  in Hbu.
      simpl in Hbu.
      rewrite Hbu in Hbi.
      subst loc; trivial.
    split.
      rewrite Hnp'.
      rewrite H.
      trivial.
    split; trivial.
    intros off Hoff.
    clear Hbi.
    split.
      intros Hloc'.
      assert (Hx: off = loc).
        rewrite H.
        clear - Hloc'.
        desbnat.
        destruct off.
        trivial.
        apply False_ind.
        omega.
      destruct Hr as [p' [Hgp' Hp']].
      rewrite Hx.
      rewrite Hgp'.
      exists p'; split; trivial.
      rewrite Hp'.
      simpl; trivial.
    intro Hoff'.
    assert (Hneq : off <> loc).
      rewrite H.
      clear - Hoff'.
      desbnat.
      omega.
    rewrite (Hnr off Hneq Hoff).
    apply Hbco; trivial.
  split.
    unfold read_data_block.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hloc.
    destruct Hp' as [p' [Hgp' Hp']].
    rewrite Hgp'.
    rewrite Hp'.
    simpl.
    trivial.
  split.
    intros loc' Hloc'.
    unfold read_data_block.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hb.
    destruct (bvalid_page_off loc') eqn:Hvloc'; trivial.
    rewrite (Hp'2 loc' (neq_sym Hloc') Hvloc').
    destruct (block_get_page b loc') eqn:Hgloc'; trivial.
  intros pbn' Hpbn'.
  rewrite Hrb; trivial.
Qed.

(* small revision: bi_state should be (bs_log lbn pmt) *)
Lemma write_log_block_spec_write_emp: 
  forall c pbn b bi off lbn d, 
    chip_get_block c pbn = Some b
    -> bvalid_block_no pbn = true
    -> bvalid_page_off off = true
    -> (bi_state bi = bs_log lbn blank_pmt
        /\ bi_used_pages bi = next_page b
        /\ block_state b = bs_free
        /\ next_page b = 0
        /\ (forall loc,
              valid_page_off loc
              -> exists p, block_get_page b loc = Some p
                           /\ page_state p = ps_free))
    -> exists c' bi', 
         write_log_block c bi pbn off d = Some (c', bi')
         /\ bi_used_pages bi' = S (bi_used_pages bi)
         /\ bi_lbn bi' = Some lbn 
         /\ bi_erase_count bi' = bi_erase_count bi
         /\ (exists b', chip_get_block c' pbn = Some b' 
                        /\ block_coherent_log bi' b')
         /\ read_log_block c' bi' pbn off = Some d
         /\ (forall off', 
               off <> off'
               -> read_log_block c' bi' pbn off' = read_log_block c bi pbn off')
         /\ (forall pbn',
               pbn' <> pbn
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c pbn b bi off lbn d. 
  intros Hb Hpbn Hoff Hbco.
  unfold write_log_block.
  destruct Hbco as [Hbilbn [Hup [Hbs [Hnp Hbco]]]].
  assert (Hfe: exists loc, find_empty_page_in_block bi = Some loc /\ loc = 0).
    unfold find_empty_page_in_block.
    rewrite Hup.
    rewrite Hnp.
    simpl.
    exists 0; split; trivial.
  destruct Hfe as [loc [Hfe Hloc]].
  rewrite Hfe.
  assert (Hvloc: valid_page_off loc).
    rewrite Hloc.
    unfold valid_page_off.
    simpl.
    trivial.
  destruct (Hbco loc Hvloc) as [p [Hp1 Hp2]].
  assert (Hbloc3: ble_nat (next_page b) loc = true).
    rewrite Hloc.
    rewrite Hnp.
    unfold ble_nat.
    simpl.
    trivial.
  destruct (nand_write_page_spec c pbn loc d init_page_oob b p Hpbn Hvloc Hb Hp1 Hbloc3 Hp2) 
    as [c' [Hw [Hrp Hrb]]].
  exists c'.
  rewrite Hw.
  unfold bi_lbn in Hbilbn.
  destruct bi as [bi_s bi_up bi_ec].
  simpl in * .
  simpl.
  destruct bi_s as [ | | lbnx | lbnx pmt]; try discriminate.
  injection Hbilbn; intros; subst lbnx pmt; clear Hbilbn.
  simpl.
  assert (Hgloc: pmt_get blank_pmt loc = Some pmte_empty).
    destruct (blank_pmt_shape loc).
    apply H.
    apply Hvloc.
  destruct (pmt_update_spec blank_pmt loc off Hvloc Hgloc) 
    as [pmt' [Hpu [Hrpmt Hrpmt']]].
  rewrite Hpu.
  exists (mk_bi (bs_log lbn pmt') (bi_up + 1) bi_ec).
  split; trivial.
  simpl.
  split. 
    rewrite plus_comm.
    simpl; trivial.
  split; trivial.
  split; trivial.
  split.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hr Hnr]]]]]].
    exists b'.
    split; trivial.
    unfold block_coherent_log.
    exists pmt', lbn.
    simpl.
    split; trivial.
    rewrite Hnp'.
    rewrite Hup.
    rewrite Hloc.
    rewrite Hnp.
    simpl.
    split; trivial.
    split; trivial.
    split.
      apply (pmt_update_pmt_len _ _ _ _ Hpu); trivial.
    split.
      unfold pmt_page_state.
      intros loc' Hloc'.
      split.
        intros Hgloc'.
        destruct (page_off_eq_dec loc loc') as [Heq | Hneq].
          subst loc'.
          apply False_ind.
          rewrite Hrpmt in Hgloc'.
          discriminate.
        rewrite (Hnr loc' (neq_sym Hneq) Hloc').
        apply Hbco; trivial.
      intros off' Hgloc'.
      assert (Hloc'eq: loc = loc').
        destruct (page_off_eq_dec loc loc'); trivial.
        rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu (neq_sym H)) in Hgloc'.
        destruct (blank_pmt_shape loc') as [H1 H2].
        destruct (bvalid_page_off loc') eqn:Hvloc'.
          rewrite (H1 (refl_equal _)) in Hgloc'.
          discriminate.
        rewrite (H2 (refl_equal _)) in Hgloc'.
        discriminate.
      subst loc'.
      rewrite Hrpmt in Hgloc'.
      injection Hgloc'; intro; subst off'; clear Hgloc'.
      destruct Hr as [p' [Hgp' Hp']].
      exists p'.
      split; trivial.
      rewrite Hp'; simpl; trivial.
    unfold pmt_shape.
    intros loc' Hloc'.
    split.
      intros Hloc'2.
      assert (loc' = 0).
        clear - Hloc'2.
        desbnat.
        destruct loc'; trivial.
        apply False_ind.
        omega.
      exists off.
      rewrite H.
      rewrite <- Hloc.
      trivial.
    intro Hloc'2.
    assert (loc <> loc').
      rewrite Hloc.
      clear - Hloc'2.
      desbnat.
      omega.
    rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu (neq_sym H)).
    destruct (blank_pmt_shape loc') as [H1 H2].
    apply H1.
    trivial.
  split.
    unfold read_log_block.
    unfold find_page_in_log_block.
    unfold bi_state.
    assert (Hx: pmt_find_rev pmt' (pmte_log off) = Some loc).
      apply pmt_update_pmt_find_rev with blank_pmt; trivial.
      apply blank_pmt_is_domain_complete; trivial.
      rewrite Hloc.
      apply blank_pmt_shape'; trivial.
    rewrite Hx.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hvloc.
    destruct Hp' as [p' [Hgp' Hp']].
    rewrite Hgp'.
    rewrite Hp'.
    simpl.
    trivial.
  split.
    intros off' Hoff'.
    unfold read_log_block.
    unfold find_page_in_log_block.
    unfold bi_state.
    assert (Hx: pmt_find_rev pmt' (pmte_log off') = pmt_find_rev blank_pmt (pmte_log off')).
      apply pmt_update_pmt_find_rev_neq with loc off; trivial.
      apply neq_sym; trivial.
    rewrite Hx.
    destruct (pmt_find_rev blank_pmt (pmte_log off')) as [locx | ] eqn: Hfind; trivial.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hb.
    destruct (bvalid_page_off locx) eqn:Hvlocx; trivial.
    assert (Hneq : locx <> loc).
      intros HF.
      subst locx.
      rewrite (pmt_find_rev_pmt_get _ _ _ Hfind) in Hgloc.
      discriminate.
    rewrite (Hp'2 locx Hneq Hvlocx).
    destruct (block_get_page b locx) eqn:Hglocx; trivial.
  intros pbn' Hpbn'.
  rewrite Hrb; trivial.
Qed.

Lemma write_log_block_spec_write_nonemp: 
  forall c pbn b bi off lbn d, 
    chip_get_block c pbn = Some b
    -> bvalid_block_no pbn = true
    -> bvalid_page_off off = true
    -> bi_lbn bi = Some lbn
    -> bvalid_page_off (next_page b) = true
    -> block_coherent_log bi b
    -> exists c' bi', 
         write_log_block c bi pbn off d = Some (c', bi')
         /\ bi_used_pages bi' = S (bi_used_pages bi)
         /\ bi_erase_count bi' = bi_erase_count bi
         /\ bi_lbn bi' = Some lbn
         /\ (exists b', 
               chip_get_block c' pbn = Some b' /\ 
               block_coherent_log bi' b')
         /\ read_log_block c' bi' pbn off = Some d
         /\ (forall off', 
               off <> off'
               -> read_log_block c' bi' pbn off' = read_log_block c bi pbn off')
         /\ (forall pbn',
               pbn' <> pbn
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c pbn b bi off lbn d. 
  intros Hb Hpbn Hoff Hbi2 Hnpb Hbco.
  unfold write_log_block.
  unfold block_coherent_log in Hbco.
  destruct Hbco as [pmt [lbnx [Hbis [Hup [Hbs [Hpd [Hpps Hps]]]]]]].
  assert (Hfe: exists loc, find_empty_page_in_block bi = Some loc 
                           /\ pmt_get pmt loc = Some pmte_empty
                           /\ loc = next_page b 
                           /\ loc < length pmt).
    unfold find_empty_page_in_block.
    rewrite Hup.
    unfold bvalid_page_off in Hnpb.
    rewrite Hnpb.
    exists (next_page b).
    split; trivial.
    split.
      destruct (Hps (next_page b) Hnpb) as [H1 H2].
      apply H2.
      simplbnat.
      trivial.
    split; trivial.
    unfold pmt_domain_is_complete in Hpd.
    unfold pmt_len in Hpd.
    rewrite Hpd.
    clear - Hnpb.
    desbnat.
    trivial.
  destruct Hfe as [loc [Hfe [Hgloc [Hloc Hloc2]]]].
  rewrite Hfe.
  assert (Hvloc: valid_page_off loc).
    unfold valid_page_off.
    rewrite Hloc.
    trivial.
  assert (Hbloc2: blt_nat loc (next_page b)  = false).
    rewrite Hloc.
    simplbnat.
    trivial.
  assert (Hbloc3: ble_nat (next_page b) loc = true).
    rewrite Hloc.
    unfold ble_nat.
    simplbnat.
    trivial.
  destruct (Hps loc Hvloc) as [Hps1 Hps2].
  destruct (Hpps loc Hvloc) as [Hpps1 Hpps2].
  destruct (Hpps1 (Hps2 Hbloc2)) as [p [Hpg Hpst]].
  destruct (nand_write_page_spec c pbn loc d init_page_oob b p Hpbn Hvloc Hb Hpg Hbloc3 Hpst) 
    as [c' [Hw [Hrp Hrb]]].
  exists c'.
  rewrite Hw.
  unfold bi_lbn in Hbi2.
  rewrite Hbis in Hbi2.
  injection Hbi2; intro; subst lbnx; clear Hbi2.
  unfold bi_pm_table.
  rewrite Hbis.
  destruct (pmt_update_spec pmt loc off Hvloc Hgloc) 
    as [pmt' [Hpu [Hrpmt Hrpmt']]].
  rewrite Hpu.
  unfold bi_lbn.
  rewrite Hbis.
  exists (mk_bi (bs_log lbn pmt') (bi_used_pages bi + 1) (bi_erase_count bi)).
  split; trivial.
  simpl.
  split. 
    rewrite plus_comm.
    simpl; trivial.
  split; trivial.
  split; trivial.
  split.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hr Hnr]]]]]].
    exists b'.
    split; trivial.
    unfold block_coherent_log.
    exists pmt', lbn.
    simpl.
    split; trivial.
    rewrite Hnp'.
    rewrite Hup.
    rewrite Hloc.
    split.
      rewrite plus_comm.
      simpl; trivial.
    split; trivial.
    split.
      unfold pmt_domain_is_complete.
      rewrite (pmt_update_pmt_len _ _ _ _ Hpu); trivial.
    split.
      unfold pmt_page_state.
      intros loc' Hloc'.
      split.
        intros Hgloc'.
        destruct (page_off_eq_dec loc loc') as [Heq | Hneq].
          subst loc'.
          apply False_ind.
          rewrite Hrpmt in Hgloc'.
          discriminate.
        rewrite (Hnr loc' (neq_sym Hneq) Hloc').
        destruct (Hpps loc' Hloc') as [Hpps1' Hpps2'].
        apply Hpps1'; trivial.
        rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu (neq_sym Hneq)) in Hgloc'.
        trivial.
      intros off' Hgloc'.
      destruct (page_off_eq_dec loc loc') as [Heq | Hneq].
        subst loc'.
        rewrite Hrpmt in Hgloc'.
        injection Hgloc'; intro; subst off'; clear Hgloc'.
        destruct Hr as [p' [Hgp' Hp']].
        exists p'.
        split; trivial.
        rewrite Hp'; simpl; trivial.
      destruct (Hpps loc' Hloc') as [Hpps1' Hpps2'].
      rewrite (Hnr loc' (neq_sym Hneq) Hloc').
      apply Hpps2' with off'; trivial.
      rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu (neq_sym Hneq)) in Hgloc'.
      trivial.
    unfold pmt_shape.
    intros loc' Hloc'.
    split.
      intros Hloc'2.
      assert (loc' = (next_page b) \/ blt_nat loc' (next_page b) = true).
        rewrite <- Hloc.
        rewrite <- Hloc in Hloc'2.
        clear - Hloc'2.
        desbnat.
        apply lt_n_Sm_le in Hloc'2.
        apply le_lt_or_eq in Hloc'2.
        destruct Hloc'2.
          right.
          solvebnat.
          left; trivial.
      destruct H.
        exists off.
        rewrite H.
        rewrite <- Hloc.
        trivial.
      destruct (Hps loc' Hloc') as [Hps1' Hps2'].
      destruct (Hps1' H) as [off' Hgoff'].
      exists off'.
      assert (Hx : loc' <> loc).
        rewrite <- Hloc in H.
        clear - H.
        desbnat.
        intro HF.
        subst loc'.
        apply (lt_irrefl loc); trivial.
      rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu Hx); trivial.
    intros Hloc'2.
    assert (loc' <> loc).
      rewrite <- Hloc in Hloc'2.
      clear - Hloc'2.
      desbnat.
      omega.
    rewrite (pmt_update_pmt_get_neq _ _ _ _ _ Hpu H).
    destruct (Hps loc' Hloc') as [Hps1' Hps2'].
    apply Hps2'.
    clear - Hloc'2.
    desbnat.
    solvebnat.
  split.
    unfold read_log_block.
    unfold find_page_in_log_block.
    unfold bi_state.
    assert (Hx: pmt_find_rev pmt' (pmte_log off) = Some loc).
      apply pmt_update_pmt_find_rev with pmt; trivial.
      rewrite Hloc; trivial.
    rewrite Hx.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hvloc.
    destruct Hp' as [p' [Hgp' Hp']].
    rewrite Hgp'.
    rewrite Hp'.
    simpl.
    trivial.
  split.
    intros off' Hoff'.
    unfold read_log_block.
    unfold find_page_in_log_block.
    rewrite Hbis.
    simpl.
    assert (Hx: pmt_find_rev pmt' (pmte_log off') = pmt_find_rev pmt (pmte_log off')).
      apply pmt_update_pmt_find_rev_neq with loc off; trivial.
      apply neq_sym; trivial.
    rewrite Hx.
    destruct (pmt_find_rev pmt (pmte_log off')) as [locx | ] eqn: Hfind; trivial.
    unfold nand_read_page.
    rewrite Hpbn.
    destruct Hrp as [b' [Hb' [Hnp' [Hec' [Hbs' [Hp' Hp'2]]]]]].
    rewrite Hb'.
    rewrite Hb.
    destruct (bvalid_page_off locx) eqn:Hvlocx; trivial.
    assert (Hneq : locx <> loc).
      intros HF.
      subst locx.
      rewrite (pmt_find_rev_pmt_get _ _ _ Hfind) in Hgloc.
      discriminate.
    rewrite (Hp'2 locx Hneq Hvlocx).
    destruct (block_get_page b locx) eqn:Hglocx; trivial.
  intros pbn' Hpbn'.
  rewrite Hrb; trivial.
Qed.

Lemma read_data_block_spec_read_full: 
  forall c pbn b bi loc, 
    bvalid_block_no pbn = true
    -> bvalid_page_off loc = true
    -> chip_get_block c pbn = Some b
    -> block_coherent_data bi b
    -> exists d, 
         read_data_block c pbn loc = Some d.
Proof.
  unfold block_coherent_data.
  unfold read_data_block.
  unfold nand_read_page.
  intros.
  destruct H2 as [lbn [Hbi [Hbup [Hbbs [Hbnp Hg]]]]].
  rewrite H.
  rewrite H0.
  rewrite H1.
  destruct (Hg loc H0) as [p [Hp Hps]].
  rewrite Hp.
  exists (page_data p); trivial.
Qed.

Lemma read_data_block_spec_read_partial: 
  forall c pbn b loc loc', 
    bvalid_block_no pbn = true
    -> bvalid_page_off loc = true
    -> chip_get_block c pbn = Some b
    -> block_coherent_data_partial loc b
    -> blt_nat loc' loc = true
    -> exists d, 
         read_data_block c pbn loc' = Some d.
Proof.
  unfold block_coherent_data_partial, read_data_block.
  unfold nand_read_page.
  intros c pbn b loc loc' Hvpbn Hvloc Hg Hcob Hblt.
  rewrite Hvpbn.
  rewrite Hg.
  assert (blt_nat loc' PAGES_PER_BLOCK = true).
    clear - Hvloc Hblt.
    unfold bvalid_page_off in Hvloc.
    desbnat.
    solvebnat.
    omega.
  unfold bvalid_page_off.
  rewrite H.
  destruct Hcob as [Hnp [Hbs Hcob]].
  destruct (Hcob loc' H) as [H1 H2].
  destruct (H1 Hblt) as [p [Hgp Hps]].
  rewrite Hgp.
  exists (page_data p); trivial.
Qed.

Lemma read_data_block_eq :
  forall c c' pbn off,
    chip_get_block c' pbn = chip_get_block c pbn
    -> read_data_block c' pbn off = read_data_block c pbn off.
Proof.
  intros c c' pbn off H.
  unfold read_data_block, nand_read_page.
  destruct (bvalid_block_no pbn) eqn:Hvpbn; trivial.
  rewrite H.
  destruct (chip_get_block c pbn) eqn:Hgb; trivial.
Qed.


Lemma read_log_block_eq :
  forall c c' pbn bi off,
    chip_get_block c' pbn = chip_get_block c pbn
    -> read_log_block c' bi pbn off = read_log_block c bi pbn off.
Proof.
  intros c c' pbn bi off H.
  unfold read_log_block, nand_read_page.
  destruct (find_page_in_log_block bi off) eqn:Hfind; trivial.
  destruct (bvalid_block_no pbn) eqn:Hvpbn; trivial.
  rewrite H.
  destruct (chip_get_block c pbn) eqn:Hgb; trivial.
Qed.

Lemma alloc_block_spec :
  forall c bit bmt fbq, 
    I_pbn_bit_valid bit  (* I1 *)
    -> I_pbn_fbq_valid fbq  (* I3 *)
    -> I_pbn_fbq_state bit fbq (* I4 *)
    -> I_pbn_fbq_distinguishable fbq (* I8 *)
    -> I_fbq_len_greater_than_constant fbq (* SC *)
    -> J_bi_block_coherent c bit  (* J *)
    -> exists pbn c' f' bi', 
         alloc_block c (mk_FTL bit bmt fbq) = Some (pbn, (c', f'))
         /\ valid_block_no pbn
         /\ (bi_state bi' = bs_erased 
             /\ bi_used_pages bi' = 0)
         /\ (forall bi, bit_get bit pbn = Some bi 
                        -> bi_state bi = bs_invalid
                        -> bi_erase_count bi' = S (bi_erase_count bi)
                           /\ exists b, 
                                chip_get_block c pbn = Some b
                                /\ chip_set_block c pbn (erased_block (block_erase_count b)) = Some c')
         /\ (forall bi, bit_get bit pbn = Some bi 
                        -> bi_state bi = bs_erased 
                        -> bi_erase_count bi' = bi_erase_count bi
                           /\ c' = c)
         /\ (forall pbn', pbn' <> pbn -> chip_get_block c' pbn' = chip_get_block c pbn')
         /\ ftl_bm_table f' = bmt
         /\ bit_update bit pbn bi' = Some (ftl_bi_table f')
         /\ (fbq_in fbq pbn = true
             /\ fbq_in (ftl_free_blocks f') pbn = false
             /\ fbq_deq fbq = Some (pbn, ftl_free_blocks f'))
         /\ J_bi_block_coherent c' (ftl_bi_table f').
Proof.
  intros c bit bmt fbq HI1 HI3 HI4 HI8 HSC HJ.
  unfold alloc_block.
  simpl.
  (* step 1: count blocks = abundant *)
  assert (Hbc := I_fbq_len_greater_than_constant_implies_check_freebq_count_abundant fbq HSC).
  rewrite Hbc.
  destruct (abundant_elim fbq Hbc) as [pbn [fbq' [Hdeq Hb]]].
  rewrite Hdeq.
  assert (Hpbn: valid_block_no pbn).
    eauto.
  assert (Hbi: exists bi, bit_get bit pbn = Some bi).
    destruct (HI1 pbn); auto.
  destruct Hbi as [bi Hbi].
  rewrite Hbi.
  destruct (HI4 pbn bi Hb Hbi) as [Hbs | Hbs]; trivial.

    (* case 1-1: bi state is "bs_invalid" *)
    rewrite Hbs.
    destruct (HJ pbn bi Hbi) as [b [Hgetb Hcob]].
    rewrite Hbs in Hcob.
    destruct (nand_erase_block_spec c pbn b Hpbn Hgetb Hcob) as [c' [He He1]].
    destruct He1 as [He11 [He12 He13]].
    rewrite He.
    destruct (bit_update_spec bit pbn bi
                                {|bi_state := bs_erased;
                                  bi_used_pages := 0;
                                  bi_erase_count := S (bi_erase_count bi)
                                   |} Hbi) as [bit' [Hbit' [Hbit'get Hbit'get2]]].
    rewrite Hbit'.
    exists pbn.
    exists c'.
    eexists.
    exists {|bi_state := bs_erased; bi_used_pages := 0; bi_erase_count := S (bi_erase_count bi) |}.
    simpl.
    split.
      eauto.
    split; trivial.
    split.
      split; trivial.
    split.
      intros bi0.
      rewrite Hbi.
      intros Heq Hbs2.
      injection Heq.
      intros Hbieq.
      subst bi0.
      split; trivial.
      exists b.
      split; trivial.
    split.
      intros bi0.
      rewrite Hbi.
      intros Heq Hbs2.
      injection Heq.
      intros Hbieq.
      subst bi0.
      rewrite Hbs in Hbs2.        
      discriminate.
    simpl.
    split.
      intros pbn' Hneq. 
      destruct (chip_set_block_elim _ _ _ _ He11) as [Hvpbn' [Hg' Hg'2]]; eauto.
    split; trivial.
    split; trivial.
    split. 
      split; trivial.
      split; trivial.
      eapply allocated_pbn_not_in_fbq; eauto.
    (* preserve J_bi_block_coherent *)
    eapply J_bi_block_coherent_preserv_bit_update_chip_erase; eauto.    

    (* case 1-2: bi state is "bs_erase" *)
    rewrite Hbs.
    destruct (bit_update_spec bit pbn bi
                                {|bi_state := bs_erased;
                                  bi_used_pages := 0;
                                  bi_erase_count := bi_erase_count bi
                                   |} Hbi) as [bit' [Hbit' [Hbit'get Hbit'get2]]].
    rewrite Hbit'.
    exists pbn.
    exists c.
    exists {|
       ftl_bi_table := bit';
       ftl_bm_table := bmt;
       ftl_free_blocks := fbq' |}.
    simpl.
    exists (mk_bi bs_erased 0 (bi_erase_count bi)).
    simpl.
    split; trivial.
    split; trivial.
    split.
      split; trivial.
    split. 
      intros.
      rewrite Hbi in H.
      injection H.
      intro Hx; subst bi0.
      rewrite Hbs in H0.
      discriminate.
    split.
      intros.
      rewrite Hbi in H.
      injection H.
      intro Hx; subst bi0.
      split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    split.
      split; trivial.
      split; trivial.
      eapply allocated_pbn_not_in_fbq; eauto.
    eapply J_bi_block_coherent_preserv_erased_set_erased; eauto.
Qed.    

Lemma free_block_spec : 
  forall bit fbq pbn bi,
    valid_block_no pbn
    -> fbq_in fbq pbn = false
    -> bit_get bit pbn = Some bi
    -> exists bit' fbq', free_block bit fbq pbn = Some (bit', fbq')
                         /\ bit_update bit pbn (mk_bi bs_invalid
                                                      (bi_used_pages bi)
                                                      (bi_erase_count bi)) = Some bit'
                         /\ fbq_in fbq' pbn = true
                         /\ fbq_enq fbq pbn = Some fbq'.
Proof.
  intros bit fbq pbn bi Hpbn Hqin Hgetbi.
  unfold free_block.
  rewrite Hgetbi.
  destruct (bit_update_spec bit pbn bi
                            {|bi_state := bs_invalid;
                              bi_used_pages := bi_used_pages bi;
                              bi_erase_count := bi_erase_count bi
                            |} Hgetbi) as [bit' [Hbit' [Hbit'get Hbit'get2]]].
  rewrite Hbit'.
  destruct (fbq_enq_spec fbq pbn) as [fbq' Hfbq'].
  rewrite Hfbq'.
  exists bit', fbq'.
  split;trivial.
  split; trivial.
  split; trivial.
  eapply fbq_enq_fbq_in; eauto.
Qed.

Lemma merge_block_fix_case1_spec_aux : 
  forall i c lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log, 
    blt_nat i (S PAGES_PER_BLOCK) = true
    -> valid_block_no pbn_data
    -> valid_block_no pbn_log
    -> valid_block_no pbn_free
    -> pbn_data <> pbn_log
    -> pbn_log <> pbn_free
    -> pbn_free <> pbn_data
    -> chip_bi_coherent c pbn_log bi_log
    -> chip_bi_coherent c pbn_free bi_free
    -> chip_bi_coherent c pbn_data bi_data
    -> bi_state bi_data = bs_data lbn
    -> bi_state bi_free = bs_erased
    -> exists c' bi_free', 
         merge_block_fix c bi_log bi_free 
                         (Some pbn_data) pbn_log pbn_free 
                         i = Some (c', bi_free')
         /\ (bi_state bi_free' = bi_state bi_free 
             /\ bi_used_pages bi_free' = i
             /\ bi_erase_count bi_free' = bi_erase_count bi_free)
         /\ (exists b', chip_get_block c' pbn_free = Some b'
                        /\ (beq_nat i 0 = true -> block_coherent_erased bi_free' b')
                        /\ (beq_nat i 0 = false -> block_coherent_data_partial i b'))
         /\ (forall loc,
                   blt_nat loc i = true
                   -> (exists d, read_data_block c' pbn_free loc = Some d 
                                 /\ (read_log_block c bi_log pbn_log loc = Some d 
                                     \/ (read_log_block c bi_log pbn_log loc = None 
                                         /\ read_data_block c pbn_data loc = Some d))))
         /\ (forall pbn',
               pbn' <> pbn_free
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.

  induction i.

  (* base case *)
  intros c lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log. 
  intros Hi Hvd Hvl Hvf Hneq1 Hneq2 Hneq3 Hblbil Hbfbif Hbdbid Hbdbs Hbfbs.
  simpl.
  exists c, bi_free.
  split; trivial.
  split.
    split; trivial.
    split.
      unfold chip_bi_coherent in Hbfbif.
      rewrite Hbfbs in Hbfbif.
      destruct Hbfbif as [b [Hb Hco]].
      unfold block_coherent_erased in Hco.
      destruct Hco as [H1 [H2 [H3 [H4 H5]]]].
      rewrite H4 in H2.
      trivial.
     trivial.
  split. 
    assert (Hb : exists b, chip_get_block c pbn_free = Some b
                           /\ block_coherent_erased bi_free b).
      unfold chip_bi_coherent in Hbfbif.
      rewrite Hbfbs in Hbfbif.
      trivial.
    destruct Hb as [b [Hgetb Hcob]].
    exists b.
    split; trivial.
    split.
      intro; trivial.
    intro; discriminate.
    split; trivial.
    intros.
    simplbnat.

  (* induction case *)
  intros c lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log. 
  intros Hi Hvd Hvl Hvf Hneq1 Hneq2 Hneq3 Hblbil Hbfbif Hbdbid Hbdbs Hbfbs.
  simpl.
  assert (Hx1: blt_nat i (S PAGES_PER_BLOCK) = true).
    solvebnat.
  assert (IHix := IHi c lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log
                      Hx1 Hvd Hvl Hvf Hneq1 Hneq2 Hneq3 Hblbil Hbfbif Hbdbid Hbdbs Hbfbs).
  destruct IHix as [c' [bi_f' [Hm [Hm0 [Hm1 [Hm2 Hm3]]]]]].
  rewrite Hm.
  destruct (read_log_block c' bi_log pbn_log i) as [d | ] eqn: Hrlog.

  (* cast 1 : read some log *)
    destruct Hm1 as [b' [Hgetb' Hcob']].
    destruct (beq_nat i 0) eqn:Hieq0.
    
      (* case 1-1: write_data_block location = 0 *)
      assert (Hieq : i = 0).
        substbnat.
        trivial.
      subst i.
      assert (Hcob : block_coherent_erased bi_f' b').
        destruct Hcob'.
        apply H; trivial.
      assert (Hvloc0 : valid_page_off 0).
        simpl; trivial.
        destruct Hm0 as [Hm01 [Hm02 Hm03]].
      destruct (write_data_block_spec_write_emp c' pbn_free b' bi_f' 0 d Hgetb' Hvf Hvloc0 Hcob Hm02)
          as [c'' [bi_f'' [Hw Hwspec]]].

      exists c'', bi_f''.
      destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
      split; trivial.
      split. 
        rewrite Hws1, Hws2, Hws3.
        rewrite Hm01, Hm02, Hm03.
        split; trivial.
        split; trivial.
      split.
        destruct Hws4 as [b'' [Hgetb'' Hcob'']].
        exists b''.
        split; trivial.
        split; trivial.
        intro HF; discriminate HF.
      split.
        intros.
        destruct loc as [ | loc].
          exists d.
          split; trivial.
          left.
          rewrite <- (read_log_block_eq c c' pbn_log bi_log 0); trivial.
          apply Hm3; trivial.
        simplbnat.
      intros.
      rewrite Hws7; trivial.
      rewrite Hm3; trivial.

    (* case 1-2: write_data_block location > 0 *)
    assert (Hcob : block_coherent_data_partial i b').
      destruct Hcob'.
      apply H0; trivial.
    destruct Hm0 as [H1 [H2 H3]].
    assert (Hvi : bvalid_page_off i = true).
      unfold bvalid_page_off.
      simplbnat.
      trivial.
    destruct (write_data_block_spec_write_nonemp c' pbn_free b' bi_f' i d Hgetb' Hvf Hvi Hcob H2)
          as [c'' [bi_f'' [Hw Hwspec]]].
    exists c'', bi_f''.
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite H1, H2, H3.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
       destruct (blt_S_dec loc i H).
         destruct (Hm2 loc H0) as [d' [Hr' Hd']].
         exists d'.
         split; trivial.
         rewrite (Hws6 loc); trivial.
         apply beq_false_neq.
         apply beq_sym.
         apply blt_t_beq_f; trivial.
       assert (Hloc: loc = i).
         apply beq_true_eq; trivial.
       subst loc.
       clear H0 H.
       exists d.
       split; trivial.
       left; trivial.
       rewrite <- (read_log_block_eq c c' pbn_log bi_log i); trivial.
       apply Hm3; trivial.
     intros.
     rewrite Hws7; trivial.
     rewrite Hm3; trivial.

  (* case 2 : read none log *)
  assert (Hb : exists b, chip_get_block c' pbn_data = Some b
                         /\ block_coherent_data bi_data b).
    unfold chip_bi_coherent in Hbdbid.
    rewrite Hbdbs in Hbdbid.
    destruct Hbdbid as [b [Hgetb Hcob]].
    exists b.
    split; trivial.
    rewrite Hm3; eauto.
  destruct Hb as [b [Hgetb Hcob]].
  assert (Hvi : bvalid_page_off i = true).
    unfold bvalid_page_off.
    simplbnat.
    trivial.
  destruct (read_data_block_spec_read_full c' pbn_data b bi_data i Hvd Hvi Hgetb Hcob) as [d Hrd].
  rewrite Hrd.
  destruct (beq_nat i 0) eqn:Hieq0.

  (* case 2-1: write_data_block location = 0 *)
    assert (Hieq: i = 0).
      apply beq_true_eq; trivial.
    subst i.
    assert (Hb : exists bf, chip_get_block c' pbn_free = Some bf
                           /\ block_coherent_erased bi_f' bf).
    destruct Hm1 as [bf [Hgetbf [Hcobf1 Hcobf2]]].
    exists bf.
    split; trivial.
    apply Hcobf1; trivial.
    destruct Hb as [bf [Hgetbf Hcobf]].
    assert (Hvloc0 : bvalid_page_off 0 = true).
      simpl; trivial.
    destruct Hm0 as [Hm01 [Hm02 Hm03]].
    destruct (write_data_block_spec_write_emp _ _ _ _  0 d Hgetbf Hvf Hvloc0 Hcobf Hm02) as [c'' [bi_f'' [Hw Hwspec]]].
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    rewrite Hw.
    exists c'', bi_f''.
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite Hm01, Hm02, Hm03.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
        destruct loc as [ | loc].
          exists d.
          split; trivial.
          right.
          split. 
            rewrite <- (read_log_block_eq c c' pbn_log bi_log 0); trivial.
            apply Hm3; trivial.
          rewrite <- (read_data_block_eq c c' pbn_data 0); trivial.
          apply Hm3; auto.
        simplbnat.
      intros.
      rewrite Hws7; trivial.
      rewrite Hm3; trivial.

    (* case 2-2: write_data_block location > 0 *)
    destruct Hm1 as [bf [Hgetbf [Hcobf1 Hcobf2]]].
    assert (Hcobf : block_coherent_data_partial i bf).
      apply Hcobf2; trivial.
    destruct Hm0 as [H1 [H2 H3]].
    destruct (write_data_block_spec_write_nonemp c' pbn_free bf bi_f' i d Hgetbf Hvf Hvi Hcobf H2)
          as [c'' [bi_f'' [Hw Hwspec]]].
    rewrite Hw.
    exists c'', bi_f''.
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite H1, H2, H3.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
       destruct (blt_S_dec loc i H).
         destruct (Hm2 loc H0) as [d' [Hr' Hd']].
         exists d'.
         split; trivial.
         rewrite (Hws6 loc); trivial.
         apply beq_false_neq.
         apply beq_sym.
         apply blt_t_beq_f; trivial.
       assert (Hloc: loc = i).
         apply beq_true_eq; trivial.
       subst loc.
       clear H0 H.
       exists d.
       split; trivial.
       right; trivial.
       rewrite <- (read_log_block_eq c c' pbn_log bi_log i); auto.
       split; trivial.
       rewrite <- (read_data_block_eq c c' pbn_data i); trivial.
       apply Hm3; auto.
     intros.
     rewrite Hws7; trivial.
     rewrite Hm3; trivial.
Qed.

(* pbn_data is None *)
Lemma merge_block_fix_case2_spec_aux : 
  forall i c pbn_log pbn_free bi_free bi_log, 
    blt_nat i (S PAGES_PER_BLOCK) = true
    -> valid_block_no pbn_log
    -> valid_block_no pbn_free
    -> pbn_log <> pbn_free
    -> chip_bi_coherent c pbn_log bi_log
    -> chip_bi_coherent c pbn_free bi_free
    -> bi_state bi_free = bs_erased
    -> exists c' bi_free', 
         merge_block_fix c bi_log bi_free 
                         None pbn_log pbn_free 
                         i = Some (c', bi_free')
         /\ (bi_state bi_free' = bi_state bi_free 
             /\ bi_used_pages bi_free' = i
             /\ bi_erase_count bi_free' = bi_erase_count bi_free)
         /\ (exists b', chip_get_block c' pbn_free = Some b'
                        /\ (beq_nat i 0 = true -> block_coherent_erased bi_free' b')
                        /\ (beq_nat i 0 = false -> block_coherent_data_partial i b'))
         /\ (forall loc,
                   blt_nat loc i = true
                   -> (exists d, read_data_block c' pbn_free loc = Some d 
                                 /\ (read_log_block c bi_log pbn_log loc = Some d
                                     \/ (read_log_block c bi_log pbn_log loc = None
                                         /\ d = zero_page))))
         /\ (forall pbn',
               pbn' <> pbn_free
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.

  induction i.

  (* base case *)
  intros c pbn_log pbn_free bi_free bi_log. 
  intros Hi Hvl Hvf Hneq1 Hblbil Hbfbif Hbfbs.
  simpl.
  exists c, bi_free.
  split; trivial.
  split.
    split; trivial.
    split.
      unfold chip_bi_coherent in Hbfbif.
      rewrite Hbfbs in Hbfbif.
      destruct Hbfbif as [b [Hb Hco]].
      unfold block_coherent_erased in Hco.
      destruct Hco as [H1 [H2 [H3 [H4 H5]]]].
      rewrite H4 in H2.
      trivial.
     trivial.
  split. 
    assert (Hb : exists b, chip_get_block c pbn_free = Some b
                           /\ block_coherent_erased bi_free b).
      unfold chip_bi_coherent in Hbfbif.
      rewrite Hbfbs in Hbfbif.
      trivial.
    destruct Hb as [b [Hgetb Hcob]].
    exists b.
    split; trivial.
    split.
      intro; trivial.
    intro; discriminate.
    split; trivial.
    intros.
    simplbnat.

  (* induction case *)
  intros c pbn_log pbn_free bi_free bi_log. 
  intros Hi Hvl Hvf Hneq1 Hblbil Hbfbif Hbfbs.
  simpl.
  assert (Hx1: blt_nat i (S PAGES_PER_BLOCK) = true).
    solvebnat.
  assert (IHix := IHi c pbn_log pbn_free bi_free bi_log
                      Hx1 Hvl Hvf Hneq1 Hblbil Hbfbif Hbfbs).
  destruct IHix as [c' [bi_f' [Hm [Hm0 [Hm1 [Hm2 Hm3]]]]]].
  rewrite Hm.
  destruct (read_log_block c' bi_log pbn_log i) as [d | ] eqn: Hrlog.

  (* cast 1 : read some log *)
    destruct Hm1 as [b' [Hgetb' Hcob']].
    destruct (beq_nat i 0) eqn:Hieq0.
    
      (* case 1-1: write_data_block location = 0 *)
      assert (Hieq : i = 0).
        substbnat.
        trivial.
      subst i.
      assert (Hcob : block_coherent_erased bi_f' b').
        destruct Hcob'.
        apply H; trivial.
      assert (Hvloc0 : bvalid_page_off 0 = true).
        simpl; trivial.
      destruct Hm0 as [Hm01 [Hm02 Hm03]].
      destruct (write_data_block_spec_write_emp c' pbn_free b' bi_f' 0 d Hgetb' Hvf Hvloc0 Hcob Hm02)
          as [c'' [bi_f'' [Hw Hwspec]]].
      exists c'', bi_f''.
      destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
      split; trivial.
      split. 
        rewrite Hws1, Hws2, Hws3.
        rewrite Hm01, Hm02, Hm03.
        split; trivial.
        split; trivial.
      split.
        destruct Hws4 as [b'' [Hgetb'' Hcob'']].
        exists b''.
        split; trivial.
        split; trivial.
        intro HF; discriminate HF.
      split.
        intros.
        destruct loc as [ | loc].
          exists d.
          split; trivial.
          left.
          rewrite <- (read_log_block_eq c c' pbn_log bi_log 0); trivial.
          apply Hm3; trivial.
        simplbnat.
      intros.
      rewrite Hws7; trivial.
      rewrite Hm3; trivial.

    (* case 1-2: write_data_block location > 0 *)
    assert (Hcob : block_coherent_data_partial i b').
      destruct Hcob'.
      apply H0; trivial.
    destruct Hm0 as [H1 [H2 H3]].
    assert (Hvi : bvalid_page_off i = true).
      unfold bvalid_page_off.
      simplbnat; trivial.
    destruct (write_data_block_spec_write_nonemp c' pbn_free b' bi_f' i d Hgetb' Hvf Hvi Hcob H2)
          as [c'' [bi_f'' [Hw Hwspec]]].
    exists c'', bi_f''.
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite H1, H2, H3.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
       destruct (blt_S_dec loc i H).
         destruct (Hm2 loc H0) as [d' [Hr' Hd']].
         exists d'.
         split; trivial.
         rewrite (Hws6 loc); trivial.
         apply beq_false_neq.
         apply beq_sym.
         apply blt_t_beq_f; trivial.
       assert (Hloc: loc = i).
         apply beq_true_eq; trivial.
       subst loc.
       clear H0 H.
       exists d.
       split; trivial.
       left.
       rewrite <- (read_log_block_eq c c' pbn_log bi_log i); trivial.
       apply Hm3; trivial.
     intros.
     rewrite Hws7; trivial.
     rewrite Hm3; trivial.

  (* case 2 : read none log *)
  destruct (beq_nat i 0) eqn:Hieq0.

  (* case 2-1: write_data_block location = 0 *)
    assert (Hieq: i = 0).
      apply beq_true_eq; trivial.
    subst i.
    assert (Hb : exists bf, chip_get_block c' pbn_free = Some bf
                           /\ block_coherent_erased bi_f' bf).
    destruct Hm1 as [bf [Hgetbf [Hcobf1 Hcobf2]]].
    exists bf.
    split; trivial.
    apply Hcobf1; trivial.
    destruct Hb as [bf [Hgetbf Hcobf]].
    destruct Hm0 as [Hm01 [Hm02 Hm03]].
    assert (Hvloc0 : bvalid_page_off 0 = true).
      simpl; trivial.
    destruct (write_data_block_spec_write_emp _ _ _ _  0 zero_page Hgetbf Hvf Hvloc0 Hcobf Hm02) as [c'' [bi_f'' [Hw Hwspec]]].
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    rewrite Hw.
    exists c'', bi_f''.
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite Hm01, Hm02, Hm03.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
        destruct loc as [ | loc].
          exists zero_page.
          split; trivial.
          right.
          rewrite <- (read_log_block_eq c c' pbn_log bi_log 0); trivial.
          split; trivial.
          apply Hm3; trivial.
        simplbnat.
      intros.
      rewrite Hws7; trivial.
      rewrite Hm3; trivial.

    (* case 2-2: write_data_block location > 0 *)
    destruct Hm1 as [bf [Hgetbf [Hcobf1 Hcobf2]]].
    assert (Hcobf : block_coherent_data_partial i bf).
      apply Hcobf2; trivial.
    destruct Hm0 as [H1 [H2 H3]].
    assert (Hvi : bvalid_page_off i = true).
      unfold bvalid_page_off.
      simplbnat; trivial.
    destruct (write_data_block_spec_write_nonemp c' pbn_free bf bi_f' i zero_page Hgetbf Hvf Hvi Hcobf H2)
          as [c'' [bi_f'' [Hw Hwspec]]].
    rewrite Hw.
    exists c'', bi_f''.
    destruct Hwspec as [Hws1 [Hws2 [Hws3 [Hws4 [Hws5 [Hws6 Hws7]]]]]].
    split; trivial.
    split.
      rewrite Hws1, Hws2, Hws3.
      rewrite H1, H2, H3.
      split; trivial.
      split; trivial.
    split.
      destruct Hws4 as [b'' [Hgetb'' Hcob'']].
      exists b''.
      split; trivial.
      split.
        intro HF; discriminate HF.
      intro H; clear H.
      trivial.
     split.
       intros.
       destruct (blt_S_dec loc i H).
         destruct (Hm2 loc H0) as [d' [Hr' Hd']].
         exists d'.
         split; trivial.
         rewrite (Hws6 loc); trivial.
         apply beq_false_neq.
         apply beq_sym.
         apply blt_t_beq_f; trivial.
       assert (Hloc: loc = i).
         apply beq_true_eq; trivial.
       subst loc.
       clear H0 H.
       exists zero_page.
       split; trivial.
       right; trivial.
       split; trivial.
       rewrite <- (read_log_block_eq c c' pbn_log bi_log i); auto.
     intros.
     rewrite Hws7; trivial.
     rewrite Hm3; trivial.
Qed.

Lemma merge_block_fix_case1_spec : 
  forall c bit bmt lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log, 
    bmt_get bmt lbn = Some (Some pbn_data, Some pbn_log)
    -> valid_block_no pbn_data
    -> valid_block_no pbn_log
    -> valid_block_no pbn_free
    -> bit_get bit pbn_log = Some bi_log
    -> bit_get bit pbn_data = Some bi_data
    -> bit_get bit pbn_free = Some bi_free
    -> pbn_not_in_bmt bmt pbn_free
    -> I_pbn_bmt_used bit bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> J_bi_block_coherent c bit
    -> bi_state bi_free = bs_erased
    -> exists c' bi_free', 
         merge_block_fix c bi_log bi_free 
                         (Some pbn_data) pbn_log pbn_free 
                         PAGES_PER_BLOCK = Some (c', bi_free')
         /\ (bi_state bi_free' = bi_state bi_free 
             /\ bi_used_pages bi_free' = PAGES_PER_BLOCK
             /\ bi_erase_count bi_free' = bi_erase_count bi_free)
         /\ (exists b', chip_get_block c' pbn_free = Some b'
                        /\ block_coherent_data_partial PAGES_PER_BLOCK b')
         /\ (forall loc,
                   valid_page_off loc
                   -> (exists d, read_data_block c' pbn_free loc = Some d 
                                 /\ (read_log_block c bi_log pbn_log loc = Some d 
                                     \/ (read_log_block c bi_log pbn_log loc = None 
                                         /\ read_data_block c pbn_data loc = Some d))))
         /\ (forall pbn',
               pbn' <> pbn_free
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c bit bmt lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log.
  intros Hbmt Hvd Hvl Hvf Hbil Hbid Hbif Hbf HI5 HI7_2 HJ Hbifbs.
  assert (H1: blt_nat PAGES_PER_BLOCK (S PAGES_PER_BLOCK) = true).
    simplbnat.
    trivial.
  assert (H2: pbn_data <> pbn_log).
    eauto.
  assert (H3: pbn_log <> pbn_free).
    unfold pbn_not_in_bmt in Hbf.
    intro Heq.
    subst pbn_free.
    assert (pbn_in_bmt_lbn bmt lbn pbn_log).
      unfold pbn_in_bmt_lbn.
      right. 
      exists (Some pbn_data).
      trivial.
    apply Hbf.
    exists lbn; trivial.
  assert (H4: pbn_free <> pbn_data).
    unfold pbn_not_in_bmt in Hbf.
    intro Heq.
    subst pbn_free.
    assert (pbn_in_bmt_lbn bmt lbn pbn_data).
      unfold pbn_in_bmt_lbn.
      left. 
      exists (Some pbn_log).
      trivial.
    apply Hbf.
    exists lbn; trivial.
  assert (H5: chip_bi_coherent c pbn_log bi_log).
    apply (HJ pbn_log); trivial.
  assert (H6: chip_bi_coherent c pbn_free bi_free).
    apply (HJ pbn_free); trivial.
  assert (H7: chip_bi_coherent c pbn_data bi_data).
    apply (HJ pbn_data); trivial.
  assert (H8: bi_state bi_data = bs_data lbn).
    unfold chip_bi_coherent in H7.
    unfold I_pbn_bmt_used in HI5.
    destruct (HI5 lbn pbn_data bi_data Hbid) as [Hx1 Hx2].
    apply Hx1.
    exists (Some pbn_log).
    trivial.
  destruct (merge_block_fix_case1_spec_aux PAGES_PER_BLOCK c lbn pbn_data pbn_log pbn_free bi_data bi_free bi_log)
   as [c' [bi_f' H]]; trivial.
  destruct H as [Hm [Hm0 [Hm1 [Hm2 Hm3]]]].
  exists c', bi_f'.
  split; trivial.
  split; trivial.
  split.
    destruct Hm1 as [b' [Hb' [Hco1 Hco2]]].
    exists b'; split; trivial.
    apply Hco2; trivial.
  split; trivial.
Qed.

Lemma merge_block_fix_case2_spec : 
  forall c bit bmt lbn pbn_log pbn_free bi_free bi_log, 
    bmt_get bmt lbn = Some (None, Some pbn_log)
    -> valid_block_no pbn_log
    -> valid_block_no pbn_free
    -> bit_get bit pbn_log = Some bi_log
    -> bit_get bit pbn_free = Some bi_free
    -> pbn_not_in_bmt bmt pbn_free
    -> I_pbn_bmt_used bit bmt
    -> I_pbn_bmt_distinguishable_2 bmt
    -> J_bi_block_coherent c bit
    -> bi_state bi_free = bs_erased
    -> exists c' bi_free', 
         merge_block_fix c bi_log bi_free 
                         None pbn_log pbn_free 
                         PAGES_PER_BLOCK = Some (c', bi_free')
         /\ (bi_state bi_free' = bi_state bi_free 
             /\ bi_used_pages bi_free' = PAGES_PER_BLOCK
             /\ bi_erase_count bi_free' = bi_erase_count bi_free)
         /\ (exists b', chip_get_block c' pbn_free = Some b'
                        /\ block_coherent_data_partial PAGES_PER_BLOCK b')
         /\ (forall loc,
                   valid_page_off loc
                   -> (exists d, read_data_block c' pbn_free loc = Some d 
                                 /\ (read_log_block c bi_log pbn_log loc = Some d 
                                     \/ (read_log_block c bi_log pbn_log loc = None 
                                         /\ d = zero_page ))))
         /\ (forall pbn',
               pbn' <> pbn_free
               -> chip_get_block c' pbn' = chip_get_block c pbn').
Proof.
  intros c bit bmt lbn pbn_log pbn_free bi_free bi_log.
  intros Hbmt Hvl Hvf Hbil Hbif Hbf HI5 HI7_2 HJ Hbifbs.
  assert (H1: blt_nat PAGES_PER_BLOCK (S PAGES_PER_BLOCK) = true).
    simplbnat.
    trivial.
  assert (H3: pbn_log <> pbn_free).
    unfold pbn_not_in_bmt in Hbf.
    intro Heq.
    subst pbn_free.
    assert (pbn_in_bmt_lbn bmt lbn pbn_log).
      unfold pbn_in_bmt_lbn.
      right. 
      exists None.
      trivial.
    apply Hbf.
    exists lbn; trivial.
  assert (H5: chip_bi_coherent c pbn_log bi_log).
    apply (HJ pbn_log); trivial.
  assert (H6: chip_bi_coherent c pbn_free bi_free).
    apply (HJ pbn_free); trivial.
  destruct (merge_block_fix_case2_spec_aux PAGES_PER_BLOCK c pbn_log pbn_free bi_free bi_log)
   as [c' [bi_f' H]]; trivial.
  destruct H as [Hm [Hm0 [Hm1 [Hm2 Hm3]]]].
  exists c', bi_f'.
  split; trivial.
  split; trivial.
  split.
    destruct Hm1 as [b' [Hb' [Hco1 Hco2]]].
    exists b'; split; trivial.
    apply Hco2; trivial.
  split; trivial.
Qed.

Lemma merge_block_case1_spec :
  forall c f lbn bd bl, 
    Inv c f
    -> valid_logical_block_no lbn
    -> bmt_get (ftl_bm_table f) lbn = Some (Some bd, Some bl)
    -> exists c' f', merge_block c f lbn = Some (c', f')
                     /\ Inv c' f'
                     /\ (exists bf, 
                           bmt_get (ftl_bm_table f') lbn = Some (Some bf, None)
                           /\ (forall lbn', 
                                 lbn' <> lbn 
                                 -> bmt_get (ftl_bm_table f') lbn'= bmt_get (ftl_bm_table f) lbn'))
                     /\ 1 + length (ftl_free_blocks f) = length (ftl_free_blocks f')
                     /\ (forall lbn' loff',
                           FTL_read c' f' lbn' loff' = FTL_read c f lbn' loff').
Proof.
  intros c f lbn pbn_data pbn_log HInv Hlbn Hbmtg.
  destruct HInv as [HFI HRI].
  unfold merge_block.
  rewrite Hbmtg.
  destruct HFI as [HI1 [HI2 [HI3 [HI4 [HI5 [HI6 [HI7_1 [H7_2 [HI8 HI10]]]]]]]]].
  destruct f as [bit bmt fbq].
  simpl in * |- .
  assert (HSC: I_fbq_len_greater_than_constant fbq).
    apply (I_fbq_len_greater_than_constant_derivable bit bmt); trivial.
  destruct (alloc_block_spec c _ bmt _ HI1 HI3 HI4 HI8 HSC HRI)
    as [pbn_free [c' [f' [bi' [Halloc [Hpf [Hbif [Ha1 [Ha2 [Ha3 [Hbmt' [Hbit' [Hfbq' HJ']]]]]]]]]]]]].
  destruct Hfbq' as [Hf1 [Hf2 Hf3]].
  destruct Hbif as [Hbi1 Hbi2].
  rewrite Halloc.
  destruct f' as [bit' bmt' fbq'].
  simpl in * |- .
  assert (Hgetbi': bit_get bit' pbn_free = Some bi').
    eapply bit_update_bit_get_eq; eauto.
  unfold ftl_bi_table.
  assert (HI13: I_bmt_fbq_distinguiable bmt fbq).
    apply I_pbn_habitation_implies_I_bmt_fbq_distinguiable; trivial.
  assert (Hbd2 : pbn_in_bmt_lbn bmt lbn pbn_data).
    left.
    exists (Some pbn_log).
    trivial.
  assert (Hbl2 : pbn_in_bmt_lbn bmt lbn pbn_log).
    right.
    exists (Some pbn_data).
    trivial.
  assert (Hbd : valid_block_no pbn_data).
    apply (HI2 lbn pbn_data); trivial.
  assert (Hbl : valid_block_no pbn_log).
    apply (HI2 lbn pbn_log); trivial.
  assert (Hneq1 : pbn_data <> pbn_free).
    apply (HI13 pbn_data pbn_free lbn); auto.
  assert (Hneq2 : pbn_log <> pbn_free).
    apply (HI13 pbn_log pbn_free lbn); auto.
  assert (Hpbn_log: pbn_in_bmt_log bmt lbn pbn_log).
    exists (Some pbn_data).
    trivial.
  assert (Hpbn_data: pbn_in_bmt_data bmt lbn pbn_data).
    exists (Some pbn_log).
    trivial.
  assert (Hbil: exists bi_log, bit_get bit' pbn_log = Some bi_log).
    destruct (HI1 pbn_log) as [H1 H2].
    destruct (H1 Hbl) as [bi_log Hx].
    exists bi_log.
    rewrite (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free); auto.
  destruct Hbil as [bi_log Hbilog].
  rewrite Hbilog.
  rewrite Hgetbi'.
  assert (Hbid: exists bi_data, bit_get bit' pbn_data = Some bi_data).
    destruct (HI1 pbn_data) as [H1 H2].
    destruct (H1 Hbd) as [bi_data Hx].
    exists bi_data.
    rewrite (bit_update_bit_get_neq bit pbn_data bit' bi' pbn_free); auto.
  destruct Hbid as [bi_data Hbid'].
  subst bmt'.

  assert (Hbid : bit_get bit pbn_data = Some bi_data).
    rewrite (bit_update_bit_get_neq bit pbn_data bit' bi' pbn_free) in Hbid'; auto.
  assert (Hbil : bit_get bit pbn_log = Some bi_log).
    rewrite (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free) in Hbilog; auto.
    
  assert (HI5' : I_pbn_bmt_used bit' bmt).
    eapply (I_pbn_bmt_used_preserv_bit_update_irre bit bmt pbn_free bi' bit'); eauto.
    eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
  destruct (merge_block_fix_case1_spec c' bit' bmt lbn pbn_data pbn_log pbn_free bi_data bi' bi_log) 
    as [c'' [bi'' [Hm [Hbi'' [Hm1 [Hm2 Hm3 ]]]]]]; eauto.
    eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
  rewrite Hm.
  unfold ftl_bm_table, ftl_free_blocks, ftl_bi_table.
  
  destruct (bmt_update_spec bmt lbn _ (Some pbn_free, None) Hbmtg) as [bmt' [Hbmt' [Hbmt'1 Hbmt'2]]].
  rewrite Hbmt'.
  
  destruct (bit_update_spec bit' pbn_free bi' (bi_set_state bi'' (bs_data lbn))  Hgetbi')
    as [bit'' [Hbit'' [Hbit''1 Hbit''2]]].
  rewrite Hbit''.
  
  assert (Hplninfbq : fbq_in fbq pbn_log = false).
    eapply I_pbn_habitation_in_bmt_implies_not_in_fbq; eauto.
    exists lbn.
    right.
    exists (Some pbn_data).
    trivial.

  assert (Hpdninfbq : fbq_in fbq pbn_data = false).
    eapply I_pbn_habitation_in_bmt_implies_not_in_fbq; eauto.
    exists lbn.
    left.
    exists (Some pbn_log).
    trivial.

  destruct (free_block_spec bit'' fbq' pbn_log bi_log Hbl)
    as [bit3 [fbq3 [Hf [Hbit3 [Hfbq31 Hfbq32]]]]]; auto.
    eapply fbq_not_in_preserv_fbq_deq with (pbn':=pbn_free); eauto.
    trivial.
    rewrite (bit_update_bit_get_neq bit' pbn_log bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.

  rewrite Hf.
  destruct (free_block_spec bit3 fbq3 pbn_data bi_data Hbd)
    as [bit4 [fbq4 [Hf4 [Hbit4 [Hfbq41 Hfbq42]]]]]; auto.

      apply (fbq_not_in_preserv_fbq_enq fbq' pbn_data fbq3 pbn_log); eauto.
      eapply fbq_not_in_preserv_fbq_deq with (pbn':=pbn_free); eauto.
      trivial.
      rewrite (bit_update_bit_get_neq bit'' pbn_data bit3 
                  (mk_bi bs_invalid (bi_used_pages bi_log) (bi_erase_count bi_log)) pbn_log); eauto.
      rewrite (bit_update_bit_get_neq bit' pbn_data bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.
  rewrite Hf4.

  exists c'', (mk_FTL bit4 bmt' fbq4).
  split; trivial.
  split.
    (* to prove that Inv is preserved *)
    split.
      (* F_Inv *)
      unfold F_Inv.
      simpl.
      split. (* I1 *)
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_data bit3); eauto.
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_log bit''); eauto.
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_free bit'); eauto.
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_free bit); eauto.
      split. (* I2 *)
        apply I_pbn_bmt_valid_preserv_bmt_update_data_none with bmt lbn pbn_free; trivial.
      split. (* I3 *)
        eapply I_pbn_freebq_valid_preserv_fbq_enq with (fbq:=fbq3) (pbn:=pbn_data); eauto.
        eapply I_pbn_freebq_valid_preserv_fbq_enq with (fbq:=fbq') (pbn:=pbn_log); eauto.

        eapply I_pbn_fbq_valid_preserv_fbq_deq with (fbq:=fbq) (pbn:=pbn_free); eauto.
      split. (* I4 *)
        eapply I_pbn_freebq_state_preserv_fbq_enq with (fbq:=fbq3) (pbn:=pbn_data); eauto.
        eapply I_pbn_freebq_state_preserv_fbq_enq with (fbq:=fbq') (pbn:=pbn_log); eauto.
        eapply I_pbn_fbq_state_preserv_bit_update; eauto.
        eapply I_pbn_fbq_state_preserv_bit_update; eauto.

        eapply I_pbn_fbq_state_preserv_fbq_deq with (fbq:=fbq) (pbn:=pbn_free); eauto.
      split. (* I5 *)
        eapply  I_pbn_bmt_used_preserv_bit_update_irre; eauto.
        eapply  I_pbn_bmt_used_preserv_bit_update_irre; eauto.
        eapply I_pbn_bmt_used_preserv_bmt_update_data_none with (lbn:=lbn); eauto.
        eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
        eapply pbn_in_bmt_after_bmt_update_lbn with (lbn:=lbn) (bmr:= (Some pbn_free, None)); eauto.
        eapply pbn_in_bmt_after_bmt_update_lbn with (lbn:=lbn) (bmr:= (Some pbn_free, None)); eauto.
      split. (* I6 *)
        apply (I_pbn_habitation_alloc_merge bmt fbq lbn pbn_free pbn_data pbn_log bmt' fbq' fbq3 fbq4); eauto.
      split. (* I7_1 *)
        eapply (I_pbn_bmt_distinguishable_preserv_bmt_update_data_none bmt lbn pbn_free); eauto.
        eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
      split. (* I7_2 *)
        apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_data_none bmt lbn pbn_free _); eauto.
      split. (* I8 *)
        apply (I_pbn_fbq_distinguishable_preserv_fbq_enq fbq3 pbn_data fbq4); trivial.
        apply (I_pbn_fbq_distinguishable_preserv_fbq_enq fbq' pbn_log fbq3); trivial.
        apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq pbn_free fbq'); trivial.
        apply (fbq_not_in_preserv_fbq_deq fbq pbn_log fbq' pbn_free); trivial.
        apply (fbq_not_in_preserv_fbq_enq fbq' pbn_data fbq3 pbn_log); eauto.
        apply (fbq_not_in_preserv_fbq_deq fbq pbn_data fbq' pbn_free); eauto.
      (* I10 *)
      eapply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update _ lbn _); eauto.
    (* R_Inv *)
    unfold R_Inv.
    simpl.
    apply (J_bi_block_coherent_preserv_used_set_invalid bit3 c'' pbn_data bi_data bit4); eauto.
    apply (J_bi_block_coherent_preserv_used_set_invalid bit'' c'' pbn_log bi_log bit3); eauto.
    apply (J_bi_block_coherent_preserv_bit_update_merge c' bit' pbn_free bi' c'' bit'' lbn); auto.
    assert ((bi_set_state bi'' (bs_data lbn)) = mk_bi (bs_data lbn) PAGES_PER_BLOCK (bi_erase_count bi')).
      unfold bi_set_state.
      destruct Hbi'' as [Hbi''1 [Hbi''2 Hbi''3]].
      rewrite Hbi''3.
      rewrite Hbi''2.
      trivial.
    rewrite <- H; clear H.
    trivial.
    rewrite (bit_update_bit_get_neq bit' pbn_log bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.
    apply (I_pbn_bmt_used_implies_pbn_is_used bit bmt pbn_log lbn bi_log HI5 Hbil Hbl2).
    rewrite (bit_update_bit_get_neq bit'' pbn_data bit3 
                      (mk_bi bs_invalid (bi_used_pages bi_log) (bi_erase_count bi_log)) pbn_log); eauto.
    rewrite (bit_update_bit_get_neq bit' pbn_data bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.
    apply (I_pbn_bmt_used_implies_pbn_is_used bit bmt pbn_data lbn bi_data HI5 Hbid Hbd2).
  split.
    exists pbn_free.
    split; trivial.
  split.
    rewrite (fbq_enq_fbq_length_addone fbq3 pbn_data fbq4); eauto.
    rewrite (fbq_enq_fbq_length_addone fbq' pbn_log fbq3); eauto.
    rewrite (fbq_deq_fbq_length_subone fbq pbn_free fbq'); auto.

  (** KEY! : to prove that MERGE doesn't change the logical view *)
  intros.
  unfold FTL_read.
  simpl.
  assert (Hlbn_dec: lbn = lbn' \/ lbn <> lbn').
    destruct (nat_eq_dec lbn lbn'); auto.
  destruct Hlbn_dec as [Hlbneq | Hlbnneq].
    (* 1st case: lbn == lbn' *)
    simpl.
    subst lbn'.
    rewrite (bmt_update_bmt_get_eq bmt lbn (Some pbn_free, None) bmt'); trivial.
    rewrite Hbmtg.
    erewrite <- (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free); eauto.
    rewrite Hbilog.
    destruct (bvalid_page_off loff') eqn: Hboff'; trivial.
    assert (Hcc': chip_get_block c' pbn_log = chip_get_block c pbn_log).
      apply Ha3; eauto.
    assert (Hcc'2: chip_get_block c' pbn_data = chip_get_block c pbn_data).
      apply Ha3; eauto.
    assert (Hoff': valid_page_off loff').
      unfold valid_page_off; trivial.
    destruct (Hm2 loff' Hoff') as [d [Hd1 Hd2]].
    rewrite Hd1.
    destruct Hd2 as [Hd2 | [Hd2 Hd3]].
      rewrite (read_log_block_eq c c' pbn_log bi_log loff' Hcc') in Hd2.
      rewrite Hd2; trivial.
      rewrite (read_log_block_eq c c' pbn_log bi_log loff' Hcc') in Hd2.
      rewrite Hd2; trivial.
      rewrite (read_data_block_eq c c' pbn_data loff' Hcc'2) in Hd3.
      rewrite Hd3; trivial.
  (* 2nd case: lbn <> lbn' *)
  destruct (bvalid_page_off loff') eqn: Hboff'; trivial.
  assert (Hoff': valid_page_off loff').
    unfold valid_page_off; trivial.
  assert (Hbmtbmt' : bmt_get bmt' lbn' = bmt_get bmt lbn').
    eapply (bmt_update_bmt_get_neq bmt lbn _ bmt'); eauto.
  rewrite Hbmtbmt'.
  destruct (bmt_get bmt lbn') as [bmr | ] eqn:Hbmtlbn'; trivial.
  destruct bmr as [bmr1 bmr2]; destruct bmr1 as [bd | ]; destruct bmr2 as [bl|].
  (* 2nd case: lbn <> lbn',  subcase 1 *)
  assert (Hblin: pbn_in_bmt_lbn bmt lbn' bl).
    right. exists (Some bd). trivial.
  assert (Hbdin: pbn_in_bmt_lbn bmt lbn' bd).
    left. exists (Some bl). trivial.
  assert (Hpbnlin: pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists (Some pbn_data). trivial.
  assert (Hpbndin: pbn_in_bmt_lbn bmt lbn pbn_data).
    left. exists (Some pbn_log). trivial.
  assert (Hx1: bl <> pbn_data).
    assert (H:= HI7_1 lbn lbn' pbn_data bl); eauto.
  assert (Hx2: bl <> pbn_log).
    assert (H:= HI7_1 lbn lbn' pbn_log bl); eauto.
  assert (Hx3: bl <> pbn_free).
    apply (HI13 bl pbn_free lbn'); eauto.
  assert (Heq : bit_get bit4 bl = bit_get bit bl).
    rewrite (bit_update_bit_get_neq bit3 bl bit4 (mk_bi bs_invalid (bi_used_pages bi_data)(bi_erase_count bi_data)) pbn_data); auto.
    rewrite (bit_update_bit_get_neq bit'' bl (bit3) (mk_bi bs_invalid (bi_used_pages bi_log)(bi_erase_count bi_log)) pbn_log); auto.
    rewrite (bit_update_bit_get_neq bit' bl (bit'') (bi_set_state bi'' (bs_data lbn)) pbn_free); auto.
    rewrite (bit_update_bit_get_neq bit bl bit' bi' pbn_free); auto.
  rewrite Heq.  clear Heq.
  assert (Hx4: bd <> pbn_free).
    apply (HI13 bd pbn_free lbn'); eauto.
  assert (Hcc'': chip_get_block c'' bl = chip_get_block c bl).
    rewrite (Hm3 bl); auto.
  assert (Hcc''2: chip_get_block c'' bd = chip_get_block c bd).
    erewrite (Hm3 bd); auto.
  destruct (bit_get bit bl) as [bil | ] eqn:Hbil_; trivial.
  rewrite (read_log_block_eq _ _ _ _ _ Hcc'').
  rewrite (read_data_block_eq c c'' bd loff' Hcc''2).
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 2 *)
  assert (Hbdin: pbn_in_bmt_lbn bmt lbn' bd).
    left. exists (None). trivial.
  assert (Hx4: bd <> pbn_free).
    apply (HI13 bd pbn_free lbn'); eauto.
  assert (Hcc''2: chip_get_block c'' bd = chip_get_block c bd).
    rewrite (Hm3 bd); eauto.
  rewrite (read_data_block_eq c c'' bd loff' Hcc''2).
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 3 *)
  assert (Hblin: pbn_in_bmt_lbn bmt lbn' bl).
    right. exists None. trivial.
  assert (Hx3: bl <> pbn_free).
    apply (HI13 bl pbn_free lbn'); eauto.
  assert (Hcc'': chip_get_block c'' bl = chip_get_block c bl).
    rewrite (Hm3 bl); eauto.
  assert (Hpbnlin: pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists (Some pbn_data). trivial.
  assert (Hpbndin: pbn_in_bmt_lbn bmt lbn pbn_data).
    left. exists (Some pbn_log). trivial.
  assert (Hx1: bl <> pbn_data).
    assert (H:= HI7_1 lbn lbn' pbn_data bl); eauto.
  assert (Hx2: bl <> pbn_log).
    assert (H:= HI7_1 lbn lbn' pbn_log bl); eauto.
  assert (Heq : bit_get bit4 bl = bit_get bit bl).
    rewrite (bit_update_bit_get_neq bit3 bl bit4 _ pbn_data Hbit4); eauto.
    rewrite (bit_update_bit_get_neq bit'' bl bit3 _ pbn_log Hbit3); eauto.
    rewrite (bit_update_bit_get_neq bit' bl bit'' _ pbn_free Hbit''); eauto.
    rewrite (bit_update_bit_get_neq bit bl bit' _ pbn_free Hbit'); eauto.
  trivial.
  rewrite Heq.
  destruct (bit_get bit bl) as [bi_bl | ] eqn:Hblbi; trivial.
  rewrite (read_log_block_eq _ _ _ _ _ Hcc'').
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 4 *)
  trivial.
Qed.

Lemma merge_block_case2_spec :
  forall c f lbn bl, 
    Inv c f
    -> valid_logical_block_no lbn
    -> bmt_get (ftl_bm_table f) lbn = Some (None, Some bl)
    -> exists c' f', merge_block c f lbn = Some (c', f')
                     /\ Inv c' f'
                     /\ (exists bf, 
                           bmt_get (ftl_bm_table f') lbn = Some (Some bf, None)
                           /\ (forall lbn', 
                                 lbn' <> lbn 
                                 -> bmt_get (ftl_bm_table f') lbn'= bmt_get (ftl_bm_table f) lbn'))
                     /\ length (ftl_free_blocks f) = length (ftl_free_blocks f')
                     /\ (forall lbn' loff',
                           FTL_read c' f' lbn' loff' = FTL_read c f lbn' loff').
Proof.
  intros c f lbn pbn_log HInv Hlbn Hbmtg.
  destruct HInv as [HFI HRI].
  unfold merge_block.
  rewrite Hbmtg.
  destruct HFI as [HI1 [HI2 [HI3 [HI4 [HI5 [HI6 [HI7_1 [H7_2 [HI8 HI10]]]]]]]]].
  destruct f as [bit bmt fbq].
  simpl in * |- .
  assert (HSC: I_fbq_len_greater_than_constant fbq).
    apply (I_fbq_len_greater_than_constant_derivable bit bmt); trivial.
  destruct (alloc_block_spec c _ bmt _ HI1 HI3 HI4 HI8 HSC HRI)
    as [pbn_free [c' [f' [bi' [Halloc [Hpf [Hbif [Ha1 [Ha2 [Ha3 [Hbmt' [Hbit' [Hfbq' HJ']]]]]]]]]]]]].
  destruct Hfbq' as [Hf1 [Hf2 Hf3]].
  destruct Hbif as [Hbi1 Hbi2].
  rewrite Halloc.
  destruct f' as [bit' bmt' fbq'].
  simpl in * |- .
  assert (HI13: I_bmt_fbq_distinguiable bmt fbq).
    apply I_pbn_habitation_implies_I_bmt_fbq_distinguiable; trivial.
  assert (Hbl2 : pbn_in_bmt_lbn bmt lbn pbn_log).
    right.
    exists None.
    trivial.
  assert (Hbl : valid_block_no pbn_log).
    apply (HI2 lbn pbn_log); trivial.
  assert (Hneq2 : pbn_log <> pbn_free).
    apply (HI13 pbn_log pbn_free lbn); auto.
  assert (Hpbn_log: pbn_in_bmt_log bmt lbn pbn_log).
    exists None.
    trivial.
  assert (Hbil: exists bi_log, bit_get bit' pbn_log = Some bi_log).
    destruct (HI1 pbn_log) as [H1 H2].
    destruct (H1 Hbl) as [bi_log Hx].
    exists bi_log.
    rewrite (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free); auto.
  destruct Hbil as [bi_log Hbilog].
  assert (Hbil : bit_get bit pbn_log = Some bi_log).
    rewrite (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free) in Hbilog; auto.
    
  assert (Hgetbi': bit_get bit' pbn_free = Some bi').
    eapply bit_update_bit_get_eq; eauto.
  unfold ftl_bi_table.
  rewrite Hbilog.
  rewrite Hgetbi'.
  subst bmt'.

  assert (HI5' : I_pbn_bmt_used bit' bmt).
    eapply (I_pbn_bmt_used_preserv_bit_update_irre bit bmt pbn_free bi' bit'); eauto.
    eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
  destruct (merge_block_fix_case2_spec c' bit' bmt lbn pbn_log pbn_free bi' bi_log) 
    as [c'' [bi'' [Hm [Hbi'' [Hm1 [Hm2 Hm3 ]]]]]]; eauto.
    eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
  rewrite Hm.
  unfold ftl_bm_table, ftl_free_blocks, ftl_bi_table.
  
  destruct (bmt_update_spec bmt lbn _ (Some pbn_free, None) Hbmtg) as [bmt' [Hbmt' [Hbmt'1 Hbmt'2]]].
  rewrite Hbmt'.
  
  destruct (bit_update_spec bit' pbn_free bi' (bi_set_state bi'' (bs_data lbn)) Hgetbi')
    as [bit'' [Hbit'' [Hbit''1 Hbit''2]]].
  rewrite Hbit''.
  
  assert (Hplninfbq : fbq_in fbq pbn_log = false).
    eapply I_pbn_habitation_in_bmt_implies_not_in_fbq; eauto.
    exists lbn.
    right.
    exists None.
    trivial.

  destruct (free_block_spec bit'' fbq' pbn_log bi_log Hbl)
    as [bit3 [fbq3 [Hf [Hbit3 [Hfbq31 Hfbq32]]]]]; auto.
    eapply fbq_not_in_preserv_fbq_deq with (pbn':=pbn_free); eauto.
    trivial.
    rewrite (bit_update_bit_get_neq bit' pbn_log bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.

  rewrite Hf.
  exists c'', (mk_FTL bit3 bmt' fbq3).
  split; trivial.
  split.
    (* to prove that Inv is preserved *)
    split.
      (* F_Inv *)
      unfold F_Inv.
      simpl.
      split. (* I1 *)
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_log bit''); eauto.
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_free bit'); eauto.
        eapply (I_pbn_bit_valid_preserv_bit_update pbn_free bit); eauto.
      split. (* I2 *)
        apply I_pbn_bmt_valid_preserv_bmt_update_data_none with bmt lbn pbn_free; trivial.
      split. (* I3 *)
        eapply I_pbn_freebq_valid_preserv_fbq_enq with (fbq:=fbq') (pbn:=pbn_log); eauto.
        eapply I_pbn_fbq_valid_preserv_fbq_deq with (fbq:=fbq) (pbn:=pbn_free); eauto.
      split. (* I4 *)
        eapply I_pbn_freebq_state_preserv_fbq_enq with (fbq:=fbq') (pbn:=pbn_log); eauto.
        eapply I_pbn_fbq_state_preserv_bit_update; eauto.
        eapply I_pbn_fbq_state_preserv_bit_update; eauto.
        eapply I_pbn_fbq_state_preserv_fbq_deq with (fbq:=fbq) (pbn:=pbn_free); eauto.
      split. (* I5 *)
        eapply  I_pbn_bmt_used_preserv_bit_update_irre; eauto.
        eapply I_pbn_bmt_used_preserv_bmt_update_data_none with (bit:=bit')(lbn:=lbn) (bit':=bit'') (bi:=(bi_set_state bi'' (bs_data lbn))); eauto.
        eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
        eapply pbn_in_bmt_after_bmt_update_lbn with (lbn:=lbn) (bmr:= (Some pbn_free, None)); eauto.
      split. (* I6 *)
        apply (I_pbn_habitation_alloc_merge_2 bmt fbq lbn pbn_free pbn_log bmt' fbq' fbq3); eauto.
      split. (* I7_1 *)
        eapply (I_pbn_bmt_distinguishable_preserv_bmt_update_data_none bmt lbn pbn_free); eauto.
        eapply I_pbn_habitation_in_fbq_implies_not_in_bmt; eauto.
      split. (* I7_2 *)
        apply (I_pbn_bmt_distinguishable_2_preserv_bmt_update_data_none bmt lbn pbn_free _); eauto.
      split. (* I8 *)
        apply (I_pbn_fbq_distinguishable_preserv_fbq_enq fbq' pbn_log fbq3); trivial.
        apply (I_pbn_fbq_distinguishable_preserv_fbq_deq fbq pbn_free fbq'); trivial.
        apply (fbq_not_in_preserv_fbq_deq fbq pbn_log fbq' pbn_free); trivial.
      (* I10 *)
      eapply (I_valid_lbn_has_entry_in_bmt_preserv_bmt_update _ lbn _); eauto.
    (* R_Inv *)
    unfold R_Inv.
    simpl.
    apply (J_bi_block_coherent_preserv_used_set_invalid bit'' c'' pbn_log bi_log bit3); eauto.
    apply (J_bi_block_coherent_preserv_bit_update_merge c' bit' pbn_free bi' c'' bit'' lbn); auto.
    assert ((bi_set_state bi'' (bs_data lbn)) = mk_bi (bs_data lbn) PAGES_PER_BLOCK (bi_erase_count bi')).
      unfold bi_set_state.
      destruct Hbi'' as [Hbi''1 [Hbi''2 Hbi''3]].
      rewrite Hbi''3.
      rewrite Hbi''2.
      trivial.
    rewrite <- H; clear H.
    trivial.
    rewrite (bit_update_bit_get_neq bit' pbn_log bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free); eauto.
    apply (I_pbn_bmt_used_implies_pbn_is_used bit bmt pbn_log lbn bi_log HI5 Hbil Hbl2).
  split.
    exists pbn_free.
    split; trivial.
  split.
    rewrite (fbq_enq_fbq_length_addone fbq' pbn_log fbq3); eauto.
    rewrite (fbq_deq_fbq_length_subone fbq pbn_free fbq'); auto.

  (** KEY! : to prove that MERGE doesn't change the logical view *)
  intros.
  unfold FTL_read.
  simpl.
  assert (Hlbn_dec: lbn = lbn' \/ lbn <> lbn').
    destruct (nat_eq_dec lbn lbn'); auto.
  destruct Hlbn_dec as [Hlbneq | Hlbnneq].
    (* 1st case: lbn == lbn' *)
    simpl.
    subst lbn'.
    rewrite (bmt_update_bmt_get_eq bmt lbn (Some pbn_free, None) bmt'); trivial.
    rewrite Hbmtg.
    erewrite <- (bit_update_bit_get_neq bit pbn_log bit' bi' pbn_free); eauto.
    rewrite Hbilog.
    destruct (bvalid_page_off loff') eqn:Hboff'; trivial.
    assert (Hoff': valid_page_off loff').
      unfold valid_page_off; trivial.
    assert (Hcc': chip_get_block c' pbn_log = chip_get_block c pbn_log).
      apply Ha3; eauto.
    destruct (Hm2 loff' Hoff') as [d [Hd1 Hd2]].
    rewrite Hd1.
    destruct Hd2 as [Hd2 | [Hd2 Hd3]].
      rewrite (read_log_block_eq c c' pbn_log bi_log loff' Hcc') in Hd2.
      rewrite Hd2; trivial.
      rewrite (read_log_block_eq c c' pbn_log bi_log loff' Hcc') in Hd2.
      rewrite Hd2; trivial.
      rewrite Hd3; trivial.

  (* 2nd case: lbn <> lbn' *)
  assert (Hbmtbmt' : bmt_get bmt' lbn' = bmt_get bmt lbn').
    eapply (bmt_update_bmt_get_neq bmt lbn _ bmt'); eauto.
  rewrite Hbmtbmt'.
  destruct (bmt_get bmt lbn') as [bmr | ] eqn:Hbmtlbn'; trivial.
  destruct bmr as [bmr1 bmr2]; destruct bmr1 as [bd | ]; destruct bmr2 as [bl|].
  (* 2nd case: lbn <> lbn',  subcase 1 *)
  assert (Hblin: pbn_in_bmt_lbn bmt lbn' bl).
    right. exists (Some bd). trivial.
  assert (Hbdin: pbn_in_bmt_lbn bmt lbn' bd).
    left. exists (Some bl). trivial.
  assert (Hpbnlin: pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists None. trivial.
  assert (Hx2: bl <> pbn_log).
    assert (H:= HI7_1 lbn lbn' pbn_log bl); eauto.
  destruct (bvalid_page_off loff') eqn:Hboff'; trivial.
  assert (Hoff': valid_page_off loff').
    unfold valid_page_off; trivial.
  assert (Hx3: bl <> pbn_free).
    apply (HI13 bl pbn_free lbn'); eauto.
  assert (Heq : bit_get bit3 bl = bit_get bit bl).
    rewrite (bit_update_bit_get_neq bit'' _ (bit3) (mk_bi bs_invalid (bi_used_pages bi_log)(bi_erase_count bi_log)) pbn_log); auto.
    rewrite (bit_update_bit_get_neq bit' _ (bit'') (bi_set_state bi'' (bs_data lbn)) pbn_free); auto.
    rewrite (bit_update_bit_get_neq bit _ bit' bi' pbn_free); auto.
  rewrite Heq.  clear Heq.
  assert (Hx4: bd <> pbn_free).
    apply (HI13 bd pbn_free lbn'); eauto.
  assert (Hcc'': chip_get_block c'' bl = chip_get_block c bl).
    rewrite (Hm3 bl); auto.
  assert (Hcc''2: chip_get_block c'' bd = chip_get_block c bd).
    erewrite (Hm3 bd); auto.
  destruct (bit_get bit bl) as [bil | ] eqn:Hbil_; trivial.
  rewrite (read_log_block_eq _ _ _ _ _ Hcc'').
  rewrite (read_data_block_eq c c'' bd loff' Hcc''2).
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 2 *)
  assert (Hbdin: pbn_in_bmt_lbn bmt lbn' bd).
    left. exists (None). trivial.
  assert (Hx4: bd <> pbn_free).
    apply (HI13 bd pbn_free lbn'); eauto.
  assert (Hcc''2: chip_get_block c'' bd = chip_get_block c bd).
    rewrite (Hm3 bd); eauto.
  rewrite (read_data_block_eq c c'' bd loff' Hcc''2).
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 3 *)
  assert (Hblin: pbn_in_bmt_lbn bmt lbn' bl).
    right. exists None. trivial.
  assert (Hx3: bl <> pbn_free).
    apply (HI13 bl pbn_free lbn'); eauto.
  assert (Hcc'': chip_get_block c'' bl = chip_get_block c bl).
    rewrite (Hm3 bl); eauto.
  assert (Hpbnlin: pbn_in_bmt_lbn bmt lbn pbn_log).
    right. exists None. trivial.
  assert (Hx2: bl <> pbn_log).
    assert (H:= HI7_1 lbn lbn' pbn_log bl); eauto.
  destruct (bvalid_page_off loff') eqn:Hboff'; trivial.
  assert (Hoff': valid_page_off loff').
    unfold valid_page_off; trivial.
  assert (Heq : bit_get bit3 bl = bit_get bit bl).
    rewrite (bit_update_bit_get_neq bit'' bl bit3 (mk_bi bs_invalid (bi_used_pages bi_log)(bi_erase_count bi_log)) pbn_log Hbit3); auto.
    rewrite (bit_update_bit_get_neq bit' bl bit'' (bi_set_state bi'' (bs_data lbn)) pbn_free Hbit''); auto.
    rewrite (bit_update_bit_get_neq bit bl bit' bi' pbn_free Hbit'); auto.
  trivial.
  rewrite Heq.
  destruct (bit_get bit bl) as [bi_bl | ] eqn:Hblbi; trivial.
  rewrite (read_log_block_eq _ _ _ _ _ Hcc'').
  trivial.
  (* 2nd case: lbn <> lbn',  subcase 4 *)
  trivial.
Qed.
