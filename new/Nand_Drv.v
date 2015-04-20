
Definition nand_read_page (c: chip) (pbn: block_no) (off: page_off) : result (prod data_chunk oob_chunk) :=
  test (bvalid_block_no pbn);
  do b <-- list_get (chip_blocks c) pbn;
  test (bvalid_page_off off);
  do pg <-- list_get (block_pages b) off;
  ret (page_data pg, page_oob pg).

Definition nand_write_page (c: chip) (pbn: block_no) (off: page_off) (d: data_chunk) (o: oob_chunk): result chip :=
  raise c if (beq_nat 0 (chip_power_gauge c));
  do b <-- chip_get_block c pbn;
  test (bvalid_page_off off);
  test (ble_nat (next_page b) off);
  do p <-- list_get (block_pages b) off;
  test (b_page_state_is_free (page_state p));
  do b' <-- block_set_page b off (mkpage d o ps_programmed);
  do c' <-- chip_set_block c pbn b';
  ret (consume_power_by_one c').
                 
Definition nand_erase_block (c: chip) (pbn: block_no) : result chip :=
  raise c if (beq_nat 0 (chip_power_gauge c));
  test (bvalid_block_no pbn);
  do b <-- chip_get_block c pbn;
  let b' := erased_block (S (block_erase_count b)) in 
  do c' <-- chip_set_block c pbn b';
  ret (consume_power_by_one c').
