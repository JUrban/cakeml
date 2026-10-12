(*****************************************************************************
 * One genuine case-10173 cell for the first complete fast-path gate.
 *
 * Box, center, historical roots, and historical reciprocals are decoded
 * from the authenticated cell-0 payloads.  The six coordinate-root records
 * are mechanically prepared from the same exact source box.  None of the
 * expected historical jets or the expected final bound is present here.
 *****************************************************************************)
Theory compute_boundedCase10173HistoricalCell0Data
Ancestors
  compute_boundedCase10173HistoricalCell
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_cell0_positive_interval_def:
  bounded_case10173_cell0_positive_interval lower upper =
    BoundedInterval64 (BoundedSigned64 F lower) (BoundedSigned64 F upper)
End

Definition bounded_case10173_cell0_center_environment_def:
  bounded_case10173_cell0_center_environment =
    [bounded_case10173_cell0_positive_interval
       5280225921755w 5280225921756w;
     bounded_case10173_cell0_positive_interval
       4449751045401w 4449751045402w;
     bounded_case10173_cell0_positive_interval
       4449751045401w 4449751045402w;
     bounded_case10173_cell0_positive_interval
       4434553733120w 4434553733121w;
     bounded_case10173_cell0_positive_interval
       4434553733120w 4434553733121w;
     bounded_case10173_cell0_positive_interval
       4471060955136w 4471060955137w]
End

Definition bounded_case10173_cell0_box_environment_def:
  bounded_case10173_cell0_box_environment =
    [bounded_case10173_cell0_positive_interval
       5225319059842w 5335132783669w;
     bounded_case10173_cell0_positive_interval
       4398046511104w 4501455579699w;
     bounded_case10173_cell0_positive_interval
       4398046511104w 4501455579699w;
     bounded_case10173_cell0_positive_interval
       4398046511104w 4471060955138w;
     bounded_case10173_cell0_positive_interval
       4398046511104w 4471060955138w;
     bounded_case10173_cell0_positive_interval
       4398046511104w 4544075399170w]
End

Definition bounded_case10173_cell0_radii_def:
  bounded_case10173_cell0_radii : word64 list =
    [54906861913w;51704534298w;51704534298w;
     36507222017w;36507222017w;73014444033w]
End

Definition bounded_case10173_cell0_sqrt_certificates_def:
  bounded_case10173_cell0_sqrt_certificates =
    [BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2409469781108w 2409524756690w)
       (bounded_case10173_cell0_positive_interval
          2396930950505w 2421996517084w)
       (bounded_case10173_cell0_positive_interval
          250863954864w 250869678694w)
       (bounded_case10173_cell0_positive_interval
          249572163107w 252182028724w)
       (bounded_case10173_cell0_positive_interval
          25717025839w 26532071030w);
     BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2211887541596w 2211942517179w)
       (bounded_case10173_cell0_positive_interval
          2199018857505w 2224729837410w)
       (bounded_case10173_cell0_positive_interval
          273272431409w 273279223487w)
       (bounded_case10173_cell0_positive_interval
          271701713908w 274878456701w)
       (bounded_case10173_cell0_positive_interval
          33182510461w 34359807088w);
     BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2211887541596w 2211942517179w)
       (bounded_case10173_cell0_positive_interval
          2199018857505w 2224729837410w)
       (bounded_case10173_cell0_positive_interval
          273272431409w 273279223487w)
       (bounded_case10173_cell0_positive_interval
          271701713908w 274878456701w)
       (bounded_case10173_cell0_positive_interval
          33182510461w 34359807088w);
     BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2208105221597w 2208160197179w)
       (bounded_case10173_cell0_positive_interval
          2199018857505w 2217206978853w)
       (bounded_case10173_cell0_positive_interval
          273740515103w 273747330470w)
       (bounded_case10173_cell0_positive_interval
          272623582539w 274878456701w)
       (bounded_case10173_cell0_positive_interval
          33521439543w 34359807088w);
     BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2208105221597w 2208160197179w)
       (bounded_case10173_cell0_positive_interval
          2199018857505w 2217206978853w)
       (bounded_case10173_cell0_positive_interval
          273740515103w 273747330470w)
       (bounded_case10173_cell0_positive_interval
          272623582539w 274878456701w)
       (bounded_case10173_cell0_positive_interval
          33521439543w 34359807088w);
     BoundedCase10173Sqrt64Certificate
       (bounded_case10173_cell0_positive_interval
          2217176192526w 2217231168108w)
       (bounded_case10173_cell0_positive_interval
          2199018857505w 2235236770525w)
       (bounded_case10173_cell0_positive_interval
          272620608307w 272627368022w)
       (bounded_case10173_cell0_positive_interval
          270424555366w 274878456701w)
       (bounded_case10173_cell0_positive_interval
          32716770403w 34359807088w)]
End

Definition bounded_case10173_cell0_center_root_delta_def:
  bounded_case10173_cell0_center_root_delta =
    bounded_case10173_cell0_positive_interval
      13125911072900w 13125911072933w
End

Definition bounded_case10173_cell0_center_root_four_x0_def:
  bounded_case10173_cell0_center_root_four_x0 =
    bounded_case10173_cell0_positive_interval
      4818991512029w 4818991512031w
End

Definition bounded_case10173_cell0_center_reciprocals_def:
  bounded_case10173_cell0_center_reciprocals =
    [bounded_case10173_cell0_positive_interval 46051120295w 46051120296w;
     bounded_case10173_cell0_positive_interval 250866974261w 250866974262w;
     bounded_case10173_cell0_positive_interval 367412905w 367412906w;
     bounded_case10173_cell0_positive_interval 46051120295w 46051120296w;
     bounded_case10173_cell0_positive_interval 21014248359w 21014248360w]
End

Definition bounded_case10173_cell0_box_root_delta_def:
  bounded_case10173_cell0_box_root_delta =
    bounded_case10173_cell0_positive_interval
      12905755228498w 13346838920096w
End

Definition bounded_case10173_cell0_box_root_four_x0_def:
  bounded_case10173_cell0_box_root_four_x0 =
    bounded_case10173_cell0_positive_interval
      4793870697103w 4843982052557w
End

Definition bounded_case10173_cell0_box_reciprocals_def:
  bounded_case10173_cell0_box_reciprocals =
    [bounded_case10173_cell0_positive_interval 45288844304w 46836694104w;
     bounded_case10173_cell0_positive_interval 3730891727w 3990273244w;
     bounded_case10173_cell0_positive_interval 249572728903w 252181566004w;
     bounded_case10173_cell0_positive_interval 113298568998w 115679617433w;
     bounded_case10173_cell0_positive_interval 350996245w 384816891w;
     bounded_case10173_cell0_positive_interval 45288844304w 46836694104w;
     bounded_case10173_cell0_positive_interval 20559783409w 21484722066w;
     bounded_case10173_cell0_positive_interval 19532315898w 20569653515w;
     bounded_case10173_cell0_positive_interval 19758253732w 20569653515w]
End

Definition bounded_case10173_cell0_check_def:
  bounded_case10173_cell0_check (_:unit) ⇔
    bounded_case10173_checked_cell_accepts
      bounded_case10173_cell0_radii
      bounded_case10173_cell0_center_environment
      bounded_case10173_cell0_box_environment
      bounded_case10173_cell0_sqrt_certificates
      bounded_case10173_cell0_center_root_delta
      bounded_case10173_cell0_center_root_four_x0
      bounded_case10173_cell0_center_reciprocals
      bounded_case10173_cell0_box_root_delta
      bounded_case10173_cell0_box_root_four_x0
      bounded_case10173_cell0_box_reciprocals
End

Definition bounded_case10173_cell0_accepts_def:
  bounded_case10173_cell0_accepts ⇔
    bounded_case10173_cell0_check ()
End

Theorem bounded_case10173_cell0_accepts_value:
  bounded_case10173_cell0_accepts
Proof
  rw [bounded_case10173_cell0_accepts_def,
      bounded_case10173_cell0_check_def]
  >> EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_cell0_check_value:
  bounded_case10173_cell0_check ()
Proof
  metis_tac [bounded_case10173_cell0_accepts_def,
             bounded_case10173_cell0_accepts_value]
QED

Definition bounded_case10173_cell0_repeat_def:
  bounded_case10173_cell0_repeat 0 = T ∧
  bounded_case10173_cell0_repeat (SUC n) =
    (bounded_case10173_cell0_check () ∧
     bounded_case10173_cell0_repeat n)
End

Theorem bounded_case10173_cell0_repeat_value:
  ∀n. bounded_case10173_cell0_repeat n
Proof
  Induct >> simp [bounded_case10173_cell0_repeat_def,
                  bounded_case10173_cell0_check_value]
QED

val _ = export_theory ();
