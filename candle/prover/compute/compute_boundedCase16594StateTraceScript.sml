(*****************************************************************************
 * Development-only first-cell state-trace discriminator for case16594.
 *
 * The expected hashes were generated from the independent native fixed-scale
 * evaluator with the authenticated 167-instruction program and the first
 * genuine certificate cell.  This diagnostic stops at the first differing
 * complete stack state; it is not release evidence and is not part of the
 * checker soundness boundary.
 *****************************************************************************)
Theory compute_boundedCase16594StateTrace
Ancestors
  compute_boundedPackedSequentialCase16594Check
Libs
  bossLib preamble wordsLib

Definition bounded_trace_word64_def:
  bounded_trace_word64 (hash:word64) (value:word64) =
    (hash << 40) + (hash << 8) + (hash << 7) + (hash << 5) +
    (hash << 4) + (hash << 1) + hash + value
End

Definition bounded_signed64_trace_hash_def:
  bounded_signed64_trace_hash hash
      (BoundedSigned64 negative magnitude) =
    bounded_trace_word64
      (bounded_trace_word64 hash (if negative then 1w else 0w)) magnitude
End

Definition bounded_interval64_trace_hash_def:
  bounded_interval64_trace_hash hash (BoundedInterval64 lower upper) =
    bounded_signed64_trace_hash
      (bounded_signed64_trace_hash hash lower) upper
End

Definition bounded_interval64_list_trace_hash_def:
  bounded_interval64_list_trace_hash hash [] = hash ∧
  bounded_interval64_list_trace_hash hash (entry::entries) =
    bounded_interval64_list_trace_hash
      (bounded_interval64_trace_hash hash entry) entries
End

Definition bounded_taylor64_trace_hash_def:
  bounded_taylor64_trace_hash hash
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    bounded_interval64_list_trace_hash
      (bounded_interval64_list_trace_hash
        (bounded_interval64_trace_hash
          (bounded_interval64_list_trace_hash
            (bounded_interval64_trace_hash
              (bounded_trace_word64 hash (if domain then 1w else 0w))
              center_value)
            center_gradient)
          value_bound)
        gradient_bounds)
      hessian
End

Definition bounded_taylor64_list_trace_hash_def:
  bounded_taylor64_list_trace_hash hash [] = hash ∧
  bounded_taylor64_list_trace_hash hash (entry::entries) =
    bounded_taylor64_list_trace_hash
      (bounded_taylor64_trace_hash hash entry) entries
End

Definition bounded_taylor64_stack_trace_hash_def:
  bounded_taylor64_stack_trace_hash stack =
    bounded_taylor64_list_trace_hash
      (bounded_trace_word64 1469598103934665603w (n2w (LENGTH stack)))
      (REVERSE stack)
End

(* When the full trace first differs at the sixth atan (instruction 82), emit
 * a compact structural bit mask instead of requiring a large state exporter:
 * 1 domain, 2 center value, 4 center gradient, 8 value bound,
 * 16 gradient bounds, and 32 Hessian. *)
Definition bounded_case16594_instruction82_group_status_def:
  bounded_case16594_instruction82_group_status
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    (n2w
      ((if domain then 0 else 1) +
       (if bounded_interval64_trace_hash 1469598103934665603w center_value =
             14509762782589906807w then 0 else 2) +
       (if bounded_interval64_list_trace_hash 1469598103934665603w
             center_gradient = 12792844311603009143w then 0 else 4) +
       (if bounded_interval64_trace_hash 1469598103934665603w value_bound =
             10406997224824790087w then 0 else 8) +
       (if bounded_interval64_list_trace_hash 1469598103934665603w
             gradient_bounds = 8593609897586137498w then 0 else 16) +
       (if bounded_interval64_list_trace_hash 1469598103934665603w hessian =
             14828992664330408141w then 0 else 32)) : word8)
End

(* Row-major upper-triangular Hessian interval hashes from the same native
 * instruction-82 state.  Returning the first differing entry keeps the
 * development diagnostic compact without exporting or trusting native
 * values in the checker. *)
Definition bounded_case16594_instruction82_hessian_hash_def:
  bounded_case16594_instruction82_hessian_hash (index:num) =
    ((if index = 0 then 15346707834502457176w
     else if index = 1 then 3378191489031394503w
     else if index = 2 then 18421368203033679381w
     else if index = 3 then 15551306751630864969w
     else if index = 4 then 8944077156510289393w
     else if index = 5 then 3663326071356285349w
     else if index = 6 then 5112082423903050010w
     else if index = 7 then 13869612965037290052w
     else if index = 8 then 276150408125482711w
     else if index = 9 then 1043379402365874703w
     else if index = 10 then 13005975287542919247w
     else if index = 11 then 4118984829661684490w
     else if index = 12 then 15680902861035588797w
     else if index = 13 then 13462119859813077143w
     else if index = 14 then 17987887518874781583w
     else if index = 15 then 5945716786420165457w
     else if index = 16 then 11044404055572651348w
     else if index = 17 then 12053069598522250335w
     else if index = 18 then 9033149392229122064w
     else if index = 19 then 14070702227452508424w
     else if index = 20 then 3910995204659883434w
     else 0w) : word64)
End

Definition bounded_case16594_instruction82_hessian_first_mismatch_def:
  bounded_case16594_instruction82_hessian_first_mismatch [] (index:num) =
    (0w:word8) ∧
  bounded_case16594_instruction82_hessian_first_mismatch
      (entry::entries) index =
    if bounded_interval64_trace_hash 1469598103934665603w entry =
         bounded_case16594_instruction82_hessian_hash index
    then bounded_case16594_instruction82_hessian_first_mismatch
           entries (SUC index)
    else (n2w (SUC index):word8)
End

Definition bounded_case16594_first_native_trace_hashes_def:
  bounded_case16594_first_native_trace_hashes =
  [4587492636500049637w; 12930798522704803241w;
   8631640603092256455w; 18201368569807832471w;
   5034928081039382847w; 13002446851820192655w;
   17054053459722641309w; 8350629609551775259w;
   2809000918092553279w; 16445541952097069541w;
   3243124440386177921w; 8884101152363225499w;
   1982935892982776019w; 7248960237652309179w;
   10577752498899081173w; 15543292721352382139w;
   6264667819534252247w; 9942071507697818835w;
   8014968758107883707w; 8293097830431609813w;
   16309301241807956667w; 16279820348227668405w;
   1131060520455970709w; 7361031496190092351w;
   9774986672641722762w; 10250982754201146754w;
   7073414360788653982w; 7388386733391137162w;
   6954542932951353168w; 3505894908327764876w;
   11089888901423930w; 3199802807476941683w;
   11078860635965366869w; 15837123362048108491w;
   12860439468527149456w; 2824178067787805793w;
   7005048674010159159w; 2687054768739826042w;
   9193366613354946404w; 1478151875194966090w;
   11121638358531250154w; 13537332713670152055w;
   10920136996683095245w; 5725740849149819419w;
   18250381419049713053w; 1523468179811476633w;
   6994988739408583151w; 18069697649903722989w;
   4933390733926494603w; 8984997341828943257w;
   281573491658077207w; 15843770486956893421w;
   11033567447251858067w; 16277894009250518063w;
   16124465395673527795w; 13321507543411547813w;
   14489324480962611475w; 5165777994053869699w;
   4336912890953132819w; 13505032062844554543w;
   2833899084417039013w; 15255333001418186003w;
   2881123325586398339w; 5102921411408707347w;
   5073440517828419085w; 12469632170884742503w;
   12724695910491071663w; 3561332141902443998w;
   7368362632700754724w; 4190794239288261952w;
   15843242907356378661w; 10961841423580584199w;
   7513193398956995907w; 16337538519650391508w;
   9971739644730232736w; 8393690016919574285w;
   14806763251135694569w; 17366091599282422743w;
   425648466958472266w; 138081071601547115w;
   8913890726548574817w; 4866234536386211188w;
   18143064825536898508w; 18439244355603116502w;
   3949142657734017460w; 8684955854007638586w;
   3760472288237850112w; 15579660511167213058w;
   3950338502523620586w; 2977762700213658440w;
   17700368078631153706w; 926886930833675736w;
   4978493538736124390w; 14721813762274809956w;
   15474440915684324138w; 10664237875979288784w;
   15908564437977948780w; 12107239356478603084w;
   15748377866123691766w; 10472098441767686764w;
   4796448422781300416w; 319686851758208108w;
   9487806023649629832w; 5260769407129182966w;
   11238106962223261292w; 2511793754313829056w;
   1085695372213782636w; 1056214478633494374w;
   14896502493596886456w; 2333997395427787248w;
   6827071807565009227w; 4142660718009718429w;
   965092324597225657w; 4440471868314423627w;
   846220896759924843w; 15844316945845888167w;
   9113061686163734843w; 17374323435975443350w;
   14136801279785362606w; 8740186984045153262w;
   2732366138264112627w; 14541690482477746753w;
   17553351751229536410w; 4247281272212980943w;
   10404073610769329665w; 17021949068602885573w;
   16956875130746125955w; 5594065852412015147w;
   5053186267008967745w; 9139991845911856125w;
   13136315582671259931w; 13535381141036168859w;
   6059829264829351053w; 3382969551026690203w;
   10084936506736561435w; 3984137810754412699w;
   13401421270117507213w; 17308359437701342649w;
   6105497963099359765w; 545551536455815009w;
   4597158144358263663w; 14340478367896949229w;
   3879570800152530197w; 17516111834157046459w;
   4313694322446154839w; 7991092020256735677w;
   6752716560008026777w; 6355951105545819357w;
   11648322380959058091w; 14650283589245892317w;
   5371658687427762425w; 14711852174723069593w;
   7121959626001393885w; 9363667712491586731w;
   15416292109701466845w; 15386811216121178583w;
   5900841187481221467w; 13174571075988960931w;
   2556778349684366973w; 3022159485979482275w;
   18065753433238933049w; 11035069913126424135w;
   18329168578733865671w; 1980599641447469333w;
   8593389002339221021w; 10643309426908731896w;
   6670871903741763864w]
End

(* Superseded equation form retained for fixture review; HOL definitions do
 * not accept numeral patterns beyond constructor form.
Definition bounded_case16594_first_native_trace_hash_def:
  bounded_case16594_first_native_trace_hash 0 = SOME 4587492636500049637w ∧
  bounded_case16594_first_native_trace_hash 1 = SOME 12930798522704803241w ∧
  bounded_case16594_first_native_trace_hash 2 = SOME 8631640603092256455w ∧
  bounded_case16594_first_native_trace_hash 3 = SOME 18201368569807832471w ∧
  bounded_case16594_first_native_trace_hash 4 = SOME 5034928081039382847w ∧
  bounded_case16594_first_native_trace_hash 5 = SOME 13002446851820192655w ∧
  bounded_case16594_first_native_trace_hash 6 = SOME 17054053459722641309w ∧
  bounded_case16594_first_native_trace_hash 7 = SOME 8350629609551775259w ∧
  bounded_case16594_first_native_trace_hash 8 = SOME 2809000918092553279w ∧
  bounded_case16594_first_native_trace_hash 9 = SOME 16445541952097069541w ∧
  bounded_case16594_first_native_trace_hash 10 = SOME 3243124440386177921w ∧
  bounded_case16594_first_native_trace_hash 11 = SOME 8884101152363225499w ∧
  bounded_case16594_first_native_trace_hash 12 = SOME 1982935892982776019w ∧
  bounded_case16594_first_native_trace_hash 13 = SOME 7248960237652309179w ∧
  bounded_case16594_first_native_trace_hash 14 = SOME 10577752498899081173w ∧
  bounded_case16594_first_native_trace_hash 15 = SOME 15543292721352382139w ∧
  bounded_case16594_first_native_trace_hash 16 = SOME 6264667819534252247w ∧
  bounded_case16594_first_native_trace_hash 17 = SOME 9942071507697818835w ∧
  bounded_case16594_first_native_trace_hash 18 = SOME 8014968758107883707w ∧
  bounded_case16594_first_native_trace_hash 19 = SOME 8293097830431609813w ∧
  bounded_case16594_first_native_trace_hash 20 = SOME 16309301241807956667w ∧
  bounded_case16594_first_native_trace_hash 21 = SOME 16279820348227668405w ∧
  bounded_case16594_first_native_trace_hash 22 = SOME 1131060520455970709w ∧
  bounded_case16594_first_native_trace_hash 23 = SOME 7361031496190092351w ∧
  bounded_case16594_first_native_trace_hash 24 = SOME 9774986672641722762w ∧
  bounded_case16594_first_native_trace_hash 25 = SOME 10250982754201146754w ∧
  bounded_case16594_first_native_trace_hash 26 = SOME 7073414360788653982w ∧
  bounded_case16594_first_native_trace_hash 27 = SOME 7388386733391137162w ∧
  bounded_case16594_first_native_trace_hash 28 = SOME 6954542932951353168w ∧
  bounded_case16594_first_native_trace_hash 29 = SOME 3505894908327764876w ∧
  bounded_case16594_first_native_trace_hash 30 = SOME 11089888901423930w ∧
  bounded_case16594_first_native_trace_hash 31 = SOME 3199802807476941683w ∧
  bounded_case16594_first_native_trace_hash 32 = SOME 11078860635965366869w ∧
  bounded_case16594_first_native_trace_hash 33 = SOME 15837123362048108491w ∧
  bounded_case16594_first_native_trace_hash 34 = SOME 12860439468527149456w ∧
  bounded_case16594_first_native_trace_hash 35 = SOME 2824178067787805793w ∧
  bounded_case16594_first_native_trace_hash 36 = SOME 7005048674010159159w ∧
  bounded_case16594_first_native_trace_hash 37 = SOME 2687054768739826042w ∧
  bounded_case16594_first_native_trace_hash 38 = SOME 9193366613354946404w ∧
  bounded_case16594_first_native_trace_hash 39 = SOME 1478151875194966090w ∧
  bounded_case16594_first_native_trace_hash 40 = SOME 11121638358531250154w ∧
  bounded_case16594_first_native_trace_hash 41 = SOME 13537332713670152055w ∧
  bounded_case16594_first_native_trace_hash 42 = SOME 10920136996683095245w ∧
  bounded_case16594_first_native_trace_hash 43 = SOME 5725740849149819419w ∧
  bounded_case16594_first_native_trace_hash 44 = SOME 18250381419049713053w ∧
  bounded_case16594_first_native_trace_hash 45 = SOME 1523468179811476633w ∧
  bounded_case16594_first_native_trace_hash 46 = SOME 6994988739408583151w ∧
  bounded_case16594_first_native_trace_hash 47 = SOME 18069697649903722989w ∧
  bounded_case16594_first_native_trace_hash 48 = SOME 4933390733926494603w ∧
  bounded_case16594_first_native_trace_hash 49 = SOME 8984997341828943257w ∧
  bounded_case16594_first_native_trace_hash 50 = SOME 281573491658077207w ∧
  bounded_case16594_first_native_trace_hash 51 = SOME 15843770486956893421w ∧
  bounded_case16594_first_native_trace_hash 52 = SOME 11033567447251858067w ∧
  bounded_case16594_first_native_trace_hash 53 = SOME 16277894009250518063w ∧
  bounded_case16594_first_native_trace_hash 54 = SOME 16124465395673527795w ∧
  bounded_case16594_first_native_trace_hash 55 = SOME 13321507543411547813w ∧
  bounded_case16594_first_native_trace_hash 56 = SOME 14489324480962611475w ∧
  bounded_case16594_first_native_trace_hash 57 = SOME 5165777994053869699w ∧
  bounded_case16594_first_native_trace_hash 58 = SOME 4336912890953132819w ∧
  bounded_case16594_first_native_trace_hash 59 = SOME 13505032062844554543w ∧
  bounded_case16594_first_native_trace_hash 60 = SOME 2833899084417039013w ∧
  bounded_case16594_first_native_trace_hash 61 = SOME 15255333001418186003w ∧
  bounded_case16594_first_native_trace_hash 62 = SOME 2881123325586398339w ∧
  bounded_case16594_first_native_trace_hash 63 = SOME 5102921411408707347w ∧
  bounded_case16594_first_native_trace_hash 64 = SOME 5073440517828419085w ∧
  bounded_case16594_first_native_trace_hash 65 = SOME 12469632170884742503w ∧
  bounded_case16594_first_native_trace_hash 66 = SOME 12724695910491071663w ∧
  bounded_case16594_first_native_trace_hash 67 = SOME 3561332141902443998w ∧
  bounded_case16594_first_native_trace_hash 68 = SOME 7368362632700754724w ∧
  bounded_case16594_first_native_trace_hash 69 = SOME 4190794239288261952w ∧
  bounded_case16594_first_native_trace_hash 70 = SOME 15843242907356378661w ∧
  bounded_case16594_first_native_trace_hash 71 = SOME 10961841423580584199w ∧
  bounded_case16594_first_native_trace_hash 72 = SOME 7513193398956995907w ∧
  bounded_case16594_first_native_trace_hash 73 = SOME 16337538519650391508w ∧
  bounded_case16594_first_native_trace_hash 74 = SOME 9971739644730232736w ∧
  bounded_case16594_first_native_trace_hash 75 = SOME 8393690016919574285w ∧
  bounded_case16594_first_native_trace_hash 76 = SOME 14806763251135694569w ∧
  bounded_case16594_first_native_trace_hash 77 = SOME 17366091599282422743w ∧
  bounded_case16594_first_native_trace_hash 78 = SOME 425648466958472266w ∧
  bounded_case16594_first_native_trace_hash 79 = SOME 138081071601547115w ∧
  bounded_case16594_first_native_trace_hash 80 = SOME 8913890726548574817w ∧
  bounded_case16594_first_native_trace_hash 81 = SOME 4866234536386211188w ∧
  bounded_case16594_first_native_trace_hash 82 = SOME 18143064825536898508w ∧
  bounded_case16594_first_native_trace_hash 83 = SOME 18439244355603116502w ∧
  bounded_case16594_first_native_trace_hash 84 = SOME 3949142657734017460w ∧
  bounded_case16594_first_native_trace_hash 85 = SOME 8684955854007638586w ∧
  bounded_case16594_first_native_trace_hash 86 = SOME 3760472288237850112w ∧
  bounded_case16594_first_native_trace_hash 87 = SOME 15579660511167213058w ∧
  bounded_case16594_first_native_trace_hash 88 = SOME 3950338502523620586w ∧
  bounded_case16594_first_native_trace_hash 89 = SOME 2977762700213658440w ∧
  bounded_case16594_first_native_trace_hash 90 = SOME 17700368078631153706w ∧
  bounded_case16594_first_native_trace_hash 91 = SOME 926886930833675736w ∧
  bounded_case16594_first_native_trace_hash 92 = SOME 4978493538736124390w ∧
  bounded_case16594_first_native_trace_hash 93 = SOME 14721813762274809956w ∧
  bounded_case16594_first_native_trace_hash 94 = SOME 15474440915684324138w ∧
  bounded_case16594_first_native_trace_hash 95 = SOME 10664237875979288784w ∧
  bounded_case16594_first_native_trace_hash 96 = SOME 15908564437977948780w ∧
  bounded_case16594_first_native_trace_hash 97 = SOME 12107239356478603084w ∧
  bounded_case16594_first_native_trace_hash 98 = SOME 15748377866123691766w ∧
  bounded_case16594_first_native_trace_hash 99 = SOME 10472098441767686764w ∧
  bounded_case16594_first_native_trace_hash 100 = SOME 4796448422781300416w ∧
  bounded_case16594_first_native_trace_hash 101 = SOME 319686851758208108w ∧
  bounded_case16594_first_native_trace_hash 102 = SOME 9487806023649629832w ∧
  bounded_case16594_first_native_trace_hash 103 = SOME 5260769407129182966w ∧
  bounded_case16594_first_native_trace_hash 104 = SOME 11238106962223261292w ∧
  bounded_case16594_first_native_trace_hash 105 = SOME 2511793754313829056w ∧
  bounded_case16594_first_native_trace_hash 106 = SOME 1085695372213782636w ∧
  bounded_case16594_first_native_trace_hash 107 = SOME 1056214478633494374w ∧
  bounded_case16594_first_native_trace_hash 108 = SOME 14896502493596886456w ∧
  bounded_case16594_first_native_trace_hash 109 = SOME 2333997395427787248w ∧
  bounded_case16594_first_native_trace_hash 110 = SOME 6827071807565009227w ∧
  bounded_case16594_first_native_trace_hash 111 = SOME 4142660718009718429w ∧
  bounded_case16594_first_native_trace_hash 112 = SOME 965092324597225657w ∧
  bounded_case16594_first_native_trace_hash 113 = SOME 4440471868314423627w ∧
  bounded_case16594_first_native_trace_hash 114 = SOME 846220896759924843w ∧
  bounded_case16594_first_native_trace_hash 115 = SOME 15844316945845888167w ∧
  bounded_case16594_first_native_trace_hash 116 = SOME 9113061686163734843w ∧
  bounded_case16594_first_native_trace_hash 117 = SOME 17374323435975443350w ∧
  bounded_case16594_first_native_trace_hash 118 = SOME 14136801279785362606w ∧
  bounded_case16594_first_native_trace_hash 119 = SOME 8740186984045153262w ∧
  bounded_case16594_first_native_trace_hash 120 = SOME 2732366138264112627w ∧
  bounded_case16594_first_native_trace_hash 121 = SOME 14541690482477746753w ∧
  bounded_case16594_first_native_trace_hash 122 = SOME 17553351751229536410w ∧
  bounded_case16594_first_native_trace_hash 123 = SOME 4247281272212980943w ∧
  bounded_case16594_first_native_trace_hash 124 = SOME 10404073610769329665w ∧
  bounded_case16594_first_native_trace_hash 125 = SOME 17021949068602885573w ∧
  bounded_case16594_first_native_trace_hash 126 = SOME 16956875130746125955w ∧
  bounded_case16594_first_native_trace_hash 127 = SOME 5594065852412015147w ∧
  bounded_case16594_first_native_trace_hash 128 = SOME 5053186267008967745w ∧
  bounded_case16594_first_native_trace_hash 129 = SOME 9139991845911856125w ∧
  bounded_case16594_first_native_trace_hash 130 = SOME 13136315582671259931w ∧
  bounded_case16594_first_native_trace_hash 131 = SOME 13535381141036168859w ∧
  bounded_case16594_first_native_trace_hash 132 = SOME 6059829264829351053w ∧
  bounded_case16594_first_native_trace_hash 133 = SOME 3382969551026690203w ∧
  bounded_case16594_first_native_trace_hash 134 = SOME 10084936506736561435w ∧
  bounded_case16594_first_native_trace_hash 135 = SOME 3984137810754412699w ∧
  bounded_case16594_first_native_trace_hash 136 = SOME 13401421270117507213w ∧
  bounded_case16594_first_native_trace_hash 137 = SOME 17308359437701342649w ∧
  bounded_case16594_first_native_trace_hash 138 = SOME 6105497963099359765w ∧
  bounded_case16594_first_native_trace_hash 139 = SOME 545551536455815009w ∧
  bounded_case16594_first_native_trace_hash 140 = SOME 4597158144358263663w ∧
  bounded_case16594_first_native_trace_hash 141 = SOME 14340478367896949229w ∧
  bounded_case16594_first_native_trace_hash 142 = SOME 3879570800152530197w ∧
  bounded_case16594_first_native_trace_hash 143 = SOME 17516111834157046459w ∧
  bounded_case16594_first_native_trace_hash 144 = SOME 4313694322446154839w ∧
  bounded_case16594_first_native_trace_hash 145 = SOME 7991092020256735677w ∧
  bounded_case16594_first_native_trace_hash 146 = SOME 6752716560008026777w ∧
  bounded_case16594_first_native_trace_hash 147 = SOME 6355951105545819357w ∧
  bounded_case16594_first_native_trace_hash 148 = SOME 11648322380959058091w ∧
  bounded_case16594_first_native_trace_hash 149 = SOME 14650283589245892317w ∧
  bounded_case16594_first_native_trace_hash 150 = SOME 5371658687427762425w ∧
  bounded_case16594_first_native_trace_hash 151 = SOME 14711852174723069593w ∧
  bounded_case16594_first_native_trace_hash 152 = SOME 7121959626001393885w ∧
  bounded_case16594_first_native_trace_hash 153 = SOME 9363667712491586731w ∧
  bounded_case16594_first_native_trace_hash 154 = SOME 15416292109701466845w ∧
  bounded_case16594_first_native_trace_hash 155 = SOME 15386811216121178583w ∧
  bounded_case16594_first_native_trace_hash 156 = SOME 5900841187481221467w ∧
  bounded_case16594_first_native_trace_hash 157 = SOME 13174571075988960931w ∧
  bounded_case16594_first_native_trace_hash 158 = SOME 2556778349684366973w ∧
  bounded_case16594_first_native_trace_hash 159 = SOME 3022159485979482275w ∧
  bounded_case16594_first_native_trace_hash 160 = SOME 18065753433238933049w ∧
  bounded_case16594_first_native_trace_hash 161 = SOME 11035069913126424135w ∧
  bounded_case16594_first_native_trace_hash 162 = SOME 18329168578733865671w ∧
  bounded_case16594_first_native_trace_hash 163 = SOME 1980599641447469333w ∧
  bounded_case16594_first_native_trace_hash 164 = SOME 8593389002339221021w ∧
  bounded_case16594_first_native_trace_hash 165 = SOME 10643309426908731896w ∧
  bounded_case16594_first_native_trace_hash 166 = SOME 6670871903741763864w ∧
  bounded_case16594_first_native_trace_hash _ = NONE
End *)

Definition bounded_case16594_first_native_trace_hash_def:
  bounded_case16594_first_native_trace_hash (index:num) =
    if index = 0 then SOME 4587492636500049637w
    else
    if index = 1 then SOME 12930798522704803241w
    else
    if index = 2 then SOME 8631640603092256455w
    else
    if index = 3 then SOME 18201368569807832471w
    else
    if index = 4 then SOME 5034928081039382847w
    else
    if index = 5 then SOME 13002446851820192655w
    else
    if index = 6 then SOME 17054053459722641309w
    else
    if index = 7 then SOME 8350629609551775259w
    else
    if index = 8 then SOME 2809000918092553279w
    else
    if index = 9 then SOME 16445541952097069541w
    else
    if index = 10 then SOME 3243124440386177921w
    else
    if index = 11 then SOME 8884101152363225499w
    else
    if index = 12 then SOME 1982935892982776019w
    else
    if index = 13 then SOME 7248960237652309179w
    else
    if index = 14 then SOME 10577752498899081173w
    else
    if index = 15 then SOME 15543292721352382139w
    else
    if index = 16 then SOME 6264667819534252247w
    else
    if index = 17 then SOME 9942071507697818835w
    else
    if index = 18 then SOME 8014968758107883707w
    else
    if index = 19 then SOME 8293097830431609813w
    else
    if index = 20 then SOME 16309301241807956667w
    else
    if index = 21 then SOME 16279820348227668405w
    else
    if index = 22 then SOME 1131060520455970709w
    else
    if index = 23 then SOME 7361031496190092351w
    else
    if index = 24 then SOME 9774986672641722762w
    else
    if index = 25 then SOME 10250982754201146754w
    else
    if index = 26 then SOME 7073414360788653982w
    else
    if index = 27 then SOME 7388386733391137162w
    else
    if index = 28 then SOME 6954542932951353168w
    else
    if index = 29 then SOME 3505894908327764876w
    else
    if index = 30 then SOME 11089888901423930w
    else
    if index = 31 then SOME 3199802807476941683w
    else
    if index = 32 then SOME 11078860635965366869w
    else
    if index = 33 then SOME 15837123362048108491w
    else
    if index = 34 then SOME 12860439468527149456w
    else
    if index = 35 then SOME 2824178067787805793w
    else
    if index = 36 then SOME 7005048674010159159w
    else
    if index = 37 then SOME 2687054768739826042w
    else
    if index = 38 then SOME 9193366613354946404w
    else
    if index = 39 then SOME 1478151875194966090w
    else
    if index = 40 then SOME 11121638358531250154w
    else
    if index = 41 then SOME 13537332713670152055w
    else
    if index = 42 then SOME 10920136996683095245w
    else
    if index = 43 then SOME 5725740849149819419w
    else
    if index = 44 then SOME 18250381419049713053w
    else
    if index = 45 then SOME 1523468179811476633w
    else
    if index = 46 then SOME 6994988739408583151w
    else
    if index = 47 then SOME 18069697649903722989w
    else
    if index = 48 then SOME 4933390733926494603w
    else
    if index = 49 then SOME 8984997341828943257w
    else
    if index = 50 then SOME 281573491658077207w
    else
    if index = 51 then SOME 15843770486956893421w
    else
    if index = 52 then SOME 11033567447251858067w
    else
    if index = 53 then SOME 16277894009250518063w
    else
    if index = 54 then SOME 16124465395673527795w
    else
    if index = 55 then SOME 13321507543411547813w
    else
    if index = 56 then SOME 14489324480962611475w
    else
    if index = 57 then SOME 5165777994053869699w
    else
    if index = 58 then SOME 4336912890953132819w
    else
    if index = 59 then SOME 13505032062844554543w
    else
    if index = 60 then SOME 2833899084417039013w
    else
    if index = 61 then SOME 15255333001418186003w
    else
    if index = 62 then SOME 2881123325586398339w
    else
    if index = 63 then SOME 5102921411408707347w
    else
    if index = 64 then SOME 5073440517828419085w
    else
    if index = 65 then SOME 12469632170884742503w
    else
    if index = 66 then SOME 12724695910491071663w
    else
    if index = 67 then SOME 3561332141902443998w
    else
    if index = 68 then SOME 7368362632700754724w
    else
    if index = 69 then SOME 4190794239288261952w
    else
    if index = 70 then SOME 15843242907356378661w
    else
    if index = 71 then SOME 10961841423580584199w
    else
    if index = 72 then SOME 7513193398956995907w
    else
    if index = 73 then SOME 16337538519650391508w
    else
    if index = 74 then SOME 9971739644730232736w
    else
    if index = 75 then SOME 8393690016919574285w
    else
    if index = 76 then SOME 14806763251135694569w
    else
    if index = 77 then SOME 17366091599282422743w
    else
    if index = 78 then SOME 425648466958472266w
    else
    if index = 79 then SOME 138081071601547115w
    else
    if index = 80 then SOME 8913890726548574817w
    else
    if index = 81 then SOME 4866234536386211188w
    else
    if index = 82 then SOME 18143064825536898508w
    else
    if index = 83 then SOME 18439244355603116502w
    else
    if index = 84 then SOME 3949142657734017460w
    else
    if index = 85 then SOME 8684955854007638586w
    else
    if index = 86 then SOME 3760472288237850112w
    else
    if index = 87 then SOME 15579660511167213058w
    else
    if index = 88 then SOME 3950338502523620586w
    else
    if index = 89 then SOME 2977762700213658440w
    else
    if index = 90 then SOME 17700368078631153706w
    else
    if index = 91 then SOME 926886930833675736w
    else
    if index = 92 then SOME 4978493538736124390w
    else
    if index = 93 then SOME 14721813762274809956w
    else
    if index = 94 then SOME 15474440915684324138w
    else
    if index = 95 then SOME 10664237875979288784w
    else
    if index = 96 then SOME 15908564437977948780w
    else
    if index = 97 then SOME 12107239356478603084w
    else
    if index = 98 then SOME 15748377866123691766w
    else
    if index = 99 then SOME 10472098441767686764w
    else
    if index = 100 then SOME 4796448422781300416w
    else
    if index = 101 then SOME 319686851758208108w
    else
    if index = 102 then SOME 9487806023649629832w
    else
    if index = 103 then SOME 5260769407129182966w
    else
    if index = 104 then SOME 11238106962223261292w
    else
    if index = 105 then SOME 2511793754313829056w
    else
    if index = 106 then SOME 1085695372213782636w
    else
    if index = 107 then SOME 1056214478633494374w
    else
    if index = 108 then SOME 14896502493596886456w
    else
    if index = 109 then SOME 2333997395427787248w
    else
    if index = 110 then SOME 6827071807565009227w
    else
    if index = 111 then SOME 4142660718009718429w
    else
    if index = 112 then SOME 965092324597225657w
    else
    if index = 113 then SOME 4440471868314423627w
    else
    if index = 114 then SOME 846220896759924843w
    else
    if index = 115 then SOME 15844316945845888167w
    else
    if index = 116 then SOME 9113061686163734843w
    else
    if index = 117 then SOME 17374323435975443350w
    else
    if index = 118 then SOME 14136801279785362606w
    else
    if index = 119 then SOME 8740186984045153262w
    else
    if index = 120 then SOME 2732366138264112627w
    else
    if index = 121 then SOME 14541690482477746753w
    else
    if index = 122 then SOME 17553351751229536410w
    else
    if index = 123 then SOME 4247281272212980943w
    else
    if index = 124 then SOME 10404073610769329665w
    else
    if index = 125 then SOME 17021949068602885573w
    else
    if index = 126 then SOME 16956875130746125955w
    else
    if index = 127 then SOME 5594065852412015147w
    else
    if index = 128 then SOME 5053186267008967745w
    else
    if index = 129 then SOME 9139991845911856125w
    else
    if index = 130 then SOME 13136315582671259931w
    else
    if index = 131 then SOME 13535381141036168859w
    else
    if index = 132 then SOME 6059829264829351053w
    else
    if index = 133 then SOME 3382969551026690203w
    else
    if index = 134 then SOME 10084936506736561435w
    else
    if index = 135 then SOME 3984137810754412699w
    else
    if index = 136 then SOME 13401421270117507213w
    else
    if index = 137 then SOME 17308359437701342649w
    else
    if index = 138 then SOME 6105497963099359765w
    else
    if index = 139 then SOME 545551536455815009w
    else
    if index = 140 then SOME 4597158144358263663w
    else
    if index = 141 then SOME 14340478367896949229w
    else
    if index = 142 then SOME 3879570800152530197w
    else
    if index = 143 then SOME 17516111834157046459w
    else
    if index = 144 then SOME 4313694322446154839w
    else
    if index = 145 then SOME 7991092020256735677w
    else
    if index = 146 then SOME 6752716560008026777w
    else
    if index = 147 then SOME 6355951105545819357w
    else
    if index = 148 then SOME 11648322380959058091w
    else
    if index = 149 then SOME 14650283589245892317w
    else
    if index = 150 then SOME 5371658687427762425w
    else
    if index = 151 then SOME 14711852174723069593w
    else
    if index = 152 then SOME 7121959626001393885w
    else
    if index = 153 then SOME 9363667712491586731w
    else
    if index = 154 then SOME 15416292109701466845w
    else
    if index = 155 then SOME 15386811216121178583w
    else
    if index = 156 then SOME 5900841187481221467w
    else
    if index = 157 then SOME 13174571075988960931w
    else
    if index = 158 then SOME 2556778349684366973w
    else
    if index = 159 then SOME 3022159485979482275w
    else
    if index = 160 then SOME 18065753433238933049w
    else
    if index = 161 then SOME 11035069913126424135w
    else
    if index = 162 then SOME 18329168578733865671w
    else
    if index = 163 then SOME 1980599641447469333w
    else
    if index = 164 then SOME 8593389002339221021w
    else
    if index = 165 then SOME 10643309426908731896w
    else
    if index = 166 then SOME 6670871903741763864w
    else
      NONE
End

Definition bounded_case16594_first_native_trace_expected_def:
  bounded_case16594_first_native_trace_expected (index:num) =
    BoundedSigned64 F
      (if index = 0 then 4587492636500049637w
       else if index = 1 then 12930798522704803241w
       else if index = 2 then 8631640603092256455w
       else if index = 3 then 18201368569807832471w
       else if index = 4 then 5034928081039382847w
       else if index = 5 then 13002446851820192655w
       else if index = 6 then 17054053459722641309w
       else if index = 7 then 8350629609551775259w
       else if index = 8 then 2809000918092553279w
       else if index = 9 then 16445541952097069541w
       else if index = 10 then 3243124440386177921w
       else if index = 11 then 8884101152363225499w
       else if index = 12 then 1982935892982776019w
       else if index = 13 then 7248960237652309179w
       else if index = 14 then 10577752498899081173w
       else if index = 15 then 15543292721352382139w
       else if index = 16 then 6264667819534252247w
       else if index = 17 then 9942071507697818835w
       else if index = 18 then 8014968758107883707w
       else if index = 19 then 8293097830431609813w
       else if index = 20 then 16309301241807956667w
       else if index = 21 then 16279820348227668405w
       else if index = 22 then 1131060520455970709w
       else if index = 23 then 7361031496190092351w
       else if index = 24 then 9774986672641722762w
       else if index = 25 then 10250982754201146754w
       else if index = 26 then 7073414360788653982w
       else if index = 27 then 7388386733391137162w
       else if index = 28 then 6954542932951353168w
       else if index = 29 then 3505894908327764876w
       else if index = 30 then 11089888901423930w
       else if index = 31 then 3199802807476941683w
       else if index = 32 then 11078860635965366869w
       else if index = 33 then 15837123362048108491w
       else if index = 34 then 12860439468527149456w
       else if index = 35 then 2824178067787805793w
       else if index = 36 then 7005048674010159159w
       else if index = 37 then 2687054768739826042w
       else if index = 38 then 9193366613354946404w
       else if index = 39 then 1478151875194966090w
       else if index = 40 then 11121638358531250154w
       else if index = 41 then 13537332713670152055w
       else if index = 42 then 10920136996683095245w
       else if index = 43 then 5725740849149819419w
       else if index = 44 then 18250381419049713053w
       else if index = 45 then 1523468179811476633w
       else if index = 46 then 6994988739408583151w
       else if index = 47 then 18069697649903722989w
       else if index = 48 then 4933390733926494603w
       else if index = 49 then 8984997341828943257w
       else if index = 50 then 281573491658077207w
       else if index = 51 then 15843770486956893421w
       else if index = 52 then 11033567447251858067w
       else if index = 53 then 16277894009250518063w
       else if index = 54 then 16124465395673527795w
       else if index = 55 then 13321507543411547813w
       else if index = 56 then 14489324480962611475w
       else if index = 57 then 5165777994053869699w
       else if index = 58 then 4336912890953132819w
       else if index = 59 then 13505032062844554543w
       else if index = 60 then 2833899084417039013w
       else if index = 61 then 15255333001418186003w
       else if index = 62 then 2881123325586398339w
       else if index = 63 then 5102921411408707347w
       else if index = 64 then 5073440517828419085w
       else if index = 65 then 12469632170884742503w
       else if index = 66 then 12724695910491071663w
       else if index = 67 then 3561332141902443998w
       else if index = 68 then 7368362632700754724w
       else if index = 69 then 4190794239288261952w
       else if index = 70 then 15843242907356378661w
       else if index = 71 then 10961841423580584199w
       else if index = 72 then 7513193398956995907w
       else if index = 73 then 16337538519650391508w
       else if index = 74 then 9971739644730232736w
       else if index = 75 then 8393690016919574285w
       else if index = 76 then 14806763251135694569w
       else if index = 77 then 17366091599282422743w
       else if index = 78 then 425648466958472266w
       else if index = 79 then 138081071601547115w
       else if index = 80 then 8913890726548574817w
       else if index = 81 then 4866234536386211188w
       else if index = 82 then 18143064825536898508w
       else if index = 83 then 18439244355603116502w
       else if index = 84 then 3949142657734017460w
       else if index = 85 then 8684955854007638586w
       else if index = 86 then 3760472288237850112w
       else if index = 87 then 15579660511167213058w
       else if index = 88 then 3950338502523620586w
       else if index = 89 then 2977762700213658440w
       else if index = 90 then 17700368078631153706w
       else if index = 91 then 926886930833675736w
       else if index = 92 then 4978493538736124390w
       else if index = 93 then 14721813762274809956w
       else if index = 94 then 15474440915684324138w
       else if index = 95 then 10664237875979288784w
       else if index = 96 then 15908564437977948780w
       else if index = 97 then 12107239356478603084w
       else if index = 98 then 15748377866123691766w
       else if index = 99 then 10472098441767686764w
       else if index = 100 then 4796448422781300416w
       else if index = 101 then 319686851758208108w
       else if index = 102 then 9487806023649629832w
       else if index = 103 then 5260769407129182966w
       else if index = 104 then 11238106962223261292w
       else if index = 105 then 2511793754313829056w
       else if index = 106 then 1085695372213782636w
       else if index = 107 then 1056214478633494374w
       else if index = 108 then 14896502493596886456w
       else if index = 109 then 2333997395427787248w
       else if index = 110 then 6827071807565009227w
       else if index = 111 then 4142660718009718429w
       else if index = 112 then 965092324597225657w
       else if index = 113 then 4440471868314423627w
       else if index = 114 then 846220896759924843w
       else if index = 115 then 15844316945845888167w
       else if index = 116 then 9113061686163734843w
       else if index = 117 then 17374323435975443350w
       else if index = 118 then 14136801279785362606w
       else if index = 119 then 8740186984045153262w
       else if index = 120 then 2732366138264112627w
       else if index = 121 then 14541690482477746753w
       else if index = 122 then 17553351751229536410w
       else if index = 123 then 4247281272212980943w
       else if index = 124 then 10404073610769329665w
       else if index = 125 then 17021949068602885573w
       else if index = 126 then 16956875130746125955w
       else if index = 127 then 5594065852412015147w
       else if index = 128 then 5053186267008967745w
       else if index = 129 then 9139991845911856125w
       else if index = 130 then 13136315582671259931w
       else if index = 131 then 13535381141036168859w
       else if index = 132 then 6059829264829351053w
       else if index = 133 then 3382969551026690203w
       else if index = 134 then 10084936506736561435w
       else if index = 135 then 3984137810754412699w
       else if index = 136 then 13401421270117507213w
       else if index = 137 then 17308359437701342649w
       else if index = 138 then 6105497963099359765w
       else if index = 139 then 545551536455815009w
       else if index = 140 then 4597158144358263663w
       else if index = 141 then 14340478367896949229w
       else if index = 142 then 3879570800152530197w
       else if index = 143 then 17516111834157046459w
       else if index = 144 then 4313694322446154839w
       else if index = 145 then 7991092020256735677w
       else if index = 146 then 6752716560008026777w
       else if index = 147 then 6355951105545819357w
       else if index = 148 then 11648322380959058091w
       else if index = 149 then 14650283589245892317w
       else if index = 150 then 5371658687427762425w
       else if index = 151 then 14711852174723069593w
       else if index = 152 then 7121959626001393885w
       else if index = 153 then 9363667712491586731w
       else if index = 154 then 15416292109701466845w
       else if index = 155 then 15386811216121178583w
       else if index = 156 then 5900841187481221467w
       else if index = 157 then 13174571075988960931w
       else if index = 158 then 2556778349684366973w
       else if index = 159 then 3022159485979482275w
       else if index = 160 then 18065753433238933049w
       else if index = 161 then 11035069913126424135w
       else if index = 162 then 18329168578733865671w
       else if index = 163 then 1980599641447469333w
       else if index = 164 then 8593389002339221021w
       else if index = 165 then 10643309426908731896w
       else if index = 166 then 6670871903741763864w
       else 0w)
End

Definition bounded_case16594_state_trace_run_def:
  bounded_case16594_state_trace_run (radii:word64 list)
      (center_environment:bounded_interval64 list)
      (box_environment:bounded_interval64 list)
      (instructions:bounded_analytic64_instruction list)
      (state:bounded_taylor64 list # bounded_analytic64_certificate list)
      (index:num) =
    case instructions of
    | [] =>
        (case state of
         | ([BoundedTaylor64 result_domain result_center_value
                result_center_gradient result_value_bound
                result_gradient_bounds result_hessian],[]) =>
             if bounded_signed64_strict_negative
               (bounded_interval64_upper result_value_bound)
             then (0w:word8) else 250w
         | ([_],[]) => 249w
         | (_,[]) => 248w
         | _ => 247w)
    | instruction::rest =>
        (case bounded_case16594_first_native_trace_expected index of
         | BoundedSigned64 unexpected expected =>
           if unexpected then 255w else
           case bounded_analytic64_program_step radii center_environment
             box_environment instruction state of
           | NONE => 254w
           | SOME next =>
               if bounded_taylor64_stack_trace_hash (FST next) = expected then
                 bounded_case16594_state_trace_run radii center_environment
                   box_environment rest next (SUC index)
               else if index = 82 then
                 case FST next of
                 | result::stack =>
                     (case result of
                      | BoundedTaylor64 result_domain result_center_value
                          result_center_gradient result_value_bound
                          result_gradient_bounds hessian =>
                          bounded_case16594_instruction82_hessian_first_mismatch
                            hessian 0)
                 | [] => 255w
               else n2w (SUC index))
End

Definition bounded_case16594_first_state_trace_status_def:
  bounded_case16594_first_state_trace_status
      ((box_environment,center_environment,radii),certificates) =
    bounded_case16594_state_trace_run radii center_environment
      box_environment bounded_case16594_prepared_program ([],certificates) 0
End

Definition bounded_packed_chars_case16594_first_state_trace_status_def:
  bounded_packed_chars_case16594_first_state_trace_status bytes =
    case bounded_packed_chars_case16594_header bytes of
    | NONE => (252w:word8)
    | SOME rest =>
      case bounded_packed_chars_case16594_cell rest of
      | NONE => (253w:word8)
      | SOME (cell,remaining) =>
          bounded_case16594_first_state_trace_status cell
End

Theorem bounded_case16594_first_native_trace_hash_count:
  LENGTH bounded_case16594_first_native_trace_hashes = 167
Proof
  EVAL_TAC
QED

val _ = export_theory ();
