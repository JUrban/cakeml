(*****************************************************************************
 * Development-only instruction-state discriminator for genuine cell 220.
 *
 * The expected hashes come from the independent native fixed-scale trace
 * whose 31 scalar certificates match the unchanged full-batch certificate
 * rows for cell 220.  Status 1..167 is the first differing/failing
 * instruction; zero is a complete matching, accepting execution.
 *****************************************************************************)
Theory compute_boundedCase16594Cell220StateTrace
Ancestors
  compute_boundedCase16594StateTrace
  compute_boundedCase16594BatchStatus
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_cell220_native_trace_hashes_def:
  bounded_case16594_cell220_native_trace_hashes () =
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
   1131060520455970709w; 10651523648652402811w;
   10054597010633458258w; 1018512145506903514w;
   16287687825803962358w; 7667997071382872658w;
   16168816397966661544w; 12720168373343073252w;
   7462956093029782318w; 17497310959134943161w;
   6929624713913816731w; 16847630625188861213w;
   7403110393233217843w; 6025164822557626262w;
   6335777492746222660w; 16759711671621917740w;
   4920403094401313830w; 8267499400347254628w;
   465812304847291112w; 14440973196997446826w;
   10498671804887378086w; 10640572794506303942w;
   18186846308486691550w; 9153880128883828508w;
   12791805192486703544w; 11315526683527727624w;
   15405313844405451804w; 1010176378598348842w;
   10753496602137034408w; 9089599520580898056w;
   4279396480875862702w; 9523723042874522698w;
   3474537775042096572w; 2505175418774348072w;
   1839396860331180252w; 16858351101387425950w;
   10133729344031253212w; 855104442213123320w;
   10464311033489390888w; 2605405380786754780w;
   14573696432919954590w; 10899737864486827740w;
   10870256970906539478w; 1653300046247542762w;
   8947038794235998168w; 2776523136995267111w;
   6871811657073848511w; 3694243263661355739w;
   12887580404593530052w; 11443962047018652196w;
   7995314022395063904w; 4225899424839336519w;
   16401182000246996396w; 9862838794546616563w;
   7871136105358742811w; 12711576855187026067w;
   5255607475857024541w; 14668331790602081837w;
   8512861789039848131w; 4921197773920091059w;
   10468932450752814346w; 2589535697542516693w;
   1966025707424196507w; 16537266384907153199w;
   13057074369396512679w; 15199974278581321271w;
   17342730850555103049w; 2419167879759740837w;
   6775212119654137089w; 8752356191679132573w;
   12803962799581581227w; 4100538949410715177w;
   4549284956707307521w; 18185825990711823783w;
   4983408479000932163w; 11548644536024685481w;
   10694026140445622613w; 9913503621313769161w;
   12318036537513835415w; 18207836105013842121w;
   8929211203195712229w; 206417681451113813w;
   10679512141769343689w; 10033381869046364055w;
   527100551759865033w; 497619658179576771w;
   9842150767918817303w; 5065894727436180105w;
   2702220874556142864w; 13977760469928138668w;
   10800192076515645896w; 315620935305557264w;
   10681320648678345082w; 7232672624054756790w;
   5729898604179027788w; 14855425604307351867w;
   16292568941209448489w; 4018758452252969119w;
   7183233820776802340w; 5171897958759847662w;
   519013711561010359w; 3546539783581751763w;
   1412248222601519786w; 15423244248581074061w;
   4693683877966584665w; 2979970050229333266w;
   2367809319134115894w; 17775347306783131310w;
   937092411323486190w; 6417070481814181716w;
   11959835690574232440w; 14711402965514254676w;
   16332457409098339310w; 15312571225241977172w;
   854683622152836984w; 3711726276654127290w;
   17649640976689659352w; 12725883592253819626w;
   16777490200156268280w; 8074066349985402230w;
   15423713813742829784w; 10613510774037794430w;
   15857837336036454426w; 12841202932919071934w;
   12652722985752908164w; 11206062018208155614w;
   4745721320839806062w; 1053650428198676958w;
   10221769600090098682w; 2165114526758399364w;
   11972070538663730142w; 2461066652372334702w;
   1819658948654251486w; 1790178055073963224w;
   11800847613226102854w; 18024681988651297188w;
   14100921363274666560w; 7872270398641818532w;
   5519015785274262820w; 3916759253904436992w;
   6129945407386091930w; 16644305404078383218w;
   324201088869523219w; 3324818496222187932w;
   17799125046764771516w]
End

Definition bounded_case16594_cell220_native_trace_expected_def:
  bounded_case16594_cell220_native_trace_expected (index:num) =
    ((if index = 0 then 4587492636500049637w
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
      else if index = 23 then 10651523648652402811w
      else if index = 24 then 10054597010633458258w
      else if index = 25 then 1018512145506903514w
      else if index = 26 then 16287687825803962358w
      else if index = 27 then 7667997071382872658w
      else if index = 28 then 16168816397966661544w
      else if index = 29 then 12720168373343073252w
      else if index = 30 then 7462956093029782318w
      else if index = 31 then 17497310959134943161w
      else if index = 32 then 6929624713913816731w
      else if index = 33 then 16847630625188861213w
      else if index = 34 then 7403110393233217843w
      else if index = 35 then 6025164822557626262w
      else if index = 36 then 6335777492746222660w
      else if index = 37 then 16759711671621917740w
      else if index = 38 then 4920403094401313830w
      else if index = 39 then 8267499400347254628w
      else if index = 40 then 465812304847291112w
      else if index = 41 then 14440973196997446826w
      else if index = 42 then 10498671804887378086w
      else if index = 43 then 10640572794506303942w
      else if index = 44 then 18186846308486691550w
      else if index = 45 then 9153880128883828508w
      else if index = 46 then 12791805192486703544w
      else if index = 47 then 11315526683527727624w
      else if index = 48 then 15405313844405451804w
      else if index = 49 then 1010176378598348842w
      else if index = 50 then 10753496602137034408w
      else if index = 51 then 9089599520580898056w
      else if index = 52 then 4279396480875862702w
      else if index = 53 then 9523723042874522698w
      else if index = 54 then 3474537775042096572w
      else if index = 55 then 2505175418774348072w
      else if index = 56 then 1839396860331180252w
      else if index = 57 then 16858351101387425950w
      else if index = 58 then 10133729344031253212w
      else if index = 59 then 855104442213123320w
      else if index = 60 then 10464311033489390888w
      else if index = 61 then 2605405380786754780w
      else if index = 62 then 14573696432919954590w
      else if index = 63 then 10899737864486827740w
      else if index = 64 then 10870256970906539478w
      else if index = 65 then 1653300046247542762w
      else if index = 66 then 8947038794235998168w
      else if index = 67 then 2776523136995267111w
      else if index = 68 then 6871811657073848511w
      else if index = 69 then 3694243263661355739w
      else if index = 70 then 12887580404593530052w
      else if index = 71 then 11443962047018652196w
      else if index = 72 then 7995314022395063904w
      else if index = 73 then 4225899424839336519w
      else if index = 74 then 16401182000246996396w
      else if index = 75 then 9862838794546616563w
      else if index = 76 then 7871136105358742811w
      else if index = 77 then 12711576855187026067w
      else if index = 78 then 5255607475857024541w
      else if index = 79 then 14668331790602081837w
      else if index = 80 then 8512861789039848131w
      else if index = 81 then 4921197773920091059w
      else if index = 82 then 10468932450752814346w
      else if index = 83 then 2589535697542516693w
      else if index = 84 then 1966025707424196507w
      else if index = 85 then 16537266384907153199w
      else if index = 86 then 13057074369396512679w
      else if index = 87 then 15199974278581321271w
      else if index = 88 then 17342730850555103049w
      else if index = 89 then 2419167879759740837w
      else if index = 90 then 6775212119654137089w
      else if index = 91 then 8752356191679132573w
      else if index = 92 then 12803962799581581227w
      else if index = 93 then 4100538949410715177w
      else if index = 94 then 4549284956707307521w
      else if index = 95 then 18185825990711823783w
      else if index = 96 then 4983408479000932163w
      else if index = 97 then 11548644536024685481w
      else if index = 98 then 10694026140445622613w
      else if index = 99 then 9913503621313769161w
      else if index = 100 then 12318036537513835415w
      else if index = 101 then 18207836105013842121w
      else if index = 102 then 8929211203195712229w
      else if index = 103 then 206417681451113813w
      else if index = 104 then 10679512141769343689w
      else if index = 105 then 10033381869046364055w
      else if index = 106 then 527100551759865033w
      else if index = 107 then 497619658179576771w
      else if index = 108 then 9842150767918817303w
      else if index = 109 then 5065894727436180105w
      else if index = 110 then 2702220874556142864w
      else if index = 111 then 13977760469928138668w
      else if index = 112 then 10800192076515645896w
      else if index = 113 then 315620935305557264w
      else if index = 114 then 10681320648678345082w
      else if index = 115 then 7232672624054756790w
      else if index = 116 then 5729898604179027788w
      else if index = 117 then 14855425604307351867w
      else if index = 118 then 16292568941209448489w
      else if index = 119 then 4018758452252969119w
      else if index = 120 then 7183233820776802340w
      else if index = 121 then 5171897958759847662w
      else if index = 122 then 519013711561010359w
      else if index = 123 then 3546539783581751763w
      else if index = 124 then 1412248222601519786w
      else if index = 125 then 15423244248581074061w
      else if index = 126 then 4693683877966584665w
      else if index = 127 then 2979970050229333266w
      else if index = 128 then 2367809319134115894w
      else if index = 129 then 17775347306783131310w
      else if index = 130 then 937092411323486190w
      else if index = 131 then 6417070481814181716w
      else if index = 132 then 11959835690574232440w
      else if index = 133 then 14711402965514254676w
      else if index = 134 then 16332457409098339310w
      else if index = 135 then 15312571225241977172w
      else if index = 136 then 854683622152836984w
      else if index = 137 then 3711726276654127290w
      else if index = 138 then 17649640976689659352w
      else if index = 139 then 12725883592253819626w
      else if index = 140 then 16777490200156268280w
      else if index = 141 then 8074066349985402230w
      else if index = 142 then 15423713813742829784w
      else if index = 143 then 10613510774037794430w
      else if index = 144 then 15857837336036454426w
      else if index = 145 then 12841202932919071934w
      else if index = 146 then 12652722985752908164w
      else if index = 147 then 11206062018208155614w
      else if index = 148 then 4745721320839806062w
      else if index = 149 then 1053650428198676958w
      else if index = 150 then 10221769600090098682w
      else if index = 151 then 2165114526758399364w
      else if index = 152 then 11972070538663730142w
      else if index = 153 then 2461066652372334702w
      else if index = 154 then 1819658948654251486w
      else if index = 155 then 1790178055073963224w
      else if index = 156 then 11800847613226102854w
      else if index = 157 then 18024681988651297188w
      else if index = 158 then 14100921363274666560w
      else if index = 159 then 7872270398641818532w
      else if index = 160 then 5519015785274262820w
      else if index = 161 then 3916759253904436992w
      else if index = 162 then 6129945407386091930w
      else if index = 163 then 16644305404078383218w
      else if index = 164 then 324201088869523219w
      else if index = 165 then 3324818496222187932w
      else if index = 166 then 17799125046764771516w
      else 0w) : word64)
End

Definition bounded_case16594_cell220_trace_run_def:
  bounded_case16594_cell220_trace_run (radii:word64 list)
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
             if result_domain ∧ bounded_signed64_strict_negative
               (bounded_interval64_upper result_value_bound)
             then (0w:word8) else 250w
         | ([_],[]) => 249w
         | (_,[]) => 248w
         | _ => 247w)
    | instruction::rest =>
        let expected =
          bounded_case16594_cell220_native_trace_expected index in
        case bounded_analytic64_program_step radii center_environment
          box_environment instruction state of
        | NONE => (n2w (SUC index):word8)
        | SOME next =>
            if bounded_taylor64_stack_trace_hash (FST next) = expected then
              bounded_case16594_cell220_trace_run radii center_environment
                box_environment rest next (SUC index)
            else (n2w (SUC index):word8)
End

Definition bounded_packed_chars_case16594_cell_at_def:
  bounded_packed_chars_case16594_cell_at 0 bytes =
    (case bounded_packed_chars_case16594_cell bytes of
     | NONE => NONE
     | SOME (cell,rest) => SOME cell) ∧
  bounded_packed_chars_case16594_cell_at (SUC index) bytes =
    case bounded_packed_chars_case16594_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        bounded_packed_chars_case16594_cell_at index rest
End

Definition bounded_case16594_cell220_state_trace_status_def:
  bounded_case16594_cell220_state_trace_status
      ((box_environment,center_environment,radii),certificates) =
    bounded_case16594_cell220_trace_run radii center_environment
      box_environment bounded_case16594_prepared_program ([],certificates)
      0
End

Definition bounded_packed_chars_case16594_cell220_state_trace_status_def:
  bounded_packed_chars_case16594_cell220_state_trace_status bytes =
    case bounded_packed_chars_case16594_header bytes of
    | NONE => (252w:word8)
    | SOME rest =>
      case bounded_packed_chars_case16594_cell_at 220 rest of
      | NONE => (253w:word8)
      | SOME cell => bounded_case16594_cell220_state_trace_status cell
End

Theorem bounded_case16594_cell220_native_trace_hash_count:
  LENGTH (bounded_case16594_cell220_native_trace_hashes ()) = 167
Proof
  EVAL_TAC
QED

val _ = export_theory ();
