(******************************************************************************
 * Development export of the authenticated case-16594 cell-0 word packets.  *
 *                                                                            *
 * The emitted TSV is untrusted fixture data.  Its only purpose is to make    *
 * the exact 134-item fast certificate stream easy to reproduce in HOL Light; *
 * the frozen entry comparison and verified checker remain authoritative.     *
 ******************************************************************************)
Theory compute_boundedCase16594Cell0FastCertificateRowsExport
Ancestors
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTrace
Libs
  bossLib preamble wordsLib

fun dest_constructor expected tm =
  let
    val (head,arguments) = strip_comb tm
    val actual = fst (dest_const head)
  in
    if actual = expected then arguments
    else raise Fail ("expected " ^ expected ^ ", found " ^ actual)
  end;

fun dest_signed64 tm =
  case dest_constructor "BoundedSigned64" tm of
    [negative,magnitude] =>
      let
        val negative_text =
          if aconv negative boolSyntax.T then "1"
          else if aconv negative boolSyntax.F then "0"
          else raise Fail "nonliteral bounded-signed sign"
        val magnitude_text =
          Arbnum.toString (wordsSyntax.dest_word_literal magnitude)
      in
        (negative_text,magnitude_text)
      end
  | _ => raise Fail "malformed BoundedSigned64";

fun dest_interval64 tm =
  case dest_constructor "BoundedInterval64" tm of
    [lower,upper] =>
      let
        val (lower_negative,lower_magnitude) = dest_signed64 lower
        val (upper_negative,upper_magnitude) = dest_signed64 upper
      in
        (lower_negative,lower_magnitude,upper_negative,upper_magnitude)
      end
  | _ => raise Fail "malformed BoundedInterval64";

val packet_definition =
  compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def;
val (packets,_) = listSyntax.dest_list (rhs (concl packet_definition));
val _ =
  if List.length packets = 134 then ()
  else raise Fail "authenticated fast certificate row count is not 134";

val output_path =
  "compute_bounded_case16594_cell0_fast_certificate_rows.tsv";
val channel = TextIO.openOut output_path;
val _ = TextIO.output (channel,"CANDLE_CASE16594_CELL0_FAST_CERTIFICATES_V1\t134\t1099511627776\n");
fun write_packets _ [] = ()
  | write_packets index (packet::remaining) =
      let
        val (ln,lm,un,um) = dest_interval64 packet
        val _ =
          TextIO.output
            (channel,
             Int.toString index ^ "\t" ^ ln ^ "\t" ^ lm ^ "\t" ^
             un ^ "\t" ^ um ^ "\n")
      in
        write_packets (index + 1) remaining
      end;
val _ = write_packets 0 packets;
val _ = TextIO.closeOut channel;

val _ = export_theory ();
