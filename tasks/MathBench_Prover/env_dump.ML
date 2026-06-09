(*  Title:      env_dump.ML

Dump the "environment fingerprint" of the current theory context so it can be
compared against PutnamBench import combinations to detect divergences that
would silently change the meaning of (or break) a Putnam problem when proved
under MathBench_Prover. Three dimensions are captured:

  * constant short-name resolution  (which long const a base name resolves to)
  * type short-name resolution      (likewise for types)
  * notation                        (Syntax.print_syntax: mixfix / grammar /
                                     parse & print rules; "符号" — a subkind of
                                     syntax, distinct from name resolution)

This same file is loaded both by Env_Dump.thy (to produce the MathBench_Prover
reference) and inlined by tools/check_putnam_divergence.py (to produce the
per-import-set Putnam dumps), so both sides always run identical code.
*)

signature ENV_DUMP =
sig
  val dump_const_resolution: theory -> string -> unit
  val dump_type_resolution: theory -> string -> unit
  val dump_notation: Proof.context -> string -> unit
  val dump_all: Proof.context -> {const: string, typ: string, notation: string} -> unit
end;

structure Env_Dump : ENV_DUMP =
struct

(* For every base (short) name occurring among `long_names`, write
   "base \t winner_long_name" where winner is what the base name resolves to
   via Name_Space.intern. Base names whose winner is hidden ("??."-prefixed,
   i.e. made inaccessible by hide_const/hide_type) are skipped. *)
fun dump_resolution space long_names path =
  let
    val bases =
      fold (fn nm => Symtab.update (Long_Name.base_name nm, ())) long_names Symtab.empty
      |> Symtab.keys;
    val out = TextIO.openOut path;
    val _ =
      List.app (fn base =>
        let val winner = Name_Space.intern space base in
          if Long_Name.is_hidden winner then ()
          else TextIO.output (out, base ^ "\t" ^ winner ^ "\n")
        end) bases;
  in TextIO.closeOut out end;

fun dump_const_resolution thy path =
  let val {const_space, constants, ...} = Consts.dest (Sign.consts_of thy)
  in dump_resolution const_space (map fst constants) path end;

fun dump_type_resolution thy path =
  let
    val type_space = Sign.type_space thy;
    val type_names = map fst (Name_Space.dest_table (#types (Type.rep_tsig (Sign.tsig_of thy))));
  in dump_resolution type_space type_names path end;

(* Capture Syntax.print_syntax (which writes via Output) by temporarily
   redirecting the private writeln channel into a buffer. This is the "notation"
   (符号) dimension: mixfix grammar productions and parse/print rules. *)
fun dump_notation ctxt path =
  let
    val syn = Proof_Context.syntax_of ctxt;
    val buf = Unsynchronized.ref ([] : string list);
    val old = ! Private_Output.writeln_fn;
    val _ = Private_Output.writeln_fn := (fn ss => buf := implode ss :: ! buf);
    val res = Exn.capture Syntax.print_syntax syn;
    val _ = Private_Output.writeln_fn := old;
    val _ = Exn.release res;
    val out = TextIO.openOut path;
    val _ = TextIO.output (out, String.concatWith "\n" (rev (! buf)));
  in TextIO.closeOut out end;

fun dump_all ctxt {const, typ, notation} =
  let val thy = Proof_Context.theory_of ctxt in
    dump_const_resolution thy const;
    dump_type_resolution thy typ;
    dump_notation ctxt notation
  end;

end;
