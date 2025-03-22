theory Get_Thy_Info
  imports Isa_REPL.Isa_REPL
begin

ML \<open>

fun dump () =
  let val sf = BinIO.openOut "./sessions.msgpack"
      val (sinfo, tinfo) = Lazy.force REPL_Aux.session_theory_infos
      open MessagePackBinIO.Pack

      fun pack_sinfo {deps, theories} =
          packPair (packList packString, packList packString) (deps, theories)
      val spacker = packPairList (packString, pack_sinfo) o Symtab.dest
      val _ = spacker sinfo (BinIO.getOutstream sf)
      val _ = BinIO.closeOut sf

      val tf = BinIO.openOut "./theories.msgpack"
      fun pack_header {name, imports, ...} =
          packPair (packString, packList packString) (fst name, map fst imports)
      val tpacker = packPairList (packString, packPair (pack_header, packString o Path.implode)) o Symtab.dest
      val _ = tpacker tinfo (BinIO.getOutstream tf)
      val _ = BinIO.closeOut tf
   in ()
  end

\<close>

ML \<open>dump ()\<close>

ML \<open>error "IGNORE THIS ERROR"\<close>

end