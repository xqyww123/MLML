
(*Sessions that are referenced at least M times*)
fun sessions_dep M () =
  let val (sinfo, tinfo) = Lazy.force REPL_Aux.session_theory_infos
      val sref_count = Symtab.fold (fn (_, {deps,...}) =>
              fold (fn dep => Symtab.map_default (dep, 0) (fn N => N + 1) ) deps
            ) sinfo Symtab.empty
      val sessions = Symtab.fold (fn (k, N) => fn L =>
              if N >= M
              then k :: L
              else L
            ) sref_count []

      val tref_count = Symtab.build (Symtab.fold (fn (_, {theories,...}) =>
                fold (fn theory => Symtab.update (theory, 0)) theories
            ) sinfo)
            |> Symtab.fold (fn (_, (header, _)) =>
                  fold (fn (name,_) => fn count =>
                    if Symtab.defined count name
                    then Symtab.map_entry name (fn x => x + 1) count
                    else count
                  ) (#imports header)
               ) tinfo
      val theories = Symtab.fold (fn (k, N) => fn L =>
              if N >= M
              then k :: L
              else L
            ) tref_count []
   in (Symtab.keys sinfo, theories)
  end

