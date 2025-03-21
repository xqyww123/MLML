theory Gen_AFP_Session
  imports Isa_REPL.Isa_REPL
begin

ML_file \<open>library/gen_afp_session.ML\<close>

ML \<open>let val (sessions,theoies) = sessions_dep 1 ()
     in File.write_list (Path.explode "dep1_sessions") (map (fn s => s ^ "\n") sessions)
      ; File.write_list (Path.explode "dep1_theories") (map (fn s => s ^ "\n") theoies)
    end \<close>

end