signature INFO_VC = sig

type number = int
type statistics = {
  opr: number Unsynchronized.ref Symtab.table (*opr name*) Unsynchronized.ref Symtab.table (*category*),
  total_opr: number Unsynchronized.ref Symtab.table (*opr name*),
  quantifier: number,
  (* size: number, (*number of AST node*) *)
  atom: number, (*number of constant & variables*)
  depth: number,
  non_linear: number Unsynchronized.ref Symtab.table,
  symbol: Symtab.set,
  dependent_thy: string list Symtab.table
}
val info : Proof.state -> statistics

val REPL_App : REPL_Server.App

end

structure Info_VC : INFO_VC = struct

type number = int
type statistics = {
  opr: number Unsynchronized.ref Symtab.table (*opr name*) Unsynchronized.ref Symtab.table (*category*),
  total_opr: number Unsynchronized.ref Symtab.table (*opr name*),
  quantifier: number,
  (* size: number, (*number of AST node*) *)
  atom: number, (*number of constant & variables*)
  depth: number,
  non_linear: number Unsynchronized.ref Symtab.table,
  symbol: Symtab.set,
  dependent_thy: string list Symtab.table
}

fun max a b = if a >= b then a else b

val empty_st : statistics = {
    opr = Symtab.empty,
    total_opr = Symtab.empty,
    quantifier = 0,
    atom = 0,
    depth = 0,
    non_linear = Symtab.empty,
    symbol = Symtab.empty,
    dependent_thy = Symtab.empty
  }

fun merge_st st1 st2 =
  { opr = Symtab.join (K (fn (ta,tb) =>
              Unsynchronized.ref (Symtab.join (K (fn (a,b) => Unsynchronized.ref (!a + !b))) (!ta,!tb))
            )) (#opr st1, #opr st2),
    total_opr = Symtab.join (K (fn (a,b) => Unsynchronized.ref (!a + !b)))
                            (#total_opr st1, #total_opr st2),
    quantifier = #quantifier st1 + #quantifier st2,
    atom = #atom st1 + #atom st2,
    depth = max (#depth st1) (#depth st2),
    non_linear = Symtab.join (K (fn (a,b) => Unsynchronized.ref (!a + !b)))
                      (#non_linear st1, #non_linear st2),
    symbol = Symtab.join (K fst) (#symbol st1, #symbol st2),
    dependent_thy = Symtab.join (K (merge (op =))) (#dependent_thy st1, #dependent_thy st2)
  }

val known_thy_names = Thy_Info.get_names ()
        |> map Long_Name.base_name
        |> Symtab.make_set

val type_classification = Symtab.make_distinct
  [ (\<^type_name>\<open>int\<close>, "int"),
    (\<^type_name>\<open>real\<close>, "float"),
    (\<^type_name>\<open>udouble\<close>, "float"),
    (\<^type_name>\<open>usingle\<close>, "float"),
    (\<^type_name>\<open>list\<close>, "list"),
    (\<^type_name>\<open>word\<close>, "word"),
    (\<^type_name>\<open>array31\<close>, "list"),
    (\<^type_name>\<open>array32\<close>, "list"),
    (\<^type_name>\<open>array63\<close>, "list"),
    (\<^type_name>\<open>fmap\<close>, "set"),
    (\<^type_name>\<open>multiset\<close>, "set"),
    (\<^type_name>\<open>fset\<close>, "set"),
    (\<^type_name>\<open>Set.set\<close>, "set"),
    (\<^type_name>\<open>set\<close>, "set"),
    (\<^type_name>\<open>Memory_Memory.addr\<close>, "memory"),
    (\<^type_name>\<open>matrix_Matrix.matrix\<close>, "other"), (*matrix*)
    (\<^type_name>\<open>ieee_float_Float64.t\<close>, "float"),
    (\<^type_name>\<open>ieee_float_RoundingMode.mode\<close>, "float"),
    (\<^type_name>\<open>hashtbl_Hashtbl.key\<close>, "set"),
    (\<^type_name>\<open>hashtbl_Hashtbl.t\<close>, "set"),
    (\<^type_name>\<open>fmap_MapImpInt.t\<close>, "set"),
    (\<^type_name>\<open>floating_point_SingleFormat.single\<close>, "float"),
    (\<^type_name>\<open>floating_point_Rounding.mode\<close>, "float"),
    (\<^type_name>\<open>bintree_Tree.tree\<close>, "other") (*tree*)
   ]

fun type_class (\<^Type>\<open>fun a b\<close>) = union (op =) (type_class a) (type_class b)
  | type_class (\<^Type>\<open>prod a b\<close>) = union (op =) (type_class a) (type_class b)
  | type_class (\<^Type>\<open>sum a b\<close>) = union (op =) (type_class a) (type_class b)
  | type_class (\<^Type>\<open>list \<^Type>\<open>char\<close>\<close>) = ["other"] (*string*)
  | type_class (\<^Type>\<open>list x\<close>) = insert (op =) "list" (type_class x)
  | type_class (\<^Type>\<open>option x\<close>) = type_class x
  | type_class (Type(name, args)) =
      fold (Term.fold_atyps (fn ty => union (op =) (type_class ty))) args
      ( case Symtab.lookup type_classification name
          of SOME cat => [cat]
           | NONE => let
                 val thy = Long_Name.explode name |> hd
              in if Symtab.defined known_thy_names thy
               then []
               else ["custom"]
             end )
  | type_class _ = []

fun dependent_thy_of thy =
  let val parents = Theory.parents_of thy
      val ret = Symtab.build (Symtab.update ("$this", map Context.theory_long_name parents))
      fun collect thy ret =
        let val name = Context.theory_long_name thy
         in if Symtab.defined ret name orelse Symtab.defined known_thy_names name
          then ret
          else let val parents = Theory.parents_of thy
             in Symtab.update (name, map Context.theory_long_name parents) ret
             |> fold collect parents
            end
        end
   in fold collect parents ret
  end

fun num_opr_of ctxt tm =
  let fun add i = i + 1
      fun is_arith name =
          member (op =) [\<^const_name>\<open>plus\<close>, \<^const_name>\<open>minus\<close>, \<^const_name>\<open>divide\<close>, \<^const_name>\<open>times\<close>,
                  \<^const_name>\<open>power\<close>, \<^const_name>\<open>less\<close>, \<^const_name>\<open>less_eq\<close>] name orelse
          member (op =) ["plus", "add", "lt", "gt", "le", "ge", "less", "less_eq", "greater", "greater_eq",
                "minus", "sub", "mul", "times", "div", "divide", "fma", "sqrt", "pow", "power", "fact"]
              (Long_Name.base_name name) orelse
          member (op =) ["Cbits_Cbits", "Cint_Cint", "Int"] (Long_Name.qualifier name)
      fun incr key tab =
          case Symtab.lookup tab key
            of SOME v => (v := !v + 1; tab)
             | NONE => (let val rf = Unsynchronized.ref 1
                         in Symtab.update (key, rf) tab
                        end )
      fun map_default (key, default) F tab =
          case Symtab.lookup tab key
            of SOME v => (v := F (!v); tab)
             | NONE => (let val rf = Unsynchronized.ref (F default)
                         in Symtab.update (key, rf) tab
                        end )
      val consts = Proof_Context.consts_of ctxt
      val occur = Term.fold_aterms (
          fn Const(name, ty0) =>
            let val thy = Long_Name.explode name |> hd
                val base = Long_Name.base_name name
             in
            if member (op =) ["HOL", "Fun"] thy orelse base = "p_unchanged"
            then I
            else let val ty = if member (op =) [\<^const_name>\<open>plus\<close>, \<^const_name>\<open>minus\<close>, \<^const_name>\<open>divide\<close>,
                                    \<^const_name>\<open>times\<close>, \<^const_name>\<open>power\<close>, \<^const_name>\<open>less\<close>,
                                    \<^const_name>\<open>less_eq\<close>, \<^const_name>\<open>inf\<close>, \<^const_name>\<open>sup\<close>,
                                    \<^const_name>\<open>prod\<close>] name
                              then ty0
                              else Consts.the_const_type consts name
                     val cats = type_class ty
                          |> member (op =) [\<^const_name>\<open>map_occ\<close>, \<^const_name>\<open>fun_upd\<close>] name ?
                              insert (op =) "set"
                          |> not (is_arith name) ? remove (op =) "int"
                          |> base = "load_s1_list" ? remove (op =) "float"
                       (* |> base = "p_unchanged" ? remove (op =) "float" *)
             in fold (fn cat =>
                  map_default (cat, Symtab.empty) (
                    if thy = "List" andalso cat <> "list" 
                    then I
                    else incr name)) cats
            end end
           | _ => I
        ) tm Symtab.empty
      val total_opr = Term.fold_aterms (
              fn Const(\<^const_name>\<open>Num.num.Bit1\<close>, _) => I
               | Const(\<^const_name>\<open>Num.num.Bit0\<close>, _) => I
               | Const("Num.num.One", _) => I
               | Const(name, _) => incr name
               | _ => I
            ) tm Symtab.empty
      val quantifier_num = Term.fold_aterms (
            fn Const(\<^const_name>\<open>HOL.All\<close>, _) => add
             | Const(\<^const_name>\<open>HOL.Ex\<close> , _) => add
             | _ => I ) tm 0
      val atom = Term.fold_aterms (K add) tm 0
      fun depth d (f $ x) = max (depth d f) (depth (d+1) x)
        | depth d (Abs (_, _, X)) = depth (d+1) X
        | depth d _ = d
      fun is_number (f $ x) = is_number f andalso is_number x
        | is_number (Abs _) = false
        | is_number (Free _) = false
        | is_number (Bound _) = false
        | is_number (Var _) = false
        | is_number _ = true
      fun non_linear ret (Const(name as \<^const_name>\<open>times\<close>, _) $ A $ B) = 
            if is_number A andalso is_number B then ret else incr name ret
        | non_linear ret (Const(name as \<^const_name>\<open>divide\<close>, _) $ A $ B) =
            if is_number A andalso is_number B then ret else incr name ret
        | non_linear ret (Const(name as \<^const_name>\<open>power\<close>, _) $ A $ B) =
            if is_number A andalso is_number B then ret else incr name ret
        | non_linear ret (Const(name, _) $ A $ B) =
            let val ret' =
                if member (op =) ["div","mul","pow","fma","sqrt","times","divid"]
                                 (Long_Name.base_name name)
                   andalso not (is_number A andalso is_number B)
                then incr name ret
                else ret
             in non_linear (non_linear ret' A) B
            end
        | non_linear ret (f $ x) = non_linear (non_linear ret f) x
        | non_linear ret (Abs (_, _, X)) = non_linear ret X
        | non_linear ret _ = ret
      val symbol = Term.fold_aterms (
            fn Const(name, _) => Symtab.insert_set name
             | Free(name, _) => Symtab.insert_set name
             | Var((name,_), _) => Symtab.insert_set name
             | _ => I
          ) tm Symtab.empty
   in {opr = occur, quantifier = quantifier_num, atom = atom,
       depth = depth 0 tm,
       non_linear = non_linear Symtab.empty tm,
       symbol = symbol,
       total_opr = total_opr,
       dependent_thy = dependent_thy_of (Proof_Context.theory_of ctxt) }
  end

fun info s =
  let val ctxt = Proof.context_of s
      val st0 = #goal (Proof.goal s)
          |> Thm.prems_of
          |> map (num_opr_of ctxt)
          |> (fn L => fold merge_st L empty_st)
      val st1 = Assumption.all_prems_of (Proof.context_of s)
            |> map (num_opr_of ctxt o Thm.prop_of)
            |> (fn L => fold merge_st L st0)
   in st1
  end

local open MessagePackBinIO.Unpack MessagePackBinIO.Pack in
fun pack_statistics {opr, quantifier, atom, depth, non_linear, symbol, total_opr, dependent_thy} =
      packTuple8 (packPairList (packString, packPairList (packString, packInt)),
                  packInt, packInt, packInt,
                  packPairList (packString, packInt),
                  packList packString,
                  packPairList (packString, packInt),
                  packPairList (packString, packList packString))
          ( Symtab.dest opr |> map (apsnd ((op !) #> Symtab.dest #> map (apsnd (op !)))),
            quantifier, atom, depth,
            Symtab.dest non_linear |> map (apsnd (op !)),
            Symtab.keys symbol,
            Symtab.dest total_opr |> map (apsnd (op !)),
            Symtab.dest dependent_thy )
end

fun REPL_App (_, cout, state) =
  let val _ = File.write (Path.explode "/tmp/t3") "OK11"
      val st = \<^try>\<open>info (Toplevel.proof_of state)
          catch E => (File.write (Path.explode "/tmp/t5") "bad"; raise E)\<close>
      val _ = File.write (Path.explode "/tmp/t4") "OK"
   in pack_statistics st cout
    ; BinIO.StreamIO.flushOut cout
    ; state
  end

val _ = REPL_Server.register_app "Info_VC" REPL_App

end