signature THEOREM_EXTRACTION = sig

type constant_name = string
type AC_shuffle_max_num = int
val ac_shuffle : AC_shuffle_max_num -> Context.generic -> term -> term list

val install_AC : Context.generic -> Context.generic -> Context.generic
val install_AC_by_rewriting : thm list -> Context.generic -> Context.generic
val remove_AC : constant_name list (*oprs*) -> Context.generic -> Context.generic

type ac_shuffle = term -> term list

end

structure Theorem_Extraction : THEOREM_EXTRACTION = struct

type AC_shuffle_max_num = int

type constant_name = string
datatype AC = Assoc  of constant_name * constant_name
            | Assoc' of constant_name * constant_name
            | Comm   of constant_name
            | AssocC of constant_name * constant_name

type AC_table = AC list Symtab.table
type ac_shuffle = term -> term list

structure AC_table = Generic_Data (
  type T = AC_table
  val empty = Symtab.empty
  val merge = Symtab.join (K (uncurry (union (op =))))
)

fun mk_AC_table (ac as Assoc (N,M)) tab = tab
    |> Symtab.map_default (N, []) (insert (op =) ac)
    |> Symtab.map_default (M, []) (insert (op =) ac)
  | mk_AC_table (ac as AssocC (N,M)) tab = tab
    |> Symtab.map_default (N, []) (insert (op =) ac)
    |> Symtab.map_default (M, []) (insert (op =) ac)
  | mk_AC_table (ac as Assoc' (N,M)) tab = tab
    |> Symtab.map_default (N, []) (insert (op =) ac)
    |> Symtab.map_default (M, []) (insert (op =) ac)
  | mk_AC_table (ac as Comm N) tab = tab
    |> Symtab.map_default (N, []) (insert (op =) ac)

fun remove_AC oprs =
      AC_table.map (Symtab.map (fn _ => fn L => 
          filter_out (fn Assoc (N,M) => member (op =) oprs N andalso
                                        member (op =) oprs M
                       | Assoc'(N,M) => member (op =) oprs N andalso
                                        member (op =) oprs M
                       | Comm N => member (op =) oprs N
                       | AssocC(N,M) => member (op =) oprs N andalso
                                        member (op =) oprs M
                     ) L))


fun is_Var (Var _) = true
  | is_Var (Free _) = true
  | is_Var _ = false

fun chk_C_pair (Const(N1, _) $ A1 $ B1, Const(N2,_) $ B2 $ A2) =
      if is_Var A1 andalso is_Var B1 andalso is_Var B2 andalso is_Var A2 andalso
         N1 = N2 andalso A1 aconv A2 andalso B1 aconv B2
      then SOME (Comm N1)
      else NONE
  | chk_C_pair _ = NONE
fun chk_A_pair (Const(N1, _) $ A1 $ (Const(M1, _) $ B1 $ C1),
                Const(N2, _) $ (Const(M2, _) $ A2 $ B2) $ C2) =
      if is_Var A1 andalso is_Var B1 andalso is_Var C1 andalso
         is_Var A2 andalso is_Var B2 andalso is_Var C2 andalso
         N1 = N2 andalso M1 = M2 andalso A1 aconv A2 andalso B1 aconv B2 andalso C1 aconv C2
      then SOME (Assoc (N1, M1))
      else NONE
  | chk_A_pair (Const(N2, _) $ (Const(M2, _) $ A2 $ B2) $ C2,
                Const(N1, _) $ A1 $ (Const(M1, _) $ B1 $ C1)) =
      if is_Var A1 andalso is_Var B1 andalso is_Var C1 andalso
         is_Var A2 andalso is_Var B2 andalso is_Var C2 andalso
         N1 = N2 andalso M1 = M2 andalso A1 aconv A2 andalso B1 aconv B2 andalso C1 aconv C2
      then SOME (Assoc (N1, M1))
      else NONE
  | chk_A_pair _ = NONE
fun chk_A'_pair (Const(N1, _) $ A1 $ (Const(M1, _) $ B1 $ C1),
                 Const(M2, _) $ (Const(N2, _) $ A2 $ B2) $ C2) =
      if is_Var A1 andalso is_Var B1 andalso is_Var C1 andalso
         is_Var A2 andalso is_Var B2 andalso is_Var C2 andalso
         N1 = N2 andalso M1 = M2 andalso A1 aconv A2 andalso B1 aconv B2 andalso C1 aconv C2
      then SOME (Assoc (N1, M1))
      else NONE
  | chk_A'_pair (Const(M2, _) $ (Const(N2, _) $ A2 $ B2) $ C2,
                 Const(N1, _) $ A1 $ (Const(M1, _) $ B1 $ C1)) =
      if is_Var A1 andalso is_Var B1 andalso is_Var C1 andalso
         is_Var A2 andalso is_Var B2 andalso is_Var C2 andalso
         N1 = N2 andalso M1 = M2 andalso A1 aconv A2 andalso B1 aconv B2 andalso C1 aconv C2
      then SOME (Assoc (N1, M1))
      else NONE
  | chk_A'_pair _ = NONE
fun chk_AC_pair pair =
      case chk_C_pair pair
        of SOME ret => SOME ret
         | _ => (
      case chk_A_pair pair
        of SOME ret => SOME ret
         | _ => chk_A'_pair pair)

fun chk_AC_rule (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk_AC_rule X
  | chk_AC_rule (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ A $ B) = chk_AC_pair (A,B)
  | chk_AC_rule (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ B) = chk_AC_pair (A,B)
  | chk_AC_rule _ = NONE

fun install_AC_by_rewriting thms =
  AC_table.map (fold mk_AC_table (map_filter (chk_AC_rule o Thm.prop_of) thms))

fun install_AC ctxt =
  AC_table.map (fold mk_AC_table
    (map_filter (chk_AC_rule o Thm.prop_of)
        (maps snd (Facts.dest_all ctxt false [] (Proof_Context.facts_of (Context.proof_of ctxt))))))

fun permutations [] = [[]]
  | permutations (x :: xs) =
      let
        fun insert_all y [] = [[y]]
          | insert_all y (xs as z :: zs) =
              (y :: xs) :: map (cons z) (insert_all y zs)

        val perms = permutations xs
      in
        flat (map (insert_all x) perms)
      end

fun shuffle xs =
    let
      fun shuffle_aux [] acc = acc
        | shuffle_aux [x] acc = x :: acc
        | shuffle_aux xs acc =
            let
              val len = length xs
              val rand_idx = Random.random_range 0 (len - 1)
              val selected = nth xs rand_idx
              val remaining = nth_drop rand_idx xs
            in
              shuffle_aux remaining (selected :: acc)
            end
    in
      shuffle_aux xs []
    end

fun bounded_permutations N xs =
  if length xs <= 5
  then permutations xs
    |> take N
  else let
      fun generate_perms 0 acc = acc
        | generate_perms k acc =
            let
              val perm = shuffle xs
            in
              generate_perms (k - 1) (perm :: acc)
            end
    in
      generate_perms N []
    end

fun nth_root_ceil (x: int, n: int) : int =
    let val root = Math.pow (real x, 1.0 / real n)
     in Real.ceil root
    end

fun gen_indexes _ 0 _ = []
  | gen_indexes passed N cap =
      let val x = Random.random_range 0 (cap-1)
          fun restore ret [] = ret
            | restore ret (h :: L) =
                if h <= ret then restore (ret+1) L else restore ret L
          val L = gen_indexes (x::passed) (N-1) (cap-1)
       in restore x passed :: L
      end

(*
val alphabet = Vector.tabulate (26, fn i => Char.chr (i+97))

fun random_binding_names NUM name =
  let val size = String.size name
      fun alli 0 P = P 0
        | alli N P = P N andalso alli (N-1) P
      val can_random = size >= 1 andalso size < 4 andalso
                       Char.isAlpha (String.sub(name, 0)) andalso
                       ( alli (size-1) (fn i => Char.isDigit (String.sub(name, i+1))) orelse
                         size >= 2 andalso member (op =) [#"_", #"'"] (String.sub(name,1)) andalso
                            alli (size-2) (fn i => Char.isDigit (String.sub(name, i+2))) )
   in if can_random
    then gen_indexes [] NUM 26
      |> map (fn i =>
            let val base = Char.toString (Vector.sub (alphabet, i))
             in if size > 1
              then base ^ string_of_int (Random.random_range 0 99)
              else base
            end )
    else [name]
  end

fun random_binding_name name =
  let val size = String.size name
      fun alli 0 _ = true
        | alli N P = P (N-1) andalso alli (N-1) P
      val can_random =
             size >= 1 andalso size < 4 andalso
             Char.isAlpha (String.sub(name, 0)) andalso
             ( alli (size-1) (fn i => Char.isDigit (String.sub(name, i+1))) orelse
               size >= 2 andalso member (op =) [#"_", #"'"] (String.sub(name,1)) andalso
                  alli (size-2) (fn i => Char.isDigit (String.sub(name, i+2))) )
   in if can_random
    then let val base = Char.toString (Vector.sub (alphabet, Random.random_range 0 25))
         in if size > 1
          then base ^ string_of_int (Random.random_range 0 99)
          else base
        end
    else name
  end
*)


fun apply_AC AC_max_num table =
  let fun take_shuf AC_max_num L =
          let val len = length L
           in if len <= AC_max_num * 2
              then L
              else let
              val indexes = gen_indexes [] AC_max_num len
                         |> sort int_ord
              fun filter _ [] _ = []
                | filter j (i::is) (x::L) =
                    if j = i then x :: filter (j+1) is L
                             else filter (j+1) (i::is) L
                | filter _ _ _ = error "Impossible apply_AC.take_shuf.filter"
           in filter 0 indexes L
          end end
  fun apply AC_max_num term =
    let fun fallback term =
               case term
                 of A $ B =>
                    let val As' = apply AC_max_num A
                        val Bs' = apply AC_max_num B
                     in maps (fn A' => map (fn B' => A' $ B') Bs') As'
                     |> take_shuf AC_max_num
                    end
                  | Abs (name, typ, X) => map (fn X' => Abs (name, typ, X')) (apply AC_max_num X)
                                       |> take_shuf AC_max_num
                  | atom => [atom]
        fun apply_acs (ac :: acs) (term as (Const(N', typ) $ A' $ B')) =
              let val expansions =
                    case ac of Assoc (N,M) =>
                          let val right = case B' of Const(M', typ2) $ B $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ (Const(M', typ2) $ A' $ B) $ C]
                                            else []
                                                   | _ => []
                              val left  = case A' of Const(M', typ2) $ A $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ A $ (Const(M', typ2) $ B' $ C)]
                                            else []
                                                   | _ => []
                           in left @ right
                          end
                      | (Assoc' (M,N)) =>
                          let val right = case B' of Const(M', typ2) $ B $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ (Const(M', typ2) $ A' $ B) $ C]
                                            else []
                                                   | _ => []
                              val left  = case A' of Const(M', typ2) $ A $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ A $ (Const(M', typ2) $ B' $ C)]
                                            else []
                                                   | _ => []
                           in left @ right
                          end
                      | (Comm N) =>
                          if N = N'
                          then [Const(N', typ) $ B' $ A']
                          else []
                      | (AssocC (N,M)) =>
                          let val right = case B' of Const(M', typ2) $ B $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ C $ (Const(M', typ2) $ A' $ B)]
                                            else []
                                                   | _ => []
                              val left  = [] (*case A' of Const(M', typ2) $ A $ C =>
                                            if N' = N andalso M' = M
                                            then [Const(N', typ) $ (Const(M', typ2) $ B' $ C) $ A]
                                            else []
                                                   | _ => [] *)
                           in left @ right
                          end
               in case expansions
                    of [] => apply_acs acs term
                     |  L => maps (apply_acs acs) (term :: L)
                          |> take_shuf AC_max_num
              end
          | apply_acs _ term = fallback term
              
     in case term
     of Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) =>
          shuffle_prems term
      | (Const(N', _) $ _ $ _) =>
        let fun add_AssocC _ [] = []
              | add_AssocC origin ((x as Assoc (N,M)) :: acs) =
                  if exists (fn Comm N' => N = N' | _ => false) origin
                  then x :: insert (op =) (AssocC(N,M)) (add_AssocC origin acs)
                  else x :: add_AssocC origin acs
              | add_AssocC origin (x :: acs) = x :: add_AssocC origin acs
            val acs = the_default [] (Symtab.lookup table N')
            val acs = add_AssocC acs acs
         in apply_acs acs term
        end
      | Const (cname1, _) $ Abs (_, _, Const (cname2, _) $ Abs (_, _, _)) =>
          if cname1 = cname2 andalso
             member (op =) [\<^const_name>\<open>All\<close>] cname1
          then shuffle_quantifiers AC_max_num cname1 term
          else fallback term
    (* | Abs (name, ty, X) =>
          let val names' = random_binding_names 3 name
           in apply AC_max_num X
            |> maps (fn X' => map (fn name' => Abs (name', ty, X')) names')
            |> take_shuf AC_max_num
          end *)
      | _ => fallback term
    end
  and shuffle_prems term =
    let val prems = Logic.strip_imp_prems term
                 |> map (apply AC_max_num)
     in if null prems
        then apply AC_max_num term
        else let
        val concl = Logic.strip_imp_concl term
                 |> apply AC_max_num
        fun get_max ret [] = ret
          | get_max ret (x::L) =
              let val len = length x
               in get_max (if ret < len then len else ret) L
              end
        val max = get_max (length concl) prems
        fun pad L = if length L < max
                    then pad (L @ L)
                    else take max L
        val prems = map_transpose I (map (shuffle o pad) prems)
        val concl = pad concl
        val pairs = prems ~~ concl

        val need_permutation = length prems < AC_max_num
        val perm_num = AC_max_num div length prems + 1
     in ( if need_permutation
      then map Logic.list_implies (
              maps (fn (prem,c) =>
                    map (rpair c) (bounded_permutations perm_num prem)
              ) pairs)
      else map (Logic.list_implies o apfst shuffle) pairs)
    end end
  and shuffle_quantifiers origin_AC_max_num quantifier term =
    let fun strip_qnt ret (Const(cname, ctyp) $ Abs (vname, vtyp, X)) =
              if cname = quantifier
              then strip_qnt ((vname, vtyp, ctyp) :: ret) X
              else ret
          | strip_qnt ret _ = ret
        val vars = strip_qnt [] term
        val var_len = length vars
        val vars = map_index (fn (i, x) => (x, var_len - 1 - i)) vars
        val AC_max_num = if origin_AC_max_num > 10
                         then origin_AC_max_num div 3 + 1
                         else origin_AC_max_num
        val vars's = bounded_permutations AC_max_num vars
        val body = Term.strip_qnt_body quantifier term
     in maps (fn vars' =>
          let val residues = List.tabulate (var_len, fn i =>
                    let val k = find_index (fn (_, j) => i = j) vars'
                     in if k = ~1
                       then error "BUG: Premise_Extration.shuffle_quantifiers"
                       else Bound (var_len - 1 - k)
                    end )
              val body's = apply AC_max_num body
           in map (fn body' =>
              Term.subst_bounds (residues, body')
           |> fold_rev (fn ((vname, vty, ctyp), _) => fn X =>
                Const(quantifier, ctyp) $ Abs (vname, vty, X) ) vars'
            ) body's
          end ) vars's
     |> take_shuf origin_AC_max_num
    end
  in fn term => remove (op aconv) term (shuffle_prems term)
             |> take AC_max_num
 end

fun ac_shuffle AC_max_num ctxt = apply_AC AC_max_num (AC_table.get ctxt)

end

