(* Version 1
   TODO: 1. Consider abbreviation !!


   SE Study: try different options under fixed 16K context window

   1. Ways of including definition dependencies:
      - local theory first?
      - local session first?
      - mixture of above two?
      - uniformally? (the current version)
      in total ~5 models

   2. use of hierarchical natural lang explanation?
      no, on constants, on constants + premises, or constants + premises + goals?
      in total 4 x (2 best of the 1's 5) = 8 models?
      also measure the cost of generating the natural lang explanation!

   3 is not very interesting?
   3. Add constants' theory name or not?
      Add theory dependencies or not?
      no theory vs constant theory vs. constant theory + dependecies (depth: 2, 4)
      Ways of annotation: all separated?
      in total 4 models.   
 *)

signature CONTEXT_INFO = sig

type buffer = string list Unsynchronized.ref
val content_of : buffer -> string
val put : buffer -> string -> unit
val mk_buffer: unit -> buffer

val put_record : Proof.context -> buffer -> string -> unit
val put_ADT : Proof.context -> buffer -> string -> unit
val put_syntax : Proof.context -> buffer -> string -> unit

datatype ctxt_info = Record of string
                   | ADT of string
                   | Fact of term
                   | Class of string
                   | Syntax of string

val defctxt_of : Proof.context -> term -> ctxt_info list
val put_defctxt : Proof.context -> buffer -> ctxt_info -> unit
val defctxt_string_of : Proof.context -> term -> string

end

structure Context_Info : CONTEXT_INFO = struct

type buffer = string list Unsynchronized.ref
fun mk_buffer () = Unsynchronized.ref []
fun put buf s = buf := s :: !buf
fun intercalate buf sep lst gen = fold_index (fn (i,x) => fn () => (
      (if i = 0 then () else put buf sep);
      gen i x
    )) lst ()
fun content_of buf = String.concat (rev(!buf))

val WELLKNOWN = ["Pure", "HOL", "Groups", "Lattices", "Boolean_Algebras", "Set", "Fun", "Complete_Lattices",
  "Inductive", "Rings", "Typedef", "Nat", "Fields", "Meson", "Product_Type", "Complete_Partial_Order",
  "Sum_Type", "Relation", "Finite_Set", "Transitive_Closure", "Wellfounded", "Fun_Def_Base",
  "Hilbert_Choice", "ATP", "Metis", "Wfrec", "Order_Relation", "Num", "Power", "Equiv_Relations",
  "Lifting", "Lifting_Set", "Option", "Lattices_Big", "Partial_Function", "Fun_Def", "Quotient",
  "Int", "Divides", "SMT", "List", "Factorial", "Enum", "String", "Orderings"]

fun is_wellknown name =
  let val qualifier = hd (Long_Name.explode name)
   in member (op =) WELLKNOWN qualifier
  end

fun def_of ctxt name =
  case try (Proof_Context.get_fact ctxt) (Facts.Named ((name ^ "_def", Position.none), NONE))
    of SOME ret => ret
     | NONE =>
  try (Proof_Context.get_fact ctxt) (Facts.Named ((name ^ ".simps", Position.none), NONE))
    |> the_default []

fun put_sort buf [] = put buf "{}"
  | put_sort buf [s] = put buf s
  | put_sort buf sort = (
      put buf "{";
      intercalate buf ", " sort (K (put buf));
      put buf "}")
fun put_sort' _ [] gen = gen ()
  | put_sort' _ \<^sort>\<open>type\<close> gen = gen ()
  | put_sort' buf sort gen = (
      put buf "(";
      gen ();
      put buf " :: ";
      put_sort buf sort;
      put buf ")")

val const_prefix = "\<^const>"
fun extern_name ctxt =
  let val space = Consts.space_of (Proof_Context.consts_of ctxt)
      val qualifier = Context.theory_base_name (Proof_Context.theory_of ctxt) ^ "."
   in fn name =>
    let val ret = Name_Space.extern ctxt space name
     in if String.isPrefix qualifier ret orelse String.isPrefix "??." ret
      then Long_Name.base_name name
      else ret
    end
  end

fun extern_name_T ctxt =
  let val space = Proof_Context.type_space ctxt
      val qualifier = Context.theory_base_name (Proof_Context.theory_of ctxt) ^ "."
   in fn name =>
    let val ret = Name_Space.extern ctxt space name
        val _ = if name = "Product_Type.prod" then () else ()
     in if String.isPrefix qualifier ret orelse String.isPrefix "??." ret
      then Long_Name.base_name name
      else ret
    end
  end

fun string_of_term ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks false
     in Syntax.pretty_term ctxt'
     #> Pretty.string_of_ops (Pretty.output_ops (SOME 100000))
     #> REPL.trim_makrup
    end
fun put_term ctxt =
  let val sot = string_of_term ctxt
      fun print buf term =
            put buf ( sot term (*
                   |> String.fields (fn #"\n" => true | _ => false)
                   |> String.concatWith " " *) )
   in print
  end

(*
fun put_type ctxt buf =
  let val extern = extern_name_T ctxt
      fun put_ty (Type(name, [])) = put buf (extern name)
        | put_ty (Type(name, args)) = (
            put buf "(";
            intercalate buf ", " args (K put_ty);
            put buf ") ";
            put buf (extern name))
        | put_ty (TFree(name, sort)) = put_sort' buf sort (fn () => put buf name)
        | put_ty (TVar((name, i), sort)) = put_sort' buf sort (fn () => (
            (if Config.get ctxt Printer.show_question_marks then put buf "?" else ());
            put buf name;
            (if i = 0 then () else (put buf "."; put buf (string_of_int i)))
            ))
   in put_ty
  end
*)

fun string_of_typ ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks false
     in Syntax.pretty_typ ctxt'
     #> Pretty.string_of_ops (Pretty.output_ops (SOME 100000))
     #> REPL.trim_makrup
    end
fun put_type ctxt buf typ = put buf (string_of_typ ctxt typ)

(* Isabelle2025-2: Printer.prtabs is abstract, so general/outfix mixfix can no
   longer be enumerated from it. We recover a constant's notation by combining the
   three still-precise queries (get_infix/prefix/binder) with a print-and-compare
   probe: render `c` applied to i dummy args; a pure prefix application always
   renders as "head _ _ ... _", so any deviation reveals a real mixfix at arity i.
   Arity 0 is judged by whether the bare render is still the plain (possibly
   qualified) const name. This reproduces every notation class the old concrete
   `Syntax.prtabs` enumeration produced (its remaining blind spot, type-conditional
   glyphs like bot's {}, was invisible to the old approach too). *)
fun analyse_syntax ctxt =
  let val prtabs = Syntax.prtabs (Proof_Context.syntax_of ctxt)
      val thy = Proof_Context.theory_of ctxt
      val sot = string_of_term ctxt
      fun app_shape i s =
            (case String.tokens Char.isSpace s
               of t :: args => t <> "" andalso length args = i
                               andalso forall (fn a => a = "_") args
                | [] => false)
      fun is_plain_ident s =
            s <> "" andalso
            List.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'" orelse c = #".")
                     (String.explode s)
   in fn name =>
      let val key = const_prefix ^ name
          val infx  = Printer.get_infix  prtabs key
          val prefx = Printer.get_prefix prtabs key
          val bindr = Printer.get_binder prtabs key
          val (arity, templates) =
            case try (Sign.the_const_type thy) name
              of NONE => (0, [])
               | SOME T =>
                  let val N = length (fst (Term.strip_type T))
                      val positive = map_filter (fn i =>
                            let val s = sot (Term.list_comb (Const (name, T), replicate i Term.dummy))
                             in if app_shape i s then NONE else SOME (i, s) end)
                          (1 upto N)
                      (* arity-0: only for genuinely nullary consts -- an infix/prefix/binder
                         renders unapplied as its operator-section form ((+), (!), ...), which is
                         already emitted precisely below; also drop schematic type-var leaks such
                         as "'a0" for numerals. *)
                      val nullary =
                        if is_some infx orelse is_some prefx orelse is_some bindr then []
                        else let val s0 = sot (Const (name, T))
                              in if (is_plain_ident s0 andalso
                                     Long_Name.base_name s0 = Long_Name.base_name name)
                                    orelse String.isPrefix "'" s0
                                 then [] else [(0, s0)] end
                   in (N, nullary @ positive) end
       in {infx = infx, prefx = prefx, bindr = bindr, arity = arity, templates = templates,
           has = is_some infx orelse is_some prefx orelse is_some bindr
                 orelse not (null templates)}
      end
  end

fun has_syntax ctxt = #has o analyse_syntax ctxt

fun put_syntax ctxt =
  let val analyse = analyse_syntax ctxt
      val extern = extern_name ctxt
      fun pp buf name =
        let val {infx, prefx, arity, templates, ...} = analyse name
            val xname = extern name
            fun emit body = (put buf ("notation " ^ xname ^ body ^ "\n\n\n"))
         in (case infx
               of SOME {assoc, delim, pri} =>
                    emit ((case assoc of Printer.Left_Assoc  => " infixl "
                                       | Printer.Right_Assoc => " infixr "
                                       | Printer.No_Assoc    => " infix ")
                          ^ string_of_int pri ^ " \<open>" ^ delim ^ "\<close>")
                | NONE => ())
          ; List.app (fn (i, s) =>
              if is_some infx andalso i = 2 then ()   (* infix already emitted precisely *)
              else emit (" \<open>" ^ s ^ "\<close>")) templates
          ; (case (prefx, templates)
               of (SOME d, []) => emit (" \<open>" ^ d ^ (if arity >= 1 then " _" else "") ^ "\<close>")
                | _ => ())
        end
   in pp
  end

fun put_record ctxt buf name =
  let open Record
      val thy = Proof_Context.theory_of ctxt
      val info = Record.the_info thy name
      (* val ctxt = Config.put Printer.show_question_marks false ctxt *)
      val extern = extern_name ctxt
      val externT = extern_name_T ctxt
   in put buf "record "
    ; (case #args info
        of [] => ()
         | args => (
             put buf "("
           ; intercalate buf ", " args (fn _ => fn (name, sort) =>
                put_sort' buf sort (fn () => put buf name))
           ; put buf ") "))
    ; put buf (extern name)
    ; put buf " {"
    ; intercalate buf ", " (#fields info) (fn _ => fn (name, typ) => (
        put buf (extern name)
      ; put buf " :: "
      ; put_type ctxt buf typ ))
    ; put buf "}"
    ; (case #parent info
        of SOME (args, typ) => (
            put buf " extends ";
            put_type ctxt buf (Type (typ, args)))
         | NONE => ())
    ; put buf "\n\n\n"
  end

fun is_atomT (Type (_, [])) = true
  | is_atomT (TFree _) = true
  | is_atomT (TVar _) = true
  | is_atomT _ = false

fun put_ADT ctxt buf const_name =
  let open Ctr_Sugar
      val info = case Ctr_Sugar.ctr_sugar_of ctxt const_name
                   of SOME x => x | NONE => error "AAA"
      val bnf' = BNF_Def.bnf_of ctxt const_name
      (* val ctxt = Config.put Printer.show_question_marks false ctxt *)
      val _ = if #kind info = Record then error "should use print_record" else ()
      val num = length (#ctrs info)
      val data = #ctrs info
              ~~ (if length (#discs info) = 0
                  then List.tabulate (num, K NONE)
                  else if length (#discs info) = num
                  then map SOME (#discs info)
                  else error ("BUG put_ADT 1A" ^ Syntax.string_of_typ ctxt (#T info)))
              ~~ (if length (#selss info) = 0
                  then List.tabulate (num, K [])
                  else if length (#selss info) = num
                  then #selss info
                  else error ("BUG put_ADT 1B" ^ Syntax.string_of_typ ctxt (#T info)))
      val extern = extern_name ctxt
   in (case #kind info
         of Datatype => put buf "datatype "
          | Codatatype => put buf "codatatype "
          | Record => put buf "record "
          | Unknown => put buf "structure ")
    ; put_type ctxt buf (#T info)
    ; put buf " = "
    ; intercalate buf " | " data (fn _ => fn ((ctr, disc), sels) => 
        let val name = case ctr of Const (name, _) => name
                                 | tm => error ("BUG put_ADT 3 " ^ Syntax.string_of_term ctxt tm)
            fun args_of (Type ("fun", [T,U])) = T :: args_of U
              | args_of _ = []
            val args = args_of (Term.fastype_of ctr)
            val sels = if length sels = 0
                       then List.tabulate (length args, K NONE)
                       else if length sels = length args
                       then let fun chk (tm as (Const (cname, _))) =
                                   let val cname = Long_Name.base_name cname
                                     in if String.isPrefix "un_" cname
                                      then NONE
                                      else SOME cname
                                    end
                                  | chk _ = NONE
                         in map chk sels
                        end
                       else error ("BUG2: put_ADT " ^ Syntax.string_of_typ ctxt (#T info))
         in (case disc of SOME (Const (dname, _)) =>
                            if Long_Name.base_name dname = "is_" ^ Long_Name.base_name name
                            then ()
                            else (put buf (extern dname); put buf ": ")
                        | SOME _ => ()
                        | NONE => ())
          ; put buf (extern name)
          ; List.app (fn (typ, sel) =>
            if is_atomT typ andalso not (is_some sel)
            then (
              put buf " "
            ; put_type ctxt buf typ )
            else (
              put buf " \<open>"
            ; (case sel of SOME s => (put buf (extern s) ; put buf ": ") | NONE => ())
            ; put_type ctxt buf typ
            ; put buf "\<close>"
            )) (args ~~ sels)
        end )
  (*  ; (case bnf' of NONE => ()
          | SOME bnf =>
        let fun pp title tail term =
              case term of Const (name, _) => (put buf title; put buf (extern name); put buf tail)
                         | _ => ()
         in put buf "          " (*10 spaces*)
          ; pp "mapper: \<open>" "\<close> " (BNF_Def.map_of_bnf bnf)
          ; pp "predicate: \<open>" "\<close> " (BNF_Def.pred_of_bnf bnf)
          ; pp "relation: \<open>" "\<close> " (BNF_Def.rel_of_bnf bnf)
          ; (case map_filter (fn Const (name, _) => SOME (extern name) | _ => NONE)
                             (BNF_Def.sets_of_bnf bnf)
               of [] => ()
                | L => (
                  put buf "set: \<open>"
                ; intercalate buf "\<close> \<open>" L (K (put buf))
                ; put buf "\<close>"))
        end) *)
    ; put buf "\n\n\n"
  end


(*
fun 
*)

fun put_class ctxt00 buf locale_name =
  let val thy = Proof_Context.theory_of ctxt00
      val ctxt0 = Proof_Context.init_global thy
      val ctxt = Target_Context.context_begin_named_cmd [] (locale_name, Position.none) thy
      val put_type = put_type ctxt
      val put_term = put_term ctxt

      fun assms_conv ctm =
        let open Conv
         in case Thm.term_of ctm
         of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => arg_conv assms_conv ctm
          | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ => combination_conv (arg_conv assms_conv) assms_conv ctm
          | tm =>
            case Term.head_of tm
              of Const (name, _) =>
                  let val local_name0 =
                        if String.isSuffix "_axioms" name
                        then String.substring (name, 0, size name - 7)
                        else name
                      val items = Long_Name.explode local_name0
                      val items_len = length items
                      val local_name = if items_len >= 3 andalso nth items (items_len - 2) = "class"
                                       then Long_Name.implode ( List.take (items, items_len - 2)
                                                              @ List.drop (items, items_len - 1) )
                                       else local_name0
                      val rule =
                        if Locale.defined thy local_name
                        then try (Proof_Context.get_thm ctxt) (name ^ "_def")
                        else NONE
                   in case rule
                   of SOME rule' => try_conv (rewr_conv rule' then_conv assms_conv) ctm
                    | NONE => all_conv ctm
                  end
               | _ => all_conv ctm
        end
      fun parse (Const(\<^const_name>\<open>Trueprop\<close>, _) $ P) ret = parse P ret
        | parse (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) ret = parse A (parse B ret)
        | parse (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) ret = ret
        | parse (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ ) ret = ret
        | parse X ret = X :: ret
      val assms = Assumption.local_prems_of ctxt ctxt0
          |> map (Conv.fconv_rule assms_conv)
          |> (fn L => fold (parse o Thm.prop_of) L [])
          |> distinct (op aconv)
      val (vars, typs) = Variable.constraints_of ctxt
      val xname = Locale.extern ctxt0 locale_name
   in put buf "class "
    ; put buf xname
    ; (if Vartab.is_empty typs then () else (
        put buf "\ntypes "
      ; Vartab.fold (fn ((name, ind), sort) => fn i =>
          if ind = ~1 then (
              (if i = 0 then () else put buf " and ")
            ; put buf name
            ; put buf " :: \<open>"
            ; put_sort buf sort
            ; put buf "\<close>"
            ; i + 1
          ) else i) typs 0
      ; () ))
    ; (if Vartab.is_empty vars then () else (
        put buf "\nvariables "
      ; Vartab.fold (fn ((name, ind), typ) => fn i =>
          let
           in (if ind = ~1 then () else error "BUG put_locale")
            ; (if i = 0 then () else put buf " and ")
            ; put buf name
            ; put buf " :: \<open>"
            ; put_type buf typ
            ; put buf "\<close>"
            ; i + 1
          end) vars 0
      ; ()))
    ; (if null assms then () else (
        put buf "\nassumes "
      ; intercalate buf " and " assms (K (fn term => (
          put buf "\<open>" ;
          put_term buf term ;
          put buf "\<close>"
        )))))
    ; put buf "\n\n\n"
  end

(*
fun put_locale ctxt =
  let val thy = Proof_Context.theory_of ctxt
      val deps = Locale.dest_dependencies [] thy
      val extern = Locale.extern thy
      val params_of = Locale.params_of thy
      val put_term = put_term ctxt
      val put_type = put_type ctxt
      val hyp_spec_of = Locale.hyp_spec_of thy

      fun print buf name =
        let val xname = extern name
            val srcs = filter (fn {target,...} => target = name) deps
            val params = params_of name
            val assms = hyp_spec_of name

            fun put_element (Element.Fixes _) = ()
              | put_element (Element.Constrains _ ) = ()
              | put_element (Element.Assumes props) =
                  intercalate buf " and " (maps (map fst o snd) props) (fn _ => fn prop => (
                      put buf "\<open>"
                    ; put_term buf prop
                    ; put buf "\<close>"))
              | put_element (Element.Defines _) = ()
              | put_element (Element.Notes _) = ()
              | put_element (Element.Lazy_Notes _) = ()

         in put buf "locale "
          ; put buf xname
          ; put buf " ="
          ; List.app (fn {source, morphism, ...} =>
              let val params = params_of source
                            |> map (apfst (`(Morphism.term morphism) o Free))
               in put buf " "
                ; put buf (extern source)
                ; (if forall (fn ((new, origin), _) => new aconv origin) params
                   then ()
                   else List.app (fn ((new, _), mixfix) => 
                     let
                      in put buf " \<open>"
                       ; put_term buf new
                       ; put buf "\<close>"
                     end ) params )
                ; put buf " +"
              end) srcs
          ; (if null params then ()
            else (
              put buf " for "
            ; intercalate buf " and " params (fn _ => fn ((name, typ), mixfix) =>
                let
                 in put buf name
                  ; put buf " :: \<open>"
                  ; put_type buf typ
                  ; put buf "\<close>"
                end )))
          ; (if null assms then ()
            else (
              put buf " assumes "
            ; intercalate buf " and " assms (K put_element)))
          ; put buf "\n"
        end
   in print
  end
*)

datatype ctxt_info = Record of string
                   | ADT of string
                   | Fact of term
                   | Class of string
                   | Syntax of string

fun ctxt_info_eq (Record a, Record b) = (a = b)
  | ctxt_info_eq (ADT a, ADT b) = (a = b)
  | ctxt_info_eq (Fact a, Fact b) = a aconv b
  | ctxt_info_eq (Syntax a, Syntax b) = (a = b)
  | ctxt_info_eq (Class a, Class b) = (a = b)
  | ctxt_info_eq _ = false

fun weak_ord_ctxt_info (Syntax _, Syntax _) = EQUAL
  | weak_ord_ctxt_info (Syntax _, _) = LESS
  | weak_ord_ctxt_info (_, Syntax _) = GREATER
  | weak_ord_ctxt_info (Class _, Class _) = EQUAL
  | weak_ord_ctxt_info (Class _, _) = LESS
  | weak_ord_ctxt_info (_, Class _) = GREATER
  | weak_ord_ctxt_info (Fact _, Fact _) = EQUAL
  | weak_ord_ctxt_info (Fact _, _) = GREATER
  | weak_ord_ctxt_info (_, Fact _) = LESS
  | weak_ord_ctxt_info _ = EQUAL

fun fold_atom_typs f (T as Type (_, Ts)) = f T #> fold (fold_atom_typs f) Ts
  | fold_atom_typs f T = f T;

fun defctxt_of ctxt =
  let val has_syntax = has_syntax ctxt
      fun gen (queue,rets,ret_len) term0 =
  let val term = singleton (Syntax.uncheck_terms ctxt) term0
      fun consts_of term =
            Term.fold_aterms (
              fn Const (name, _) => if is_wellknown name then I else insert (op =) name
               | _ => I) term []
   (* fun types_of term =
            Term.fold_aterms (Term.fold_types (Term.fold_atyps (
              fn Type (name, _) => insert (op =) name
               | _ => I
            ))) term [] *)
      fun classes_of term =
            Term.fold_aterms (Term.fold_types (Term.fold_atyps (
              let val act = fold (fn name => if is_wellknown name then I else insert (op =) name)
               in fn TFree (_, sort) => act sort
                   | TVar  (_, sort) => act sort
                   | _ => I
              end
            ))) term []


      fun facts_of consts =
            maps (def_of ctxt) consts
         |> map Thm.prop_of

      val thy = Proof_Context.theory_of ctxt
      fun is_related_to_record const =
        let val name = Long_Name.qualifier const
         in Record.get_info thy name
         |> Option.map (K name)
        end

      fun is_related_to_ADT const =
        let val name = Long_Name.qualifier const
         in Ctr_Sugar.ctr_sugar_of ctxt name
         |> Option.map (K name)
        end

      fun is_related_to_locale const =
        let val name = Long_Name.qualifier const
         in if Locale.defined thy name
          then SOME name
          else NONE
        end

      fun get_fact const =
            let val consts = [const]
                val facts1 = facts_of consts |> distinct (op aconv) |> remove (op aconv) term
                (* val consts2 = distinct (op =) (maps consts_of facts1)
                val facts2 = facts1 @ facts_of consts2 |> distinct (op aconv) |> remove (op aconv) term *)
             in map Fact facts1
            end
      val const_deps = fold_rev (fn const =>
               (if not (is_wellknown const) andalso has_syntax const
                then insert ctxt_info_eq (Syntax const)
                else I) #>
               (case is_related_to_record const
                  of SOME const => insert ctxt_info_eq (Record const)
                   | NONE => (
                case is_related_to_ADT const
                  of SOME const => insert ctxt_info_eq (ADT const)
                   | NONE => fold_rev (insert ctxt_info_eq) (get_fact const)
               ) (* @ (
                case is_related_to_locale const
                  of SOME l => [Class l]
                   | NONE => []
               ) *) )) (consts_of term) []
      val class_deps = fold_rev (fn class =>
                if Locale.defined thy class
                then insert ctxt_info_eq (Class class)
                else I
              ) (classes_of term) []
      val ret = class_deps @ const_deps
             |> distinct ctxt_info_eq
             |> filter_out (fn x => exists (fn y => member (op ctxt_info_eq) y x) rets)
             |> sort weak_ord_ctxt_info
      val rets = ret :: rets
      val ret_len = ret_len + length ret
   in if ret_len >= 300
    then flat (rev rets)
    else let val queue = fold (
                fn Fact term => Queue.enqueue term
                 | _ => I
              ) ret queue
      in if Queue.is_empty queue
      then flat (rev rets)
      else let val (next, queue) = Queue.dequeue queue
        in gen (queue,rets,ret_len) next
       end
     end

(* if lev <= 0
    then ret
    else let
      in fold (
            fn Fact term => (fn data as (ret, num) =>
                if num >= 300 then data
                else let val new = gen (lev-1) term
                                |> filter_out (fn x => exists (fn y => member (op ctxt_info_eq) y x) ret)
                  in (new::ret, num + length new)
                end)
             | _ => I
          ) ret ([ret], length ret)
      |> fst |> rev |> flat
      |> distinct ctxt_info_eq
      |> sort weak_ord_ctxt_info
     end *)
  end
   in gen (Queue.empty, [], 0)
  end

fun put_defctxt ctxt  =
  let val put_syntax = put_syntax ctxt
      val put_term = put_term ctxt
      val put_class = put_class ctxt
      fun print buf (Record info) = (try (put_record ctxt buf) info; ())
        | print buf (ADT info) = (try (put_ADT ctxt buf) info; ())
        | print buf (Fact expr) =
            let val ([expr'], _) = Variable.import_terms true [expr] ctxt
             in put buf "fact \<open>"
              ; put_term buf expr'
              ; put buf "\<close>\n\n\n"
            end
        | print buf (Syntax synt) = (try (put_syntax buf) synt; ())
        | print buf (Class l) = (try (put_class buf) l; ())
   in fn buf => (
      put buf "theory "
    ; put buf (Context.theory_long_name (Proof_Context.theory_of ctxt))
    ; put buf "\n\n\n"
    ; print buf )
  end


fun defctxt_string_of ctxt =
  let val put_defctxt = put_defctxt ctxt
      val defctxt_of = defctxt_of ctxt
   in fn term =>
    let val buf = mk_buffer ()
        val dc = defctxt_of term
     in List.app (put_defctxt buf) dc
      ; content_of buf
    end
  end

end