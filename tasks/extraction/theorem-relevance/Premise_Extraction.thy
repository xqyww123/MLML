theory Premise_Extraction
  imports Minilang_Translator.MS_Translator Isa_REPL.Isa_REPL "HOL-Library.FuncSet" Category3.Category
begin

declare [[ML_debugger, ML_print_depth = 1000, ML_exception_trace, ML_exception_debugger]]

ML_file "ac_shuffle.ML"

setup \<open>Context.theory_map (
     Theorem_Extraction.install_AC (Context.Proof \<^context>)
  #> Theorem_Extraction.remove_AC [@{const_name HOL.eq}]
)\<close>

ML_file "context_info.ML"
ML_file "sledgehammer.ML"
ML_file "extraction.ML"

(*
value \<open>(3::int)^3 \<or> 1\<close>
term even


  locale partial_magma =
  fixes OP :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ex_un_null: "\<exists>!n. \<forall>t. OP n t = n \<and> OP t n = n"
  begin

    definition null :: 'a
    where "null = (THE n. \<forall>t. OP n t = n \<and> OP t n = n)"

    lemma null_eqI:
    assumes "\<And>t. OP n t = n \<and> OP t n = n"
    shows "n = null"
      using assms null_def ex_un_null the1_equality [of "\<lambda>n. \<forall>t. OP n t = n \<and> OP t n = n"]
      by auto
    
    lemma null_is_zero [simp]:
    shows "OP null t = null" and "OP t null = null"
      using null_def ex_un_null theI' [of "\<lambda>n. \<forall>t. OP n t = n \<and> OP t n = n"]
      by auto

  end

  section "Partial Composition"

  text \<open>
    A \emph{partial composition} is formally the same thing as a partial magma,
    except that we think of the operation as an operation of ``composition'',
    and we regard elements \<open>f\<close> and \<open>g\<close> of type @{typ 'a} as \emph{composable}
    if their composition is non-null.
\<close>

  type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  locale partial_composition =
    partial_magma C
  for C :: "'a comp" (infixr "\<cdot>" 55)
  begin

    text \<open>
      An \emph{identity} is a self-composable element \<open>a\<close> such that composition of
      any other element \<open>f\<close> with \<open>a\<close> on either the left or the right results in
      \<open>f\<close> whenever the composition is defined.
\<close>

    definition ide
    where "ide a \<equiv> a \<cdot> a \<noteq> null \<and>
                   (\<forall>f. (f \<cdot> a \<noteq> null \<longrightarrow> f \<cdot> a = f) \<and> (a \<cdot> f \<noteq> null \<longrightarrow> a \<cdot> f = f))"

    text \<open>
      A \emph{domain} of an element \<open>f\<close> is an identity \<open>a\<close> for which composition of
      \<open>f\<close> with \<open>a\<close> on the right is defined.
      The notion \emph{codomain} is defined similarly, using composition on the left.
      Note that, although these definitions are completely dual, the choice of terminology
      implies that we will think of composition as being written in traditional order,
      as opposed to diagram order.  It is pretty much essential to do it this way, to maintain
      compatibility with the notation for function application once we start working with
      functors and natural transformations.
\<close>

    definition domains
    where "domains f \<equiv> {a. ide a \<and> f \<cdot> a \<noteq> null}"

    definition codomains
    where "codomains f \<equiv> {b. ide b \<and> b \<cdot> f \<noteq> null}"

    lemma domains_null:
    shows "domains null = {}"
      by (simp add: domains_def)

    lemma codomains_null:
    shows "codomains null = {}"
      by (simp add: codomains_def)

    lemma self_domain_iff_ide:
    shows "a \<in> domains a \<longleftrightarrow> ide a"
      using ide_def domains_def by auto

    lemma self_codomain_iff_ide:
    shows "a \<in> codomains a \<longleftrightarrow> ide a"
      using ide_def codomains_def by auto

    text \<open>
      An element \<open>f\<close> is an \emph{arrow} if either it has a domain or it has a codomain.
      In an arbitrary partial magma it is possible for \<open>f\<close> to have one but not the other,
      but the \<open>category\<close> locale will include assumptions to rule this out.
\<close>

    definition arr
    where "arr f \<equiv> domains f \<noteq> {} \<or> codomains f \<noteq> {}"

    lemma not_arr_null [simp]:
    shows "\<not> arr null"
      by (simp add: arr_def domains_null codomains_null)

    text \<open>
      Using the notions of domain and codomain, we can define \emph{homs}.
      The predicate @{term "in_hom f a b"} expresses ``@{term f} is an arrow from @{term a}
      to @{term b},'' and the term @{term "hom a b"} denotes the set of all such arrows.
      It is convenient to have both of these, though passing back and forth sometimes involves
      extra work.  We choose @{term "in_hom"} as the more fundamental notion.
\<close>

    definition in_hom     ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<equiv> a \<in> domains f \<and> b \<in> codomains f"

    abbreviation hom
    where "hom a b \<equiv> {f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>}"

    lemma arrI:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "arr f"
      using assms arr_def in_hom_def by auto

    lemma ide_in_hom [intro]:
    shows "ide a \<longleftrightarrow> \<guillemotleft>a : a \<rightarrow> a\<guillemotright>"
      using self_domain_iff_ide self_codomain_iff_ide in_hom_def ide_def by fastforce

    text \<open>
      Arrows @{term "f"} @{term "g"} for which the composite @{term "g \<cdot> f"} is defined
      are \emph{sequential}.
\<close>

    abbreviation seq
    where "seq g f \<equiv> arr (g \<cdot> f)"

    lemma comp_arr_ide:
    assumes "ide a" and "seq f a"
    shows "f \<cdot> a = f"
      using assms ide_in_hom ide_def not_arr_null by metis

    lemma comp_ide_arr:
    assumes "ide b" and "seq b f"
    shows "b \<cdot> f = f"
      using assms ide_in_hom ide_def not_arr_null by metis

    text \<open>
      The \emph{domain} of an arrow @{term f} is an element chosen arbitrarily from the
      set of domains of @{term f} and the \emph{codomain} of @{term f} is an element chosen
      arbitrarily from the set of codomains.
\<close>

    definition dom
    where "dom f = (if domains f \<noteq> {} then (SOME a. a \<in> domains f) else null)"

    definition cod
    where "cod f = (if codomains f \<noteq> {} then (SOME b. b \<in> codomains f) else null)"

    lemma dom_null [simp]:
    shows "dom null = null"
      by (simp add: dom_def domains_null)

    lemma cod_null [simp]:
    shows "cod null = null"
      by (simp add: cod_def codomains_null)

    lemma dom_in_domains:
    assumes "domains f \<noteq> {}"
    shows "dom f \<in> domains f"
      using assms dom_def someI [of "\<lambda>a. a \<in> domains f"] by auto

    lemma cod_in_codomains:
    assumes "codomains f \<noteq> {}"
    shows "cod f \<in> codomains f"
      using assms cod_def someI [of "\<lambda>b. b \<in> codomains f"] by auto

  end

  section "Categories"

  text\<open>
    A \emph{category} is defined to be a partial magma whose composition satisfies an
    extensionality condition, an associativity condition, and the requirement that every
    arrow have both a domain and a codomain.
    The associativity condition involves four ``matching conditions''
    (\<open>match_1\<close>, \<open>match_2\<close>, \<open>match_3\<close>, and \<open>match_4\<close>)
    which constrain the domain of definition of the composition, and a fifth condition
    (\<open>comp_assoc'\<close>) which states that the results of the two ways of composing
    three elements are equal.  In the presence of the \<open>comp_assoc'\<close> axiom
    \<open>match_4\<close> can be derived from \<open>match_3\<close> and vice versa.
\<close>

  locale category = partial_composition +
  assumes ext: "g \<cdot> f \<noteq> null \<Longrightarrow> seq g f"
  and has_domain_iff_has_codomain: "domains f \<noteq> {} \<longleftrightarrow> codomains f \<noteq> {}"
  and match_1: "\<lbrakk> seq h g; seq (h \<cdot> g) f \<rbrakk> \<Longrightarrow> seq g f"
  and match_2: "\<lbrakk> seq h (g \<cdot> f); seq g f \<rbrakk> \<Longrightarrow> seq h g"
  and match_3: "\<lbrakk> seq g f; seq h g \<rbrakk> \<Longrightarrow> seq (h \<cdot> g) f"
  and comp_assoc': "\<lbrakk> seq g f; seq h g \<rbrakk> \<Longrightarrow> (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
  begin

    text\<open>
      Associativity of composition holds unconditionally.  This was not the case in
      previous, weaker versions of this theory, and I did not notice this for some
      time after updating to the current axioms.  It is obviously an advantage that
      no additional hypotheses have to be verified in order to apply associativity,
      but a disadvantage is that this fact is now ``too readily applicable,''
      so that if it is made a default simplification it tends to get in the way of
      applying other simplifications that we would also like to be able to apply automatically.
      So, it now seems best not to make this fact a default simplification, but rather
      to invoke it explicitly where it is required.
\<close>

    lemma comp_assoc:
    shows "(h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
      by (metis comp_assoc' ex_un_null ext match_1 match_2)

    lemma match_4:
    assumes "seq g f" and "seq h g"
    shows "seq h (g \<cdot> f)"
      using assms match_3 comp_assoc by auto

    lemma domains_comp:
    assumes "seq g f"
    shows "domains (g \<cdot> f) = domains f"
    proof -
      have "domains (g \<cdot> f) = {a. ide a \<and> seq (g \<cdot> f) a}"
        using domains_def ext by auto
      also have "... = {a. ide a \<and> seq f a}"
        using assms ide_def match_1 match_3 by meson
      also have "... = domains f"
        using domains_def ext by auto
      finally show ?thesis by blast
    qed

    lemma codomains_comp:
    assumes "seq g f"
    shows "codomains (g \<cdot> f) = codomains g"
    proof -
      have "codomains (g \<cdot> f) = {b. ide b \<and> seq b (g \<cdot> f)}"
        using codomains_def ext by auto
      also have "... = {b. ide b \<and> seq b g}"
        using assms ide_def match_2 match_4 by meson
      also have "... = codomains g"
        using codomains_def ext by auto
      finally show ?thesis by blast
    qed

    lemma has_domain_iff_arr:
    shows "domains f \<noteq> {} \<longleftrightarrow> arr f"
      by (simp add: arr_def has_domain_iff_has_codomain)

    lemma has_codomain_iff_arr:
    shows "codomains f \<noteq> {} \<longleftrightarrow> arr f"
      using has_domain_iff_arr has_domain_iff_has_codomain by auto

    text\<open>
      A consequence of the category axioms is that domains and codomains, if they exist,
      are unique.
\<close>

    lemma domain_unique:
    assumes "a \<in> domains f" and "a' \<in> domains f"
    shows "a = a'"
    proof -
      have "ide a \<and> seq f a \<and> ide a' \<and> seq f a'"
        using assms domains_def ext by force
      thus ?thesis
        using match_1 ide_def not_arr_null by metis
    qed

    lemma codomain_unique:
    assumes "b \<in> codomains f" and "b' \<in> codomains f"
    shows "b = b'"
    proof -
      have "ide b \<and> seq b f \<and> ide b' \<and> seq b' f"
        using assms codomains_def ext by force
      thus ?thesis
        using match_2 ide_def not_arr_null by metis
    qed

    lemma domains_simp:
    assumes "arr f"
    shows "domains f = {dom f}"
      using assms dom_in_domains has_domain_iff_arr domain_unique by auto

    lemma codomains_simp:
    assumes "arr f"
    shows "codomains f = {cod f}"
      using assms cod_in_codomains has_codomain_iff_arr codomain_unique by auto

    lemma domains_char:
    shows "domains f = (if arr f then {dom f} else {})"
      using dom_in_domains has_domain_iff_arr domain_unique by auto

    lemma codomains_char:
    shows "codomains f = (if arr f then {cod f} else {})"
      using cod_in_codomains has_codomain_iff_arr codomain_unique by auto

    text\<open>
      A consequence of the following lemma is that the notion @{term "arr"} is redundant,
      given @{term "in_hom"}, @{term "dom"}, and @{term "cod"}.  However, I have retained it
      because I have not been able to find a set of usefully powerful simplification rules
      expressed only in terms of @{term "in_hom"} that does not result in looping in many
      situations.
\<close>

    lemma arr_iff_in_hom:
    shows "arr f \<longleftrightarrow> \<guillemotleft>f : dom f \<rightarrow> cod f\<guillemotright>"
      using cod_in_codomains dom_in_domains has_domain_iff_arr has_codomain_iff_arr in_hom_def
      by auto

    lemma in_homI [intro]:
    assumes "arr f" and "dom f = a" and "cod f = b"
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
      using assms cod_in_codomains dom_in_domains has_domain_iff_arr has_codomain_iff_arr
            in_hom_def
      by auto

    lemma in_homE [elim]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    and "arr f \<Longrightarrow> dom f = a \<Longrightarrow> cod f = b \<Longrightarrow> T"
    shows "T"
     using assms in_hom_def domains_char codomains_char has_domain_iff_arr
     by (metis empty_iff singleton_iff)

    text\<open>
      To obtain the ``only if'' direction in the next two results and in similar results later
      for composition and the application of functors and natural transformations,
      is the reason for assuming the existence of @{term null} as a special element of the
      arrow type, as opposed to, say, using option types to represent partiality.
      The presence of @{term null} allows us not only to make the ``upward'' inference that
      the domain of an arrow is again an arrow, but also to make the ``downward'' inference
      that if @{term "dom f"} is an arrow then so is @{term f}.  Similarly, we will be able
      to infer not only that if @{term f} and @{term g} are composable arrows then
      @{term "C g f"} is an arrow, but also that if @{term "C g f"} is an arrow then
      \<open>f\<close> and \<open>g\<close> are composable arrows.  These inferences allow most necessary
      facts about what terms denote arrows to be deduced automatically from minimal
      assumptions.  Typically all that is required is to assume or establish that certain
      terms denote arrows in particular homs at the point where those terms are first
      introduced, and then similar facts about related terms can be derived automatically.
      Without this feature, nearly every proof would involve many tedious additional steps
      to establish that each of the terms appearing in the proof (including all its subterms)
      in fact denote arrows.
\<close>

    lemma arr_dom_iff_arr:
    shows "arr (dom f) \<longleftrightarrow> arr f"
      using dom_def dom_in_domains has_domain_iff_arr self_domain_iff_ide domains_def
      by fastforce

    lemma arr_cod_iff_arr:
    shows "arr (cod f) \<longleftrightarrow> arr f"
      using cod_def cod_in_codomains has_codomain_iff_arr self_codomain_iff_ide codomains_def
      by fastforce

    lemma arr_dom [simp]:
    assumes "arr f"
    shows "arr (dom f)"
      using assms arr_dom_iff_arr by simp

    lemma arr_cod [simp]:
    assumes "arr f"
    shows "arr (cod f)"
      using assms arr_cod_iff_arr by simp

    lemma seqI [simp]:
    assumes "arr f" and "arr g" and "dom g = cod f"
    shows "seq g f"
    proof -
      have "ide (cod f) \<and> seq (cod f) f"
        using assms(1) has_codomain_iff_arr codomains_def cod_in_codomains ext by blast
      moreover have "ide (cod f) \<and> seq g (cod f)"
        using assms(2-3) domains_def domains_simp ext by fastforce
      ultimately show ?thesis
        using match_4 ide_def ext by metis
    qed

    text \<open>
      This version of \<open>seqI\<close> is useful as an introduction rule, but not as useful
      as a simplification, because it requires finding the intermediary term \<open>b\<close>.
      Sometimes \emph{auto} is able to do this, but other times it is more expedient
      just to invoke this rule and fill in the missing terms manually, especially
      when dealing with a chain of compositions.
    \<close>

    lemma seqI' [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "seq g f"
      using assms by fastforce

    lemma compatible_iff_seq:
    shows "domains g \<inter> codomains f \<noteq> {} \<longleftrightarrow> seq g f"
    proof
      show "domains g \<inter> codomains f \<noteq> {} \<Longrightarrow> seq g f"
        using cod_in_codomains dom_in_domains empty_iff has_domain_iff_arr has_codomain_iff_arr
              domain_unique codomain_unique
        by (metis Int_emptyI seqI)
      show "seq g f \<Longrightarrow> domains g \<inter> codomains f \<noteq> {}"
      proof -
        assume gf: "seq g f"
        have 1: "cod f \<in> codomains f"
          using gf has_domain_iff_arr domains_comp cod_in_codomains codomains_simp by blast
        have "ide (cod f) \<and> seq (cod f) f"
          using 1 codomains_def ext by auto
        hence "seq g (cod f)"
          using gf has_domain_iff_arr match_2 domains_null ide_def by metis
        thus ?thesis
          using domains_def 1 codomains_def by auto
      qed
    qed

    text\<open>
      The following is another example of a crucial ``downward'' rule that would not be possible
      without a reserved @{term null} value.
\<close>

    lemma seqE [elim]:
    assumes "seq g f"
    and "arr f \<Longrightarrow> arr g \<Longrightarrow> dom g = cod f \<Longrightarrow> T"
    shows "T"
      using assms cod_in_codomains compatible_iff_seq has_domain_iff_arr has_codomain_iff_arr
            domains_comp codomains_comp domains_char codomain_unique
      by (metis Int_emptyI singletonD)

    lemma comp_in_homI [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
    proof
      show 1: "seq g f" using assms compatible_iff_seq by blast
      show "dom (g \<cdot> f) = a"
        using assms 1 domains_comp domains_simp by blast
      show "cod (g \<cdot> f) = c"
        using assms 1 codomains_comp codomains_simp by blast
    qed

    lemma comp_in_homI' [simp]:
    assumes "arr f" and "arr g" and "dom f = a" and "cod g = c" and "dom g = cod f"
    shows "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
      using assms by auto

ML \<open>               
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> @{term \<open>\<guillemotleft>\<tau> f : F a \<rightarrow> G b\<guillemotright>\<close>}
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

    lemma comp_in_homE [elim]:
    assumes "\<guillemotleft>g \<cdot> f : a \<rightarrow> c\<guillemotright>"
    obtains b where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> c\<guillemotright>"
      using assms in_hom_def domains_comp codomains_comp
      by (metis arrI in_homI seqE)

    text \<open>
      The next two rules are useful as simplifications, but they slow down the
      simplifier too much to use them by default.  So it is necessary to guess when
      they are needed and cite them explicitly.  This is usually not too difficult.
    \<close>

    lemma comp_arr_dom:
    assumes "arr f" and "dom f = a"
    shows "f \<cdot> a = f"
      using assms dom_in_domains has_domain_iff_arr domains_def ide_def by auto

    lemma comp_cod_arr:
    assumes "arr f" and "cod f = b"
    shows "b \<cdot> f = f"
      using assms cod_in_codomains has_codomain_iff_arr ide_def codomains_def by auto

    lemma ide_char:
    shows "ide a \<longleftrightarrow> arr a \<and> dom a = a \<and> cod a = a"
      using ide_in_hom by auto

    text \<open>
      In some contexts, this rule causes the simplifier to loop, but it is too useful
      not to have as a default simplification.  In cases where it is a problem, usually
      a method like \emph{blast} or \emph{force} will succeed if this rule is cited
      explicitly.
    \<close>

    lemma ideD [simp]:
    assumes "ide a"
    shows "arr a" and "dom a = a" and "cod a = a"
      using assms ide_char by auto

    lemma ide_dom [simp]:
    assumes "arr f"
    shows "ide (dom f)"
      using assms dom_in_domains has_domain_iff_arr domains_def by auto

    lemma ide_cod [simp]:
    assumes "arr f"
    shows "ide (cod f)"
      using assms cod_in_codomains has_codomain_iff_arr codomains_def by auto

    lemma dom_eqI:
    assumes "ide a" and "seq f a"
    shows "dom f = a"
      using assms cod_in_codomains codomain_unique ide_char
      by (metis seqE)

    lemma cod_eqI:
    assumes "ide b" and "seq b f"
    shows "cod f = b"
      using assms dom_in_domains domain_unique ide_char
      by (metis seqE)

    lemma dom_eqI':
    assumes "a \<in> domains f"
    shows "a = dom f"
      using assms dom_in_domains domain_unique by blast

    lemma cod_eqI':
    assumes "a \<in> codomains f"
    shows "a = cod f"
      using assms cod_in_codomains codomain_unique by blast

    lemma ide_char':
    shows "ide a \<longleftrightarrow> arr a \<and> (dom a = a \<or> cod a = a)"
      using ide_dom ide_cod ide_char by metis

    lemma dom_dom:
    shows "dom (dom f) = dom f"
      by (metis dom_null domains_char ideD(2) ide_dom dom_def)

    lemma cod_cod:
    shows "cod (cod f) = cod f"
      by (metis arr_cod_iff_arr cod_def has_codomain_iff_arr ideD(3) ide_cod)

    lemma dom_cod:
    shows "dom (cod f) = cod f"
      by (metis arr_cod_iff_arr cod_def has_codomain_iff_arr has_domain_iff_arr ideD(2)
          ide_cod dom_def)

    lemma cod_dom:
    shows "cod (dom f) = dom f"
      by (metis cod_null has_domain_iff_arr ideD(3) ide_dom dom_def)

    lemma dom_comp [simp]:
    assumes "seq g f"
    shows "dom (g \<cdot> f) = dom f"
      using assms by (simp add: dom_def domains_comp)

    lemma cod_comp [simp]:
    assumes "seq g f"
    shows "cod (g \<cdot> f) = cod g"
      using assms by (simp add: cod_def codomains_comp)

    lemma comp_ide_self [simp]:
    assumes "ide a"
    shows "a \<cdot> a = a"
      using assms comp_arr_ide arrI by auto

    lemma ide_compE [elim]:
    assumes "ide (g \<cdot> f)"
    and "seq g f \<Longrightarrow> seq f g \<Longrightarrow> g \<cdot> f = dom f \<Longrightarrow> g \<cdot> f = cod g \<Longrightarrow> T"
    shows "T"
      using assms dom_comp cod_comp ide_char ide_in_hom
      by (metis seqE seqI)

    text \<open>
      The next two results are sometimes useful for performing manipulations at the
      head of a chain of composed arrows.  I have adopted the convention that such
      chains are canonically represented in right-associated form.  This makes it
      easy to perform manipulations at the ``tail'' of a chain, but more difficult
      to perform them at the ``head''.  These results take care of the rote manipulations
      using associativity that are needed to either permute or combine arrows at the
      head of a chain.
\<close>

    lemma comp_permute:
    assumes "f \<cdot> g = k \<cdot> l" and "seq f g" and "seq g h"
    shows "f \<cdot> g \<cdot> h = k \<cdot> l \<cdot> h"
      using assms by (metis comp_assoc)

    lemma comp_reduce:
    assumes "f \<cdot> g = k" and "seq f g" and "seq g h"
    shows "f \<cdot> g \<cdot> h = k \<cdot> h"
      using assms comp_assoc by auto

    text\<open>
      Here we define some common configurations of arrows.
      These are defined as abbreviations, because we want all ``diagrammatic'' assumptions
      in a theorem to reduce readily to a conjunction of assertions of the basic forms
      @{term "arr f"}, @{term "dom f = X"}, @{term "cod f = Y"}, and @{term "in_hom f a b"}.
\<close>

    abbreviation endo
    where "endo f \<equiv> seq f f"
     
    abbreviation antipar
    where "antipar f g \<equiv> seq g f \<and> seq f g"

    abbreviation span
    where "span f g \<equiv> arr f \<and> arr g \<and> dom f = dom g"

    abbreviation cospan
    where "cospan f g \<equiv> arr f \<and> arr g \<and> cod f = cod g"

    abbreviation par
    where "par f g \<equiv> arr f \<and> arr g \<and> dom f = dom g \<and> cod f = cod g"

  end


ML \<open>      
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> @{term \<open>\<guillemotleft>\<tau> f : F a \<rightarrow>\<^sub>B G b\<guillemotright>\<close>}
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

(*
lemma \<open>AAA\<close>
  ML_val \<open>Theorem_Extraction.read_term \<^context>
            "\<forall>w::?'a::type. nonEmpty (\<lambda>Q::?'a::type \<Rightarrow> bool. Q w \<and> (\<forall>P::?'a::type \<Rightarrow> bool. P w \<longrightarrow> Q w))"
  |> Theorem_Extraction.print_term_full_typ \<^context>\<close>

*)
(*
ML \<open>Term_Ord.term_ord\<close>

ML \<open>Theorem_Extraction.ac_shuffle 10 (Context.Proof \<^context>)
      @{term \<open>A \<or> B\<close>}
  |> map (Thm.cterm_of \<^context>)\<close>

ML \<open>Theorem_Extraction.norm_AC (Context.Proof \<^context>)
      @{term \<open>(Q::nat) + (E + (C * asd)) + D = 123 \<Longrightarrow> AAA \<Longrightarrow> asda + asd = 1 \<Longrightarrow> asad\<close>}
  |> Thm.cterm_of \<^context>\<close>
*)

(*
ML \<open>fun f () = (\<^try>\<open>Syntax.read_term \<^context> "asdqq s!" catch e => error "OK"\<close>)\<close>

term \<open>Par_Exn\<close>

term 12
ML \<open>f ()\<close>
*)

(*
locale L0 =
  fixes N :: \<open>'a :: times\<close>
  assumes AX0: "N * N = N"

locale L1 = L0 +
  fixes P :: \<open>'a :: plus\<close> ("AA")
    assumes A: "P = P"

locale L2 = L1 0 1 +
  fixes Q :: bool
  assumes B: "Q"
begin
thm AX0

definition "kkk = Q"

thm L2_def
thm L1_def
thm L1_axioms_def

end

ML \<open>
let val ctxt0 = Proof_Context.init_global \<^theory>
    val ctxt = Target_Context.context_begin_named_cmd [] ("Premise_Extraction.L2", Position.none) \<^theory>
 in Assumption.local_prems_of ctxt ctxt0
  |> map (Simplifier.rewrite_rule ctxt @{thms L2_def L2_axioms_def } )
    (* Variable.constraints_of ctxt *)
end
\<close>


ML \<open>
let val ctxt = Proof_Context.init_global \<^theory>
    
    val ctxt'= Locale.activate_declarations ("Premise_Extraction.L2", Morphism.identity) ctxt
 in Assumption.local_assms_of ctxt' ctxt
end
\<close>



fun fact where
  "fact (0::nat) = 1" |
  "fact (Suc N) = N * fact N"

thm fact.simps 

ML \<open>Thy_Info.get_names () |> List.app writeln\<close>



term store
ML \<open>Record.the_info \<^theory> "A_Aodv.state" |> #args\<close>
thm state.simps
thm store_def
thm \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton_simps(1)
term PAodv
ML \<open>Record.the_info \<^theory> \<close>

thm non_trivial_neg

thm non_trivial_neg
  
typ \<open>'a :: monoid_add\<close>
ML \<open>Locale.axioms_of \<^theory> "DBM.class.time"\<close>
typ \<open>'a :: DBM.time\<close>
thm DBM.class.time_def
thm class.time_axioms_def
ML \<open>Locale.specification_of   \<^theory> "DBM.time"\<close>
 
  
ML \<open>      
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> (Thm.prop_of @{thm non_trivial_neg})
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

term less_eq
term\<open>\<infinity>\<close>
thm dbm_lt.simps
thm dbm_lt.intros
 
ML \<open> 
let val buf = Context_Info.mk_buffer ()
    val info = Context_Info.defctxt_of \<^context> (Thm.prop_of @{thm dbm_not_lt_impl(1)})
 in List.app (Context_Info.put_defctxt \<^context> buf) info
  ; Context_Info.content_of buf |> tracing
end \<close>

term CHOICE

typ AWN.seqp
typ state
record 'a xx =
  aaa :: 'a
  bbb :: \<open>'a \<times> 'a\<close>
record yy = \<open>nat xx\<close> + zzz :: int
term zzz
term "Premise_Extraction.yy_ext"

datatype ('a,'b) test = is_Test: Test nat 'b | Test2 (tB1: \<open>'a \<times> 'b\<close>) | is_Test3: Test3
datatype (aset: 'a, sset: 's, vset: 'v) t =
   T (init: 's) (rest: "('a \<times> 's) list") ("term": "'v option")
 for
   map: map
   pred: pred
   rel: rel

term pred_test

ML \<open>Record.the_info \<^theory> "Premise_Extraction.xx" |> #args\<close>
ML \<open>Record.the_info \<^theory> "Premise_Extraction.yy" |> #parent\<close>

consts AAA :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> ("_ CC _")

term LABEL   
 
ML \<open>(the (Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test"),
       BNF_Def.bnf_of \<^context> "Premise_Extraction.test")\<close>
ML \<open>    
let val buf = Context_Info.mk_buffer ()
 in Context_Info.put_ADT \<^context> buf "Premise_Extraction.test"
  ; Context_Info.content_of buf |> tracing
end \<close>


ML \<open> 
let val buf = Context_Info.mk_buffer ()
 in Context_Info.put_record \<^context> buf "Premise_Extraction.xx"
  ; Context_Info.content_of buf
end \<close>

ML \<open>
Context_Info.defctxt_string_of \<^context> @{term \<open>Test2\<close>}
\<close>

term Nil

ML \<open>
BNF_Def.bnf_of \<^context> "Premise_Extraction.test" |> the
|> BNF_Def.map_of_bnf
\<close>

term aaa
term rreqs


term plus

class semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"
begin

sublocale add: semigroup plus
  by standard (fact add_assoc)

declare add.assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]

end





context L2 begin

end

term L2.kkk
thm L2_def

ML \<open>Locale.params_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>Locale.axioms_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>(oo)\<close>
thm L2_def

term plus
ML \<open>Axclass.get_info \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Sign.super_classes \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Axclass.get_info \<^theory> "Groups.plus"\<close>

ML \<open>
fun show_const_syntax ctxt const_name =
    let
      val syn = Proof_Context.syntax_of ctxt
      val prtabs = Syntax.prtabs syn
      val tab = the_default Symtab.empty (AList.lookup (op =) prtabs "")
      val entries = Symtab.lookup_list tab const_name
    in
      if null entries then
        "No syntax for " ^ quote const_name
      else
        const_name ^ ": " ^ @{make_string} (entries)
    end
\<close>
ML \<open>show_const_syntax \<^context> \<^const_syntax>\<open>LABEL\<close> |> tracing\<close>
ML \<open>
let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern \<^context>
    val term = (Const (\<^const_name>\<open>LABEL\<close>, dummyT) $ Term.dummy $ Term.dummy)
 in Syntax.string_of_term ctxt term
 |> tracing
end
\<close>

ML \<open>fun get_local_mixfixes (Local_Syntax.Syntax {mixfixes, ...}) = mixfixes\<close>
ML \<open>Locale .params_of \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Locale.axioms_of \<^theory> "Groups.plus"\<close>
ML \<open>Locale.pretty_locale \<^theory> false "Groups.monoid_add"\<close>
ML \<open>Locale.pretty_locale \<^theory> false "Premise_Extraction.L2"\<close>
thm class.monoid_add_def

ML \<open>Locale.hyp_spec_of \<^theory> "Premise_Extraction.L1"\<close>
ML \<open>
let val dep = Locale.dest_dependencies [] \<^theory>
    val m = filter (fn {target,...} => target = "Premise_Extraction.L2") dep
  |> hd
  |> #morphism
    val m2 = filter (fn {target,...} => target = "Premise_Extraction.L1") dep
              |> hd |> #morphism
    val eles = Locale.hyp_spec_of \<^theory> "Premise_Extraction.L1"
            |> map (Element.transform_ctxt m)
    val mm = Morphism.compose m m2
 in (* Locale.params_of \<^theory> "Premise_Extraction.L0"
  |> map (Free o #1)
  |> map (Morphism.term mm) *)
  filter (fn {target,...} => target = "Premise_Extraction.L0")  dep
(*Locale.hyp_spec_of \<^theory> "Premise_Extraction.L0"
            |> map (Element.transform_ctxt mm)*)
end
\<close>

ML \<open>Locale.axioms_of \<^theory> "Premise_Extraction.L2"
      |> map (Simplifier.rewrite_rule \<^context> (Locale.get_unfolds \<^context>))\<close>
thm L2_def
thm L1_def
ML \<open>Locale.get_unfolds \<^context>\<close>
ML \<open>Locale.hyp_spec_of \<^theory> "Groups.monoid_add"\<close>
ML \<open>Locale.params_of \<^theory> "Premise_Extraction.L2"\<close>
ML \<open>Locale.params_of \<^theory> "Groups.semigroup_add"\<close>
ML \<open>Locale.specification_of \<^theory> "Groups.plus"\<close>
ML \<open>Name_Space.markup_table\<close>
ML \<open>
 local
  val code =
    "let \n\
    \  fun symb_to_string (Printer.Arg p) = \"_[\" ^ Int.toString p ^ \"]\"\n\
    \    | symb_to_string (Printer.TypArg p) = \"T[\" ^ Int.toString p ^ \"]\"\n\
    \    | symb_to_string (Printer.String (_, s)) = quote s\n\
    \    | symb_to_string (Printer.Break n) = \"break(\" ^ Int.toString n ^ \")\"\n\
    \    | symb_to_string (Printer.Block (_, symbs)) = \n\
    \        \"{\" ^ String.concatWith \" \" (map symb_to_string symbs) ^ \"}\"\n\
    \in symb_to_string end"
in
  (* 尝试动态编译 *)
  val symb_to_string_compiled =
    ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags)
      (Input.source false code (Position.none, Position.none))
      
end;

\<close>

ML \<open>
fun get_mixfixes (Local_Syntax.Syntax {mixfixes, ...}) = mixfixes
\<close>

ML \<open>
Locale.dest_dependencies [] \<^theory>
  |> map (fn {source, target, ...} => (source, target))
\<close>

ML \<open>
Named_Target.init
\<close>

ML \<open>

fun activate_all name thy activ_elem (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Element.Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Binding.empty_atts, [(A, [])])]) | _ => I) |>
      (not (null defs) ?
        activ_elem (Element.Defines (map (fn def => (Binding.empty_atts, (def, []))) defs)));
    val activate = activate_notes activ_elem (Context.Theory thy) NONE;
  in
    roundup thy activate Morphism.identity (name, Morphism.identity) (marked, input')
  end

fun pretty_locale thy show_facts name =
  let
    val locale_ctxt = Locale.init name thy;
    fun cons_elem (elem as Element.Notes _) = show_facts ? cons elem
      | cons_elem (elem as Element.Lazy_Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      Locale.activate_all name thy cons_elem (Symtab.empty, [])
      |> snd |> rev
      |> tap consolidate_notes
      |> map force_notes;
  in
    Pretty.block (Pretty.keyword1 "locale" :: Pretty.brk 1 :: pretty_name locale_ctxt name ::
      maps (fn elem => [Pretty.fbrk, Pretty.chunks (Element.pretty_ctxt locale_ctxt elem)]) elems)
  end;
\<close>

term plus

ML \<open>
fun show_const_syntax_raw ctxt const_name =
    let
      val syn = Proof_Context.syntax_of ctxt
      val prtabs = Syntax.prtabs syn
      val tab = the_default Symtab.empty (AList.lookup (op =) prtabs "")
      val entries = Symtab.lookup_list tab const_name
    in
       entries
    end
\<close>

ML \<open>Syntax.print_syntax\<close>

ML \<open>show_const_syntax_raw \<^context> \<^const_syntax>\<open>plus\<close> \<close>

ML \<open>
let val syn = Proof_Context.syntax_of @{context}
    val prtabs = Syntax.prtabs syn
    
 in Printer.get_infix prtabs \<^const_syntax>\<open>Groups.plus_class.plus\<close>
end \<close>

ML \<open>Syntax.string_of_term \<^context> (Const(\<^const_name>\<open>Groups.plus_class.plus\<close>, dummyT)) |> tracing\<close>
ML \<open>Name_Space.names_short\<close>
ML \<open>Name_Space.extern\<close>
ML \<open>Name_Space.extern \<^context> (Consts.space_of (Proof_Context.consts_of \<^context>)) "Groups.plus_class.plus"\<close>

ML "\<^const_syntax>\<open>Groups.plus_class.plus\<close> |> String.explode"

notation



term Test
term "is_Test"
term "tA1"

ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test" |> the |> #discs |> map (Thm.cterm_of \<^context>)\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.test" |> the |> #selss\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "A_Aodv.state.state_ext" |> the |> #selss\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of \<^context> "Premise_Extraction.xx.xx_ext" |> the |> #ctrs\<close>
ML \<open>String.substring ("0123456789", 3, 2)\<close>

term "Inter"

(*
ML \<open>fun mapx F (L,x) = (map F L, F x)\<close>
ML \<open>Theorem_Extraction.ac_shuffle_goal 30 (Context.Proof \<^context>)
    ([@{term \<open>(ys::'a::type list) @ [y::'a::type] = (xs::'a::type list) @
    (zs::'a::type list)\<close>},
    @{term \<open>prefix (xs::'a::type list) ((ys::'a::type list) @ [y::'a::type])\<close>}],
  @{term \<open>(xs::'a::type list) = (ys::'a::type list) @ [y::'a::type] \<or> prefix xs ys\<close>})
  |> map (mapx (Thm.cterm_of \<^context>)) \<close>


ML \<open>Theorem_Extraction.ac_shuffle_goal 100 (Context.Proof \<^context>)
    ([@{term \<open>(xs::'a::type list) = [] \<and> B\<close>},
      @{term \<open>AAA \<or> CCC\<close>}  ],
  @{term \<open>prefix xs ((y::'a::type) # (ys::'a::type list)) = (xs = [] \<or> (\<exists>zs::'a::type list. xs = y # zs \<and> prefix zs ys))\<close>})
  |> map (mapx (Thm.cterm_of \<^context>))
  |> length  \<close>

(*
declare [[ML_print_depth = 100]]
  
ML \<open>
  Theorem_Extraction.ac_shuffle 30 (Context.Proof \<^context>)
    @{term \<open>(A \<Longrightarrow> B \<Longrightarrow> \<forall>x y z. x + (1::nat) = y + z) \<Longrightarrow> C\<close>}
  |> map (Thm.cterm_of \<^context>)
\<close>

ML \<open>
fun print_term_ ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
     in Syntax.string_of_term ctxt'
     #> REPL.trim_makrup
    end\<close>
*)
*)
*)
*)

end