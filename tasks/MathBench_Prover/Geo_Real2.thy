theory Geo_Real2
  imports MathBench_ProverBase.MathBench_ProverBase
begin

section \<open>Real Euclidean plane @{typ \<open>real^2\<close>} as a model of IsaGeoCoq's Tarski axioms\<close>

text \<open>
  Tarskis_Geometry already proves @{term \<open>real_euclid: tarski\<close>} on @{typ \<open>real^2\<close>}
  with @{term real_euclid_C} = distance equality and @{term real_euclid_B} = linear
  interpolation.  Its axioms @{thm real_euclid.A1} \<dots> @{thm real_euclid.A11} match
  IsaGeoCoq's locale @{locale Tarski_Euclidean_2D_Continuous} one-to-one (A9 =
  upper_dim, A11 = Dedekind continuity), so the instantiation is pure plumbing:
  every IsaGeoCoq Tarski axiom is discharged by the corresponding Tarskis_Geometry
  fact.  This unlocks IsaGeoCoq's circle / circumcenter / concyclic / perpendicular
  bisector / two-circle-intersection development on @{typ \<open>real^2\<close>}.
\<close>

interpretation real2:
  Tarski_Euclidean_2D_Continuous
    "real_euclid_B :: [real^2, real^2, real^2] \<Rightarrow> bool"
    "real_euclid_C :: [real^2, real^2, real^2, real^2] \<Rightarrow> bool"
    "0 :: real^2" "axis 1 1" "axis 2 1"
proof
  show "\<forall>a b. real_euclid_C a b b a" using real_euclid.A1 by blast
next
  show "\<forall>a b p q r s. real_euclid_C a b p q \<and> real_euclid_C a b r s \<longrightarrow> real_euclid_C p q r s"
    using real_euclid.A2 by blast
next
  show "\<forall>a b c. real_euclid_C a b c c \<longrightarrow> a = b" using real_euclid.A3 by blast
next
  show "\<forall>a b c q. \<exists>x. real_euclid_B q a x \<and> real_euclid_C a x b c"
    using real_euclid.A4 by blast
next
  show "\<forall>a b c d a' b' c' d'.
          a \<noteq> b \<and> real_euclid_B a b c \<and> real_euclid_B a' b' c' \<and>
          real_euclid_C a b a' b' \<and> real_euclid_C b c b' c' \<and>
          real_euclid_C a d a' d' \<and> real_euclid_C b d b' d'
          \<longrightarrow> real_euclid_C c d c' d'"
    using real_euclid.A5 by blast
next
  show "\<forall>a b. real_euclid_B a b a \<longrightarrow> a = b" using real_euclid.A6 by blast
next
  show "\<forall>a b c p q. real_euclid_B a p c \<and> real_euclid_B b q c
          \<longrightarrow> (\<exists>x. real_euclid_B p x b \<and> real_euclid_B q x a)"
    using real_euclid.A7 by blast
next
  txt \<open>lower_dim for the chosen witnesses\<close>
  show "\<not> real_euclid_B (0::real^2) (axis 1 1) (axis 2 1) \<and>
        \<not> real_euclid_B (axis 1 1) (axis 2 1) (0::real^2) \<and>
        \<not> real_euclid_B (axis 2 1) (0::real^2) (axis 1 1)"
    by (auto simp: real_euclid_B_def vec_eq_iff axis_def)
next
  show "\<forall>A B C D T. real_euclid_B A D T \<and> real_euclid_B B D C \<and> A \<noteq> D
          \<longrightarrow> (\<exists>X Y. real_euclid_B A B X \<and> real_euclid_B A C Y \<and> real_euclid_B X T Y)"
    using real_euclid.A10 by blast
next
  show "\<forall>a b c p q. p \<noteq> q \<and> real_euclid_C a p a q \<and> real_euclid_C b p b q \<and> real_euclid_C c p c q
          \<longrightarrow> (real_euclid_B a b c \<or> real_euclid_B b c a \<or> real_euclid_B c a b)"
    using real_euclid.A9 by blast
next
  txt \<open>Dedekind continuity: A11 is over sets, IsaGeoCoq over predicates.\<close>
  show "\<forall>Alpha Beta.
          (\<exists>A. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B A X Y) \<longrightarrow>
          (\<exists>B. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B X B Y)"
  proof (intro allI impI)
    fix Alpha Beta :: "real^2 \<Rightarrow> bool"
    assume "\<exists>A. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B A X Y"
    then show "\<exists>B. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B X B Y"
      using real_euclid.A11[rule_format, of "Collect Alpha" "Collect Beta"] by auto
  qed
qed

end
