theory Geo_Real2
  imports MathBench_ProverBase.MathBench_ProverBase
begin

section \<open>Real Euclidean plane @{typ \<open>real^2\<close>} as a model of IsaGeoCoq's Tarski axioms\<close>

text \<open>
  Tarskis_Geometry already proves the interpretation \<open>real_euclid: tarski\<close> on
  \<^typ>\<open>real^2\<close>, with \<open>real_euclid_C\<close> = distance equality and \<open>real_euclid_B\<close> =
  linear interpolation.  Its axioms \<open>real_euclid.A1\<close> \<dots> \<open>real_euclid.A11\<close> match
  IsaGeoCoq's \<^locale>\<open>Tarski_Euclidean_2D_Continuous\<close> one-to-one (A9 = upper_dim,
  A11 = Dedekind continuity).

  Directly interpreting \<^locale>\<open>Tarski_Euclidean_2D_Continuous\<close> on \<^typ>\<open>real^2\<close>
  fails in batch build with "Duplicate fact declaration": IsaGeoCoq declares the
  same leaf name in two different ancestor locales (e.g. \<open>triangle_mid_par\<close> in both
  \<^locale>\<open>Tarski_neutral_dimensionless\<close> and \<^locale>\<open>Tarski_Euclidean\<close>), and a flat
  interpretation collapses both onto \<open>real2.triangle_mid_par\<close> (6 such clashes across
  the root / Euclidean / 2D ancestors).  We sidestep this with a wrapper locale that
  re-imports the two lower ancestors under named qualifiers \<open>neu:\<close> / \<open>euc:\<close>, so the
  clashing facts separate into distinct prefixes (\<open>real2.neu.\<close> / \<open>real2.euc.\<close>) while
  everything else stays \<open>real2.\<close>.
\<close>

locale Tarski_Euclidean_2D_Continuous' =
  neu:  Tarski_neutral_dimensionless Bet Cong TPA TPB TPC +
  n2d:  Tarski_neutral_2D            Bet Cong TPA TPB TPC +
  euc:  Tarski_Euclidean             Bet Cong TPA TPB TPC +
  e2d:  Tarski_Euclidean_2D          Bet Cong TPA TPB TPC +
  Tarski_Euclidean_2D_Continuous     Bet Cong TPA TPB TPC
  for Bet Cong TPA TPB TPC

text \<open>Dedekind continuity in predicate form (IsaGeoCoq's shape), bridged from the
      set-form \<open>real_euclid.A11\<close> by instantiating the sets as \<^term>\<open>Collect Alpha\<close>.\<close>
lemma real2_continuity_pred:
  fixes Alpha Beta :: "real^2 \<Rightarrow> bool"
  assumes "\<exists>A. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B A X Y"
  shows "\<exists>B. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B X B Y"
proof -
  from assms have "\<exists>a. \<forall>x y. x \<in> Collect Alpha \<and> y \<in> Collect Beta \<longrightarrow> real_euclid_B a x y"
    by simp
  hence "\<exists>b. \<forall>x y. x \<in> Collect Alpha \<and> y \<in> Collect Beta \<longrightarrow> real_euclid_B x b y"
    using real_euclid.A11[rule_format, of "Collect Alpha" "Collect Beta"] by metis
  thus ?thesis by simp
qed

interpretation real2:
  Tarski_Euclidean_2D_Continuous'
    "real_euclid_B :: [real^2, real^2, real^2] \<Rightarrow> bool"
    "real_euclid_C :: [real^2, real^2, real^2, real^2] \<Rightarrow> bool"
    "0 :: real^2" "vector [1, 0]" "vector [0, 1]"
proof
  txt \<open>A1-A3 (congruence axioms) come via \<open>semimetric < tarski_first3\<close>, so they are
       \<open>norm_metric.A\<^sub>n\<close> facts (\<^term>\<open>real_euclid_C\<close> abbreviates \<^term>\<open>norm_metric.smC\<close>).\<close>
  show "\<forall>a b. real_euclid_C a b b a" by (rule norm_metric.A1)
next
  show "\<forall>a b p q r s. real_euclid_C a b p q \<and> real_euclid_C a b r s \<longrightarrow> real_euclid_C p q r s"
    by (rule norm_metric.A2)
next
  show "\<forall>a b c. real_euclid_C a b c c \<longrightarrow> a = b" by (rule norm_metric.A3)
next
  show "\<forall>a b c q. \<exists>x. real_euclid_B q a x \<and> real_euclid_C a x b c"
    using real_euclid.A4 by blast
next
  show "\<forall>a b c d a' b' c' d'.
          a \<noteq> b \<and> real_euclid_B a b c \<and> real_euclid_B a' b' c' \<and>
          real_euclid_C a b a' b' \<and> real_euclid_C b c b' c' \<and>
          real_euclid_C a d a' d' \<and> real_euclid_C b d b' d'
          \<longrightarrow> real_euclid_C c d c' d'"
    by (rule real_euclid.A5)
next
  show "\<forall>a b. real_euclid_B a b a \<longrightarrow> a = b" by (rule real_euclid.A6)
next
  show "\<forall>a b c p q. real_euclid_B a p c \<and> real_euclid_B b q c
          \<longrightarrow> (\<exists>x. real_euclid_B p x b \<and> real_euclid_B q x a)"
    by (rule real_euclid.A7)
next
  txt \<open>lower_dim: \<^term>\<open>0::real^2\<close>, \<^term>\<open>vector [1,0]::real^2\<close>, \<^term>\<open>vector [0,1]::real^2\<close>
       are not collinear (clean component access via @{thm vector_2}).\<close>
  show "\<not> real_euclid_B (0::real^2) (vector [1, 0]) (vector [0, 1]) \<and>
        \<not> real_euclid_B (vector [1, 0]) (vector [0, 1]) (0::real^2) \<and>
        \<not> real_euclid_B (vector [0, 1]) (0::real^2) (vector [1, 0])"
  proof (intro conjI notI)
    assume "real_euclid_B (0::real^2) (vector [1, 0]) (vector [0, 1])"
    then obtain l where "vector [1, 0] - 0 = l *\<^sub>R (vector [0, 1] - (0::real^2))"
      unfolding real_euclid_B_def by auto
    hence "(vector [1, 0] - (0::real^2)) $ 1 = (l *\<^sub>R (vector [0, 1] - 0)) $ 1" by simp
    thus False by simp
  next
    assume "real_euclid_B (vector [1, 0]) (vector [0, 1]) (0::real^2)"
    then obtain l where "vector [0, 1] - vector [1, 0] = l *\<^sub>R ((0::real^2) - vector [1, 0])"
      unfolding real_euclid_B_def by auto
    hence "(vector [0, 1] - vector [1, 0] :: real^2) $ 2 = (l *\<^sub>R ((0::real^2) - vector [1, 0])) $ 2" by simp
    thus False by simp
  next
    assume "real_euclid_B (vector [0, 1]) (0::real^2) (vector [1, 0])"
    then obtain l where "0 - vector [0, 1] = l *\<^sub>R (vector [1, 0] - vector [0, 1] :: real^2)"
      unfolding real_euclid_B_def by auto
    hence "((0::real^2) - vector [0, 1]) $ 1 = (l *\<^sub>R (vector [1, 0] - vector [0, 1] :: real^2)) $ 1 \<and>
           ((0::real^2) - vector [0, 1]) $ 2 = (l *\<^sub>R (vector [1, 0] - vector [0, 1] :: real^2)) $ 2" by simp
    thus False by auto
  qed
next
  show "\<forall>A B C D T. real_euclid_B A D T \<and> real_euclid_B B D C \<and> A \<noteq> D
          \<longrightarrow> (\<exists>X Y. real_euclid_B A B X \<and> real_euclid_B A C Y \<and> real_euclid_B X T Y)"
    by (rule real_euclid.A10)
next
  show "\<forall>a b c p q. (p:: (real, 2) Finite_Cartesian_Product.vec) \<noteq> q \<and> real_euclid_C a p a q \<and> real_euclid_C b p b q \<and> real_euclid_C c p c q
          \<longrightarrow> (real_euclid_B a b c \<or> real_euclid_B b c a \<or> real_euclid_B c a b)"
  using real_euclid.A9 by meson
next
  show "\<forall>Alpha Beta.
          (\<exists>A :: (real, 2) Finite_Cartesian_Product.vec. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B A X Y) \<longrightarrow>
          (\<exists>B. \<forall>X Y. Alpha X \<and> Beta Y \<longrightarrow> real_euclid_B X B Y)"
    using real2_continuity_pred by blast
qed

end
